"""The re-rooting move (k4/one4.md §5): for an uncovered run in class "q frozen, no need chain to r" (q leads its block),
insert first, in place of q, the agent z holding q's second good b_q, then follow Phase 1 (P-steps before insertions,
smallest index; index order at insertions).  Check, in the new run's state P' (after envy-free upgrades to a fixpoint,
c4trace), the hypotheses of Theorem B4w (k4/c4.md §4a) for w = q: q frozen and exposed w.r.t. the new r, a need chain
q -> ... -> r, (i), (ii), r not a 4-good agent; and, independently, that the rotated pre-allocation (chain shifted,
q holding O = R_q ∩ W) has an EFX0 completion (brute force, raw EFX0).
    python3 k4/one4_reroot.py FILE"""
import os, sys, re, json, gzip, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, 'c4tools')); sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'k3'))
import c4omega1 as O, c4trace as T, k3algo as K
import one4_residual as R, one4_omega_plus as P, one4_psi_u as PU


def phase1(I, first):
    G = set(range(I.m)); Y = [None] * I.n; done = []; lead = set()
    while len(done) < I.n:
        lost = [i for i in range(I.n) if i not in done and not I.R[i] <= G]
        if not done: a = first
        elif lost: a = lost[0]
        else: a = min(i for i in range(I.n) if i not in done)
        if not lost: lead.add(a)
        Y[a] = next((g for g in I.ord[a] if g in G), None)
        if Y[a] is not None: G.discard(Y[a])
        done.append(a)
    return Y, done, lead


def b4w(I, Y, order, lead, q):
    n = I.n
    blocks, b = [], -1
    for a in order:
        if a in lead: b += 1
        blocks.append(b)
    blk = {a: bb for a, bb in zip(order, blocks)}
    st = T.State(I, [frozenset([y]) if y is not None else frozenset() for y in Y], ['pick'] * n,
                 frozenset(range(I.m)) - {y for y in Y if y is not None}, [order.index(i) for i in range(n)],
                 [blk[i] for i in range(n)], Y)
    st = T.upgrades(st, 2)
    U = {i for i in range(n) if st.kind[i] == 'upg'}
    above = lambda i: set(I.ord[i][:I.rank[i][Y[i]]]) if Y[i] is not None else set(I.R[i])
    NA = set().union(*[above(i) for i in range(n) if i not in U]) if n else set()
    frozen = {i for i in range(n) if i not in U and Y[i] is not None and Y[i] in NA}
    nonU = [a for a in order if a not in U]
    r = nonU[-1]
    W = set(st.J) | ({Y[r]} if Y[r] is not None else set())
    def exposed(x):
        if x in U or x == r: return False
        own = I.val(x, list(st.base[x])); L = [g for g in W]
        return max(I.val(x, [h for h in L if h != g]) for g in L) > own if L else False
    if q not in frozen: return 'q not frozen'
    if not exposed(q): return 'q not exposed'
    if q == r: return 'q is r'
    chains = []
    def rec(p):
        z = p[-1]
        if z == r: chains.append(list(p)); return
        for u in range(n):
            if u in p or u in U or Y[z] is None or Y[z] not in above(u): continue
            if u != r and u not in frozen: continue
            rec(p + [u])
    rec([q])
    if not chains: return 'no need chain q -> r'
    Oq = [g for g in I.R[q] if g in W]
    E = [x for x in range(n) if x != q and exposed(x)]
    if any({I.ord[x][1], I.ord[x][2]} <= set(Oq) for x in E if len(I.R[x]) == 3): return '(i) fails'
    kstar = next(a for a in order if blk[a] == blk[r])
    T_ = {i for i in range(n) if i not in U and i not in frozen}
    ii = (kstar not in E) or kstar == q or kstar in T_
    if not ii: return '(ii) fails (simple forms)'
    if len(I.R[r]) == 4: return 'r is 4-good'
    return 'B4w applies', chains[0], Oq


def completion_ok(I, v, Y, chain, Oq, q):
    n, m = I.n, I.m
    Y3 = list(Y)
    for i in range(1, len(chain)): Y3[chain[i]] = Y[chain[i - 1]]
    Y3[q] = None
    held = {Y3[i] for i in range(n) if i != q and Y3[i] is not None} | set(Oq)
    J = [g for g in range(m) if g not in held]; others = [i for i in range(n) if i != q]
    for lab in itertools.product(range(len(others) + 1), repeat=len(J)):
        if any(c > 1 for c in collections.Counter(l for l in lab if l < len(others)).values()): continue
        X = [None] * m
        for i in others:
            if Y3[i] is not None: X[Y3[i]] = i
        for g in Oq: X[g] = q
        for g, l in zip(J, lab): X[g] = others[l] if l < len(others) else q
        if K.raw_efx0(n, m, v, X): return True
    return False


def job(c):
    out = []
    for cls, l in R.residual(c):
        if not cls.startswith('q frozen'): continue
        if P.verdict(l, False).startswith('omega drops'): continue
        nn = len(json.loads(re.search(r'sets=(\S+)', l).group(1)))
        if any(PU.check(l, x).startswith('Psi-u holds') for x in range(nn)): continue
        sets, vals, order, blocks, picks, upg, Jpost, w = O.parse(l)
        I = T.Inst(sets, vals); n = I.n; v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
        q = next(i for i in range(n) if len(sets[i]) == 4)
        Y = [None if y < 0 else y for y in picks]
        z = next((i for i in range(n) if Y[i] == I.ord[q][1]), None)
        if z is None: out.append((cls, 'b_q unheld')); continue
        Y2, ordr, lead = phase1(I, z)
        res = b4w(I, Y2, ordr, lead, q)
        if isinstance(res, str): out.append((cls, 're-rooted run: ' + res)); continue
        _, chain, Oq = res
        out.append((cls, 'B4w applies; completion EFX0: %s' % completion_ok(I, v, Y2, chain, Oq, q)))
    return out


if __name__ == '__main__':
    import c4check_run
    c4check_run.build()
    print('$ python3 k4/one4_reroot.py', *sys.argv[1:], flush=True)
    cs = [c for c in json.load(gzip.open(sys.argv[1], 'rt'))['cores'] if sum(len(s) == 4 for s in c['sets']) == 1]
    Tl = collections.Counter()
    from multiprocessing import Pool
    with Pool(4) as pool:
        for o in pool.imap_unordered(job, cs): Tl.update(o)
    for k in sorted(Tl): print(' ', k, Tl[k])
