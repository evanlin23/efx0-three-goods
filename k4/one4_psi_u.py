"""Lemma Ψᵘ (k4/one4.md §4): Lemma Ψ (k4/c4one.md §6, the falling chain from x's top) when (Ψ1) fails through one
UPGRADED agent u.  Hypotheses checked here, at the state P of a run ρ (LB's key):
  (Ψᵘ1) exactly one agent u ≠ x ranks Y_x above its Phase 1 pick; u is upgraded (base {Y_u, g_u}); Y_x = a_u; no agent
        other than u ranks Y_u above its Phase 1 pick;
  (Ψ2)  the fall chain y_0 (holder of a_x), ..., y_k is in x's block, never upgraded, frozen in P, never returns, never
        reaches x; and it ends at a good g_k that is junk in P (not Y_x, which u takes);
  (Ψ3)  y_k has a good c, junk in P, c ≠ g_k, with {g_k, c} envy-free for y_k;
  (Ψ4)  in P no agent other than x and the y_i needs Y_{y_k}.
The run ρ' (hypothesis (R) of the lemma: this order is a run of Phase 1): ρ's prefix before x's block, x inserted, the fall chain y_0..y_k as P-steps, then every other agent in ρ's
order, each as a P-step if it has lost a good and otherwise inserted when no unprocessed agent has lost a good (the step
is legal only then); checked to be a run of Phase 1 with picks: x -> a_x, y_i -> g_i, u -> Y_x, everyone else unchanged.
Then ρ's upgrades except u's, y_k's upgrade with {g_k, c}, envy-free upgrades to a fixpoint (c4trace), and the check
omega' <= omega - 1.  Run on the residual runs of k4/one4_residual.py that Ω⁺/Ψ⁺ leave.
    python3 k4/one4_psi_u.py FILE"""
import os, sys, re, json, gzip, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, 'c4tools')); sys.path.insert(0, HERE)
import c4omega1 as O, c4trace as T
import one4_residual as R, one4_omega_plus as P


def run_auto(I, order):
    """order of processing; each agent is a P-step if it has lost a good, else an insertion, legal only when no
    unprocessed agent has lost a good.  Returns picks or an error string."""
    G = set(range(I.m)); Y = [None] * I.n; done = set()
    for a in order:
        lost = [i for i in range(I.n) if i not in done and not I.R[i] <= G]
        if a not in lost and lost: return 'insertion of %d while %s has lost a good' % (a, lost)
        Y[a] = next((g for g in I.ord[a] if g in G), None)
        if Y[a] is not None: G.discard(Y[a])
        done.add(a)
    return Y


def check(line, x):
    sets, vals, order, blocks, picks, upg, Jpost, w = O.parse(line)
    I = T.Inst(sets, vals); n = I.n; Y = [None if y < 0 else y for y in picks]
    above = lambda i: set(I.ord[i][:I.rank[i][Y[i]]]) if Y[i] is not None else set(I.R[i])
    if x in upg or Y[x] is None or Y[x] == I.ord[x][0]: return 'x not eligible'
    yx, ax = Y[x], I.ord[x][0]
    grab = [i for i in range(n) if i != x and yx in above(i)]
    if len(grab) != 1 or grab[0] not in upg or I.ord[grab[0]][0] != yx: return 'Psiu1 fails (grabbers)'
    u = grab[0]
    if any(Y[u] in above(i) for i in range(n) if i != u): return 'Psiu1 fails (Y_u wanted)'
    holder = {Y[i]: i for i in range(n) if Y[i] is not None}
    if ax not in holder: return 'Psi2 fails: nobody holds a_x'
    chain, cur = [], holder[ax]
    NA = set().union(*[above(i) for i in range(n) if i not in upg])
    while True:
        if cur in chain or cur == x or cur == u or cur in upg or blocks[cur] != blocks[x]: return 'Psi2 fails'
        if Y[cur] not in NA: return 'Psi2 fails: chain agent free'
        chain.append(cur)
        gone = {Y[z] for z in chain}
        g = next((h for h in I.ord[cur] if h not in gone), None)
        if g is None: return 'Psi2 fails: nothing left'
        if Jpost >> g & 1: break
        if g == yx: return 'Psiu2 fails: the fall reaches Y_x'
        if g not in holder: return 'Psi2 fails: neither pick nor junk'
        cur = holder[g]
    yk, gk = chain[-1], g
    cands = [c for c in I.ord[yk] if c != gk and Jpost >> c & 1 and
             I.val(yk, [gk, c]) >= I.val(yk, [h for h in I.R[yk] if h not in (gk, c)])]
    if not cands: return 'Psi3 fails'
    ck = cands[0]
    if any(Y[yk] in above(i) for i in range(n) if i not in chain and i != x and i not in upg): return 'Psi4 fails'
    pos = {a: k for k, a in enumerate(order)}
    prefix = [a for a in order if blocks[a] < blocks[x]]
    new = prefix + [x] + chain + [a for a in order if a not in prefix and a != x and a not in chain]
    Y2 = run_auto(I, new)
    if isinstance(Y2, str): return 'REALIZATION FAILS: ' + Y2
    want = list(Y); want[x] = ax; want[u] = yx
    for i_, z in enumerate(chain): want[z] = Y[chain[i_ + 1]] if i_ + 1 < len(chain) else gk
    if Y2 != want: return 'REALIZATION FAILS: picks %s, expected %s' % (Y2, want)
    st = T.State(I, [frozenset([y]) if y is not None else frozenset() for y in Y2], ['pick'] * n,
                 frozenset(range(I.m)) - {y for y in Y2 if y is not None}, [pos[i] for i in range(n)], blocks, Y2)
    for k, h in sorted(upg.items()):
        if k == u: continue
        B = frozenset(g_ for g_ in range(I.m) if h >> g_ & 1); g_ = next(iter(B - {Y[k]}))
        st.base[k] = frozenset([Y2[k], g_]); st.kind[k] = 'upg'; st.J = st.J - {g_}
    if not st.valid(): return 'COUNT FAILS: replayed upgrades invalid'
    st.base[yk] = frozenset([gk, ck]); st.kind[yk] = 'upg'; st.J = st.J - {ck}
    if not st.valid(): return 'COUNT FAILS: y_k upgrade invalid'
    w1 = st.omega(); w2 = T.upgrades(st, 2).omega()
    if w1 > w - 1 or w2 > w1: return 'COUNT FAILS: omega %d -> %d -> %d' % (w, w1, w2)
    return 'Psi-u holds; omega drops %d -> %d' % (w, w2)


if __name__ == '__main__':
    import c4check_run
    c4check_run.build()
    print('$ python3 k4/one4_psi_u.py', *sys.argv[1:], flush=True)
    cs = [c for c in json.load(gzip.open(sys.argv[1], 'rt'))['cores'] if sum(len(s) == 4 for s in c['sets']) == 1]
    Tl = collections.Counter(); shown = 0
    from multiprocessing import Pool
    with Pool(4) as pool:
        for res in pool.imap_unordered(R.residual, cs):
            for cls, l in res:
                if P.verdict(l, False).startswith('omega drops'): continue
                n = len(json.loads(re.search(r'sets=(\S+)', l).group(1)))
                vs = [check(l, x) for x in range(n)]
                ok = next((v for v in vs if v.startswith('Psi-u holds')), None)
                bad = next((v for v in vs if 'FAILS' in v and v.split(':')[0] in ('REALIZATION FAILS', 'COUNT FAILS')), None)
                Tl[(cls, 'Psi-u applies' if ok else ('Psi-u: ' + (bad.split(':')[0] if bad else 'hypotheses fail')))] += 1
                if bad and not ok and shown < 3: print('  ', bad, l[:200]); shown += 1
    for k in sorted(Tl): print(' ', k, Tl[k])
