"""k4/c4one.md §6, Lemma Ω (Ω₁ for chains of length 1): check its hypotheses and its conclusion on the runs of case (Tc) that the theorems leave
open, with x = q. For every core with exactly one 4-good agent q in the given certificate files, k4/c4check.c prints
those runs (-X -Y -P2 -u2 -i20 -Z3 -K4, every insertion sequence). For each distinct one this script
- checks the hypotheses (H1)-(H5) of Lemma Ω for x = q and the leader ℓ of q's block (a need chain from ℓ to q of any
  length, (H2c) for its middle agents);
- when they hold, builds the run ρ' of the proof step by step (prefix as in ρ; insert q; then the chain backwards,
  ending with ℓ; then the rest of the block in ρ's order; then every later block whose leader has b_ℓ, (H5'); then the
  other blocks as in ρ) and checks that it is
  a run of Phase 1 (a P-step agent has lost a good, an inserted agent has not and nobody unprocessed has) with the
  picks the proof says;
- replays the proof's upgrades (ρ's upgrades, then ℓ with c_ℓ, then envy-free upgrades to a fixpoint, the tracer's
  order) and checks ω' <= ω - 1.
Counts distinct printed cases (not weighted by profiles).
With --any: every class of uncovered run (G2, q frozen, (Tc), (Tb)), and every agent x of the run tried in turn;
counts the runs to which Lemma Ω applies with x = q, with another x, only its variant Ω_q, only Lemma Ψ (the falling
chain, same kind of check), or nothing.
With --general: the runs of Phase 1 with P-steps in any order (k4/c4check.c -G), not only LB's key.
Usage: python3 k4/c4tools/c4omega1.py FILE [FILE ...] [--any] [--general]"""
import os, re, sys, gzip, json, subprocess, collections
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import c4trace as T
import lb4_run, c4check_run
BIN = os.environ.get('C4CHECK_BIN') or c4check_run.BIN

def parse(line):
    g = lambda k: re.search(k + r'=(\S+)', line).group(1)
    order = [int(x) for x in re.search(r'order=([\d ]+?)  ', line).group(1).split()]
    upg = {}
    for x in re.search(r'upg=(.*?) frozen=', line).group(1).split():
        i, h = x.split(':'); upg[int(i)] = int(h, 16)
    return (json.loads(g('sets')), json.loads(g('vals')), order, [int(x) for x in g('blocks').split(',')],
            [int(x) for x in g('picks').split(',')], upg, int(g(' J'), 16), int(g(' w')))

def simulate(I, order, lead):
    """a run of Phase 1 in the given processing order; lead = the agents processed in insertion steps.
    Returns the picks, or a string saying which rule the order breaks."""
    G = set(range(I.m)); Y = [None] * I.n; done = set()
    for a in order:
        lost = [i for i in range(I.n) if i not in done and not I.R[i] <= G]
        if a in lead:
            if lost: return 'insertion of %d while %s has lost a good' % (a, lost)
        elif a not in lost: return 'P-step of %d, which has lost nothing' % a
        Y[a] = next((g for g in I.ord[a] if g in G), None)
        if Y[a] is not None: G.discard(Y[a])
        done.add(a)
    return Y

def check(line, x=None):
    """Lemma Ω for the agent x (default q) and the leader of its block; returns a verdict string"""
    sets, vals, order, blocks, picks, upg, Jpost, w = parse(line)
    I = T.Inst(sets, vals); n = I.n
    Y = [None if y < 0 else y for y in picks]
    pos = {a: k for k, a in enumerate(order)}
    q = next(i for i in range(n) if len(sets[i]) == 4)
    if x is None: x = q
    blk = lambda b: sorted((i for i in range(n) if blocks[i] == b), key=lambda i: pos[i])
    beta = blk(blocks[x]); ell = beta[0]
    if ell == x: return 'x leads its block'
    if x in upg: return 'x is upgraded'
    above = lambda i: set(I.ord[i][:I.rank[i][Y[i]]]) if Y[i] is not None else set(I.R[i])
    a_x = I.ord[x][0]
    if Y[x] is None or Y[x] == a_x: return 'H2 fails: x has no pick or holds its top'
    b_x = Y[x]   # x's pick Y_x, any good below its top (the proof only uses that x gives it back)
    # (H1) each of the leader's b and c is junk in P or is x's pick Y_x, and {b, c} is envy-free for the leader
    # (automatic with three goods, a < b + c; with four goods it needs a + d <= b + c)
    b_l, c_l = I.ord[ell][1], I.ord[ell][2]
    free_ok = lambda g: bool(Jpost >> g & 1) or g == b_x
    ef = len(sets[ell]) == 3 or I.val(ell, [b_l, c_l]) >= I.val(ell, [I.ord[ell][0], I.ord[ell][3]])
    # Lemma Ω upgrades the leader with {b, c}; its variant Ω_q (the leader is q) does without that upgrade and lowers
    # the key's second component instead (q is no longer frozen)
    noupg = not (ef and free_ok(b_l) and free_ok(c_l))
    if noupg:
        if ell != q: return 'H1 fails: b_l or c_l is neither junk nor Y_x, or {b, c} is not envy-free'
        if not free_ok(b_l): return 'H1 fails (variant, the leader is q): b_q is neither junk nor Y_x'
    # (H2) x holds a good Y_x below its top, and no agent ranks Y_x above its Phase 1 pick
    if any(b_x in above(i) for i in range(n) if i != x): return 'H2 fails: some agent ranked Y_x above its Phase 1 pick'
    # (H2c) a need chain ell = x_0 -> ... -> x_s = x, each x_i (0 < i < s) ranking above Y_{x_{i-1}} only goods of
    # x_{i+1}, ..., x_{s-1}, and not a_x
    chains = []
    def rec(p):
        z = p[-1]
        if z == x: chains.append(list(p)); return
        for u in range(n):
            if u in p or u in upg or Y[z] is None or Y[z] not in above(u): continue
            rec(p + [u])
    rec([ell])
    chains = [c for c in chains if Y[c[-2]] == a_x]
    if not chains: return 'H2 fails: no need chain from the leader to x ending with a_x'
    def ok_chain(c):
        s_ = len(c) - 1
        for i in range(1, s_):
            want = set(I.ord[c[i]][:I.rank[c[i]][Y[c[i - 1]]]])
            if not want <= {Y[c[k]] for k in range(i + 1, s_)} or a_x in want: return False
        return True
    chains = [c for c in chains if ok_chain(c)]
    if not chains: return 'H2c fails: a chain agent ranks a good not held later in the chain above its new pick'
    chain = min(chains, key=len); s_ = len(chain) - 1
    # (H3) in P no agent other than x needs a_x
    if any(a_x in above(i) for i in range(n) if i not in (x,) and i not in upg and Y[i] != a_x):
        return 'H3 fails: another agent needs a_x'
    # (H4) the agents of the block off the chain split, in rho's order, into attached ones (having among their goods b_l,
    # a chain agent's rho-pick other than x's, or an earlier attached agent's pick) and detached ones (the rest). A
    # detached agent with no earlier detached agent's pick among its goods starts a block of its own in rho', so its
    # pick must be its top; and no attached agent ranks a detached agent's pick above its own
    att, det = [], []
    for p in beta:
        if p in chain: continue
        lost = {b_l} | {Y[z] for z in chain[:-1]} | {Y[z] for z in att}
        (att if I.R[p] & lost else det).append(p)
    if any(Y[p] != I.ord[p][0] for p in det): return 'H4 fails: a detached agent does not hold its top'
    if any(Y[d] in above(a) for a in att for d in det): return 'H4 fails: an attached agent ranks a detached pick above its own'
    # (H5') every agent after the block with b_l leads its block; those blocks move into q's block, which needs that no
    # block in between that stays has a good they pick
    Z = [z for z in range(n) if blocks[z] > blocks[x] and b_l in I.R[z]]
    if any(blk(blocks[z])[0] != z for z in Z): return "H5' fails: an agent after the block that is not a leader has b_l"
    moved = sorted({blocks[z] for z in Z})
    for g_ in moved:
        picks_g = {Y[i] for i in blk(g_) if Y[i] is not None}
        for d in range(blocks[x] + 1, g_):
            if d in moved: continue
            if any(I.R[i] & picks_g for i in blk(d)): return "H5' fails: a block in between has a good of a moved block"
    h5 = 'no later agent has b_l' if not Z else ('the next block moves into q\'s' if moved == [blocks[x] + 1] else
                                                   '%d later block(s) move into q\'s' % len(moved))
    # the run rho' of the proof: x, then the chain backwards, then the rest of the block in rho's order
    prefix = [a for a in order if blocks[a] < blocks[x]]
    new = prefix + list(reversed(chain)) + att
    leaders = {blk(b)[0] for b in set(blocks) if b != blocks[x] and b not in moved} | {x}
    for g_ in moved: new += blk(g_)
    # the detached agents: a P-step for the first (in rho's order) that has lost a good, else insert the first one
    taken = {Y[z] for z in new if z not in chain and z != ell and Y[z] is not None} | {Y[z] for z in chain[:-1]} | {b_l}
    rest = list(det)
    while rest:
        lost = [p for p in rest if I.R[p] & taken]
        p = lost[0] if lost else rest[0]
        if not lost: leaders.add(p)
        new.append(p); rest.remove(p); taken.add(Y[p])
    new += [a for a in order if a not in new]
    Y2 = simulate(I, new, leaders)
    if isinstance(Y2, str): return 'PROOF STEP 1 FAILS: ' + Y2
    want = list(Y); want[ell] = b_l
    for k in range(1, s_ + 1): want[chain[k]] = Y[chain[k - 1]]
    if Y2 != want: return 'PROOF STEP 1 FAILS: picks %s, expected %s' % (Y2, want)
    # step 2: rho's upgrades, then the leader with c_l, then envy-free upgrades to a fixpoint
    base = [frozenset([y]) if y is not None else frozenset() for y in Y2]; kind = ['pick'] * n
    J = frozenset(range(I.m)) - {y for y in Y2 if y is not None}
    st = T.State(I, base, kind, J, [pos[i] for i in range(n)], blocks, Y2)
    for k, h in sorted(upg.items()):
        B = frozenset(g for g in range(I.m) if h >> g & 1); g = next(iter(B - {Y2[k]}))
        st.base[k] = B; st.kind[k] = 'upg'; st.J = st.J - {g}
    if not st.valid(): return 'PROOF STEP 2 FAILS: replaying the upgrades gives an invalid state'
    if noupg:
        w1 = st.omega(); fin = T.upgrades(st, 2); w2 = fin.omega()
        if w1 > w or w2 > w1: return 'PROOF STEP 2 FAILS (variant): omega %d -> %d -> %d' % (w, w1, w2)
        if fin.frozen()[q]: return 'PROOF STEP 2 FAILS (variant): q is still frozen'
        return 'hypotheses of the variant hold; rho\' is a run of Phase 1 with the rotated picks; q unfrozen, omega %s' % (
            'drops' if w2 < w else 'equal')
    st.base[ell] = frozenset([b_l, c_l]); st.kind[ell] = 'upg'; st.J = st.J - {c_l}
    if not st.valid(): return 'PROOF STEP 2 FAILS: the leader\'s upgrade gives an invalid state'
    w1 = st.omega(); w2 = T.upgrades(st, 2).omega()
    if w1 > w - 1 or w2 > w1: return 'PROOF STEP 2 FAILS: omega %d -> %d -> %d' % (w, w1, w2)
    return 'hypotheses hold; rho\' is a run of Phase 1 with the rotated picks; omega drops (chain length %d, %s%s)' % (
        s_, h5, ', %d detached' % len(det) if det else '')

def check_psi(line, x):
    """Lemma Ψ (the falling chain) for the agent x; returns a verdict string"""
    sets, vals, order, blocks, picks, upg, Jpost, w = parse(line)
    I = T.Inst(sets, vals); n = I.n
    Y = [None if y < 0 else y for y in picks]
    pos = {a: k for k, a in enumerate(order)}
    q = next(i for i in range(n) if len(sets[i]) == 4)
    blk = lambda b: sorted((i for i in range(n) if blocks[i] == b), key=lambda i: pos[i])
    above = lambda i: set(I.ord[i][:I.rank[i][Y[i]]]) if Y[i] is not None else set(I.R[i])
    NA = set().union(*[above(i) for i in range(n) if i not in upg])
    # (Ψ1) x not upgraded, its pick Y_x below its top, and no agent ranks Y_x above its Phase 1 pick
    if x in upg or Y[x] is None or Y[x] == I.ord[x][0]: return 'Psi1 fails'
    y_x, a_x = Y[x], I.ord[x][0]
    if any(y_x in above(i) for i in range(n) if i != x): return 'Psi1 fails'
    holder = {Y[i]: i for i in range(n) if Y[i] is not None}
    if a_x not in holder: return 'Psi2 fails: nobody holds a_x'
    # (Ψ2) the fall chain y_0 = holder of a_x, ..., y_k, all in x's block, not upgraded, frozen in P; y_i falls to its
    # best good outside {Y_{y_0}, ..., Y_{y_i}}, which is Y_{y_{i+1}} (i < k) or a good g_k of J ∪ {Y_x}
    chain, cur = [], holder[a_x]
    while True:
        if cur in chain or cur == x or cur in upg or blocks[cur] != blocks[x]: return 'Psi2 fails: chain leaves the block'
        if Y[cur] not in NA: return 'Psi2 fails: a chain agent is free in P'
        chain.append(cur)
        gone = {Y[z] for z in chain}
        g = next((h for h in I.ord[cur] if h not in gone), None)
        if g is None: return 'Psi2 fails: a chain agent has nothing left'
        if g == y_x or Jpost >> g & 1: break
        if g not in holder: return 'Psi2 fails: the fall reaches a good that is neither a pick nor junk in P'
        cur = holder[g]
    yk, gk = chain[-1], g
    # (Ψ3) y_k has a good c, junk in P (or Y_x), with {g_k, c} envy-free for it
    rest_k = [h for h in I.ord[yk] if h != gk]
    cands = [c for c in rest_k if (Jpost >> c & 1 or c == y_x) and c != gk and
             I.val(yk, [gk, c]) >= I.val(yk, [h for h in I.R[yk] if h not in (gk, c)])]
    psi_q = not cands   # variant Ψ_q: no envy-free pair, but the last agent of the chain is q, which ends unfrozen
    if psi_q and yk != q: return 'Psi3 fails: the last agent of the chain has no envy-free pair'
    c_k = cands[0] if cands else None
    # (Ψ4) in P no agent other than x and the chain agents needs Y_{y_k}
    if any(Y[yk] in above(i) for i in range(n) if i not in chain and i != x and i not in upg): return 'Psi4 fails'
    # (Ψ5) as (H4) and (H5') of Lemma Ω, with the only newly taken good g_k (if it was junk)
    beta = blk(blocks[x]); new_good = {gk}   # taken by y_k in rho', also when g_k = Y_x
    att, det = [], []
    for p in beta:
        if p == x or p in chain: continue
        lost = new_good | {Y[z] for z in chain} | {Y[z] for z in att}
        (att if I.R[p] & lost else det).append(p)
    if any(Y[p] != I.ord[p][0] for p in det): return 'Psi5 fails: a detached agent does not hold its top'
    if any(Y[d] in above(a) for a in att for d in det): return 'Psi5 fails: an attached agent ranks a detached pick above its own'
    Z = [z for z in range(n) if blocks[z] > blocks[x] and gk in new_good and gk in I.R[z]]
    if any(blk(blocks[z])[0] != z for z in Z): return "Psi5 fails: an agent after the block that is not a leader has g_k"
    moved = sorted({blocks[z] for z in Z})
    for g_ in moved:
        picks_g = {Y[i] for i in blk(g_) if Y[i] is not None}
        for d in range(blocks[x] + 1, g_):
            if d not in moved and any(I.R[i] & picks_g for i in blk(d)): return "Psi5 fails: a block in between"
    # the run: x inserted, the chain, the attached agents, the moved blocks, the detached agents, the rest
    prefix = [a for a in order if blocks[a] < blocks[x]]
    new = prefix + [x] + chain + att
    leaders = {blk(b)[0] for b in set(blocks) if b != blocks[x] and b not in moved} | {x}
    for g_ in moved: new += blk(g_)
    taken = {Y[z] for z in new if z != x and z not in chain and Y[z] is not None} | {Y[z] for z in chain} | new_good
    rest = list(det)
    while rest:
        lost = [p for p in rest if I.R[p] & taken]
        p = lost[0] if lost else rest[0]
        if not lost: leaders.add(p)
        new.append(p); rest.remove(p); taken.add(Y[p])
    new += [a for a in order if a not in new]
    Y2 = simulate(I, new, leaders)
    if isinstance(Y2, str): return 'PSI PROOF STEP 1 FAILS: ' + Y2
    want = list(Y); want[x] = a_x
    for i_, z in enumerate(chain): want[z] = Y[chain[i_ + 1]] if i_ + 1 < len(chain) else gk
    if Y2 != want: return 'PSI PROOF STEP 1 FAILS: picks %s, expected %s' % (Y2, want)
    # upgrades: rho's, then y_k with {g_k, c}, then envy-free upgrades to a fixpoint
    st = T.State(I, [frozenset([y]) if y is not None else frozenset() for y in Y2], ['pick'] * n,
                 frozenset(range(I.m)) - {y for y in Y2 if y is not None}, [pos[i] for i in range(n)], blocks, Y2)
    for k, h in sorted(upg.items()):
        B = frozenset(g for g in range(I.m) if h >> g & 1); g = next(iter(B - {Y2[k]}))
        st.base[k] = B; st.kind[k] = 'upg'; st.J = st.J - {g}
    if not st.valid(): return 'PSI PROOF STEP 2 FAILS: replaying the upgrades gives an invalid state'
    if psi_q:
        w1 = st.omega(); fin = T.upgrades(st, 2); w2 = fin.omega()
        if w1 > w or w2 > w1: return 'PSI PROOF STEP 2 FAILS (variant): omega %d -> %d -> %d' % (w, w1, w2)
        if fin.frozen()[q]: return 'PSI PROOF STEP 2 FAILS (variant): q is still frozen'
        return 'Psi hypotheses hold (variant, q falls last); q unfrozen'
    st.base[yk] = frozenset([gk, c_k]); st.kind[yk] = 'upg'; st.J = st.J - {c_k}
    if not st.valid(): return 'PSI PROOF STEP 2 FAILS: the upgrade of y_k gives an invalid state'
    w1 = st.omega(); w2 = T.upgrades(st, 2).omega()
    if w1 > w - 1 or w2 > w1: return 'PSI PROOF STEP 2 FAILS: omega %d -> %d -> %d' % (w, w1, w2)
    return 'Psi hypotheses hold; omega drops (fall chain of %d)' % len(chain)

CLS = {1: 'G2', 2: 'q frozen, no chain to r', 3: 'q frozen, (i)/(ii) of B4w fail', 4: '(Tc)', 5: '(Tb)'}
ANY = '--any' in sys.argv
GENERAL = ['-G'] if '--general' in sys.argv else []   # runs with P-steps in any order (k4/c4check.c -G)

def run(c):
    out = collections.Counter(); seen = set()
    for K in ((1, 2, 3, 4, 5) if ANY else (4,)):
        p = subprocess.run([BIN, '-X', '-Y', '-P2', '-u2', '-i20', '-o0', '-r1', '-w0', '-c0', '-f3', '-Z3', '-K%d' % K,
                            '-KL100000'] + GENERAL, input=lb4_run.encode(c['sets'], c['m'], False), capture_output=True, text=True)
        for l in p.stderr.split('\n'):
            if not l.startswith('KCASE'): continue
            key = (K, l.split(' upg=')[0])
            if key in seen: continue
            seen.add(key)
            if not ANY: out[check(l)] += 1; continue
            n = len(json.loads(re.search(r'sets=(\S+)', l).group(1)))
            q = next(i for i, S in enumerate(json.loads(re.search(r'sets=(\S+)', l).group(1))) if len(S) == 4)
            vs = {x: check(l, x) for x in range(n)}
            bad = [v for v in vs.values() if v.startswith('PROOF')]
            if bad: out[(CLS[K], 'PROOF FAILS: ' + bad[0])] += 1
            elif vs[q].startswith('hypotheses hold'): out[(CLS[K], 'Lemma Omega applies with x = q')] += 1
            elif any(v.startswith('hypotheses hold') for v in vs.values()): out[(CLS[K], 'Lemma Omega applies with another x')] += 1
            elif any(v.startswith('hypotheses of the variant') for v in vs.values()): out[(CLS[K], 'only the variant (leader q) applies')] += 1
            else:
                ps = {x: check_psi(l, x) for x in range(n)}
                badp = [v for v in ps.values() if v.startswith('PSI PROOF')]
                if badp: out[(CLS[K], badp[0])] += 1
                elif any(v.startswith('Psi hypotheses hold') for v in ps.values()): out[(CLS[K], 'only Lemma Psi applies')] += 1
                else: out[(CLS[K], 'neither Omega nor Psi applies')] += 1
    return out

def main():
    c4check_run.build()
    print('# c4omega1.py', ' '.join(sys.argv[1:]), flush=True)
    for fn in [a for a in sys.argv[1:] if not a.startswith('--')]:
        cs = [c for c in json.load(gzip.open(fn, 'rt'))['cores'] if sum(len(s) == 4 for s in c['sets']) == 1]
        tot = collections.Counter()
        with Pool(4) as pool:
            for o in pool.imap_unordered(run, cs): tot.update(o)
        print(f'{fn}: {len(cs)} cores, {sum(tot.values())} ' + ('uncovered cases' if ANY else '(Tc) cases'), flush=True)
        for k in sorted(tot, key=str): print(f'   {str(k):100s} {tot[k]}', flush=True)

if __name__ == '__main__':
    main()
