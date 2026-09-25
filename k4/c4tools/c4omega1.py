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
counts the runs to which Lemma Ω applies with x = q, with another x, or with none.
Usage: python3 k4/c4tools/c4omega1.py FILE [FILE ...] [--any]"""
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
    a_x, b_x = I.ord[x][0], I.ord[x][1]
    # (H1) each of the leader's b and c is junk in P or is x's pick b_x, and {b, c} is envy-free for the leader
    # (automatic with three goods, a < b + c; with four goods it needs a + d <= b + c)
    b_l, c_l = I.ord[ell][1], I.ord[ell][2]
    if len(sets[ell]) == 4 and I.val(ell, [b_l, c_l]) < I.val(ell, [I.ord[ell][0], I.ord[ell][3]]):
        return 'H1 fails: the leader has four goods and {b, c} is not envy-free'
    if not all(Jpost >> g & 1 or g == b_x for g in (b_l, c_l)): return 'H1 fails: b_l or c_l is neither junk nor b_x'
    # (H2) x holds its second good, and no agent ranks b_x above its Phase 1 pick
    if Y[x] != b_x: return 'H2 fails: x does not hold b_x'
    if any(b_x in above(i) for i in range(n) if i != x): return 'H2 fails: some agent ranked b_x above its Phase 1 pick'
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
    st.base[ell] = frozenset([b_l, c_l]); st.kind[ell] = 'upg'; st.J = st.J - {c_l}
    if not st.valid(): return 'PROOF STEP 2 FAILS: the leader\'s upgrade gives an invalid state'
    w1 = st.omega(); w2 = T.upgrades(st, 2).omega()
    if w1 > w - 1 or w2 > w1: return 'PROOF STEP 2 FAILS: omega %d -> %d -> %d' % (w, w1, w2)
    return 'hypotheses hold; rho\' is a run of Phase 1 with the rotated picks; omega drops (chain length %d, %s%s)' % (
        s_, h5, ', %d detached' % len(det) if det else '')

CLS = {1: 'G2', 2: 'q frozen, no chain to r', 3: 'q frozen, (i)/(ii) of B4w fail', 4: '(Tc)', 5: '(Tb)'}
ANY = '--any' in sys.argv

def run(c):
    out = collections.Counter(); seen = set()
    for K in ((1, 2, 3, 4, 5) if ANY else (4,)):
        p = subprocess.run([BIN, '-X', '-Y', '-P2', '-u2', '-i20', '-o0', '-r1', '-w0', '-c0', '-f3', '-Z3', '-K%d' % K,
                            '-KL100000'], input=lb4_run.encode(c['sets'], c['m'], False), capture_output=True, text=True)
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
            else: out[(CLS[K], 'Lemma Omega applies to no agent')] += 1
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
