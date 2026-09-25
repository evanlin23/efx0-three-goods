"""k4/c4one.md §6, Lemma Ω₁: check its hypotheses and its conclusion on the runs of case (Tc) that the theorems leave
open, with x = q. For every core with exactly one 4-good agent q in the given certificate files, k4/c4check.c prints
those runs (-X -Y -P2 -u2 -i20 -Z3 -K4, every insertion sequence). For each distinct one this script
- checks the hypotheses (H1)-(H5) of Lemma Ω₁ for x = q and the leader ℓ of q's block;
- when they hold, builds the run ρ' of the proof step by step (prefix as in ρ; insert q; then ℓ; then the rest of the
  block in ρ's order; then the next block if its leader has b_ℓ; then the other blocks as in ρ) and checks that it is
  a run of Phase 1 (a P-step agent has lost a good, an inserted agent has not and nobody unprocessed has) with the
  picks the proof says;
- replays the proof's upgrades (ρ's upgrades, then ℓ with c_ℓ, then envy-free upgrades to a fixpoint, the tracer's
  order) and checks ω' <= ω - 1.
Counts distinct printed cases (not weighted by profiles).
Usage: python3 k4/c4tools/c4omega1.py FILE [FILE ...]"""
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

def check(line):
    sets, vals, order, blocks, picks, upg, Jpost, w = parse(line)
    I = T.Inst(sets, vals); n = I.n
    Y = [None if y < 0 else y for y in picks]
    pos = {a: k for k, a in enumerate(order)}
    q = next(i for i in range(n) if len(sets[i]) == 4)
    blk = lambda b: sorted((i for i in range(n) if blocks[i] == b), key=lambda i: pos[i])
    beta = blk(blocks[q]); ell = beta[0]; x = q
    a_x, b_x = I.ord[x][0], I.ord[x][1]
    # (H1) the leader has three goods, and its b and c are junk in P
    if len(sets[ell]) != 3: return 'H1 fails: the leader has four goods'
    b_l, c_l = I.ord[ell][1], I.ord[ell][2]
    if not (Jpost >> b_l & 1 and Jpost >> c_l & 1): return 'H1 fails: b_l or c_l is not junk (one of them is Y_r)'
    # (H2) x holds its second good, its first is the leader's pick, and no agent ranks b_x above its Phase 1 pick
    if Y[x] != b_x or Y[ell] != a_x: return 'H2 fails: x does not hold b_x with a_x the leader\'s pick'
    above = lambda i: set(I.ord[i][:I.rank[i][Y[i]]]) if Y[i] is not None else set(I.R[i])
    if any(b_x in above(i) for i in range(n) if i != x): return 'H2 fails: some agent ranked b_x above its Phase 1 pick'
    # (H3) in P no agent other than x needs a_x
    if any(a_x in above(i) for i in range(n) if i not in (x, ell) and i not in upg): return 'H3 fails: another agent needs a_x'
    # (H4) every other agent of the block lost, at its turn, a good other than b_x, or has b_l
    for p in beta:
        if p in (ell, x): continue
        taken = {Y[z] for z in range(n) if pos[z] < pos[p] and Y[z] is not None}
        if not ((I.R[p] & taken) - {b_x}) and b_l not in I.R[p]: return 'H4 fails'
    # (H5) no agent after the block has b_l, except possibly the leader of the next block
    nxt = blk(blocks[q] + 1)
    Z = [z for z in range(n) if blocks[z] > blocks[q] and b_l in I.R[z]]
    if Z and (not nxt or Z != [nxt[0]]): return 'H5 fails: a later agent other than the next leader has b_l'
    # the run rho' of the proof
    prefix = [a for a in order if blocks[a] < blocks[q]]
    new = prefix + [x, ell] + [p for p in beta if p not in (ell, x)]
    leaders = {blk(b)[0] for b in set(blocks) if b != blocks[q]} | {x}
    if Z: new += nxt; leaders.discard(nxt[0])
    new += [a for a in order if a not in new]
    Y2 = simulate(I, new, leaders)
    if isinstance(Y2, str): return 'PROOF STEP 1 FAILS: ' + Y2
    want = list(Y); want[x] = a_x; want[ell] = b_l
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
    return 'hypotheses hold; rho\' is a run of Phase 1 with the rotated picks; omega drops (%s)' % \
        ('the next block moves into q\'s' if Z else 'no later agent has b_l')

def run(c):
    out = collections.Counter(); seen = set()
    p = subprocess.run([BIN, '-X', '-Y', '-P2', '-u2', '-i20', '-o0', '-r1', '-w0', '-c0', '-f3', '-Z3', '-K4', '-KL100000'],
                       input=lb4_run.encode(c['sets'], c['m'], False), capture_output=True, text=True)
    for l in p.stderr.split('\n'):
        if l.startswith('KCASE'):
            key = l.split(' upg=')[0]
            if key not in seen: seen.add(key); out[check(l)] += 1
    return out

def main():
    c4check_run.build()
    print('# c4omega1.py', ' '.join(sys.argv[1:]), flush=True)
    for fn in sys.argv[1:]:
        cs = [c for c in json.load(gzip.open(fn, 'rt'))['cores'] if sum(len(s) == 4 for s in c['sets']) == 1]
        tot = collections.Counter()
        with Pool(4) as pool:
            for o in pool.imap_unordered(run, cs): tot.update(o)
        print(f'{fn}: {len(cs)} cores, {sum(tot.values())} (Tc) cases', flush=True)
        for k in sorted(tot): print(f'   {k:100s} {tot[k]}', flush=True)

if __name__ == '__main__':
    main()
