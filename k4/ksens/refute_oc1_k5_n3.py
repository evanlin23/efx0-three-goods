"""One chain fails at k = 5 already with three agents (k4/ksens.md §8): the instance N3K5, found by kcegar.py (every
strict profile of every connected n = 3 hypergraph with at most five goods per agent; results/k4_ksens/
kcegar_k5_n3_D1.log, hypergraph n3_m6_92).

    agent 0: goods 0, 2, 3, 4, 5 worth 3, 22, 23, 38, 43
    agent 1: goods 1, 2, 3, 4, 5 worth 15, 17, 27, 40, 43
    agent 2: goods 1, 4, 5     worth 1, 2, 4
The start is a maximum-matching start (every agent picks; picks 4, 5, 1).

Lifted to full valuations (every value x100, the zeros replaced by 1, 2, 3, ... in reading order; k = m = 6, all values
positive, so EFX0 = EFX) the same start still has no completion after one round, free or one-absorber, and two rounds
repair it (N3K5+ below).

Checks: ocsat (SAT) and brute.py (every chain and round from the definition, every completion over all n^m
allocations): no completion, free or one-absorber, at the picks, after any one chain (with or without empty passes),
or after any one round; two chains repair (ocseq, and brute force).  Also MD and SD-C over every order.

    python3 k4/ksens/refute_oc1_k5_n3.py"""
import json, itertools, time
import _paths
import ocsat, ocseq, brute
from maxmatch import nu

SETS = [[0, 2, 3, 4, 5], [1, 2, 3, 4, 5], [1, 4, 5]]
VALS = [[3, 22, 23, 38, 43], [15, 17, 27, 40, 43], [1, 2, 4]]
PICKS = (4, 5, 1)

if __name__ == '__main__':
    print('$ python3 k4/ksens/refute_oc1_k5_n3.py'); t0 = time.time(); n, m = 3, 6
    I = brute.Inst(SETS, VALS, m); O = ocsat.OC(SETS, VALS, m); Q = ocseq.Seq(SETS, VALS, m)
    orders = [o for o in itertools.permutations(range(n)) if tuple(I.sd(o)) == PICKS]
    b = ocsat.bases_of(PICKS, n); base = [frozenset([g]) for g in PICKS]
    sat = [O.holds(b, chain='none', A=1), O.holds(b, chain='none'), O.holds(b, chain='any', A=1), O.holds(b, chain='any'),
           O.holds(b, chain='any', A=1, multi=True), O.holds(b, chain='any', multi=True)]
    ch = I.chains(base); ch0 = I.chains(base, empty_pass=False); rd = I.rounds(base)
    bf = [I.completes(base, 1), I.completes(base), any(I.completes(s, 1) for s in ch), any(I.completes(s) for s in ch),
          any(I.completes(s, 1) for s in rd), any(I.completes(s) for s in rd)]
    two = sum(1 for s in ch0 for s2 in I.chains([frozenset(x) for x in s], empty_pass=False) if I.completes(s2, 1))
    seq = next((c for c in range(4) if Q.holds(b, c, 1)), None)
    a = ocsat.report(SETS, VALS, m); bb, _ = brute.report(SETS, VALS, m)
    mism = sum(1 for y in a for k in ('md', 'ext', 'ext1', 'oc', 'oc1') if a[y][k] != bb[y][k])
    print('N3K5 =', json.dumps((SETS, VALS)), '; orders giving the picks', orders, '; nu', nu(SETS, VALS),
          '; complete EFX0 allocations', len(I.efx0_list()))
    print('[picks A1, picks free, one chain A1, one chain free, one round A1, one round free]: SAT %s, brute %s' % (sat, bf))
    print('one-chain states %d (official rule %d), round states %d; two-chain states (official rule) with a one-absorber '
          'completion: %d; least chains (ocseq, one absorber): %s' % (len(ch), len(ch0), len(rd), two, seq))
    print('every order: %d starts; OC1 fails on %d; MD fails on %d; SD-C %s; ocsat/brute mismatches %d' % (
        len(a), sum(1 for r in a.values() if not r['oc1']), sum(1 for r in a.values() if not r['md']),
        any(r['ext'] for r in a.values()), mism))
    ok = orders and not any(sat) and not any(bf) and two > 0 and seq == 2 and mism == 0
    # N3K5+: the full-valuation lift
    rows = [[0] * m for _ in range(n)]; c = 0
    for i, (s_, v_) in enumerate(zip(SETS, VALS)):
        for g, x in zip(s_, v_): rows[i][g] = 100 * x
    for i in range(n):
        for g in range(m):
            if rows[i][g] == 0: c += 1; rows[i][g] = c
    F = [list(range(m))] * n; OF = ocsat.OC(F, rows, m); QF = ocseq.Seq(F, rows, m); IF = brute.Inst(F, rows, m)
    rdf = IF.rounds(base)
    lift = [OF.holds(b, chain='any', A=1, multi=True), OF.holds(b, chain='any', multi=True),
            any(IF.completes(s, 1) for s in rdf), any(IF.completes(s) for s in rdf)]
    lift2 = [QF.holds(b, 2, 1, multi=True), QF.holds(b, 2, None, multi=True)]
    print('N3K5+ (full valuations) =', json.dumps(rows), '; start', tuple(IF.sd(orders[0])),
          '; one round [SAT A1, SAT free, brute A1, brute free] %s over %d round states; two rounds [A1, free] (ocseq) %s'
          % (lift, len(rdf), lift2))
    ok = ok and tuple(IF.sd(orders[0])) == PICKS and not any(lift) and all(lift2)
    print('OK: one chain and one round fail at k = 5 with n = 3 (m = 6), and one round also with every good valued; two '
          'chains (two rounds) repair:' if ok else 'NOT CONFIRMED', '%.0f s' % (time.time() - t0))
