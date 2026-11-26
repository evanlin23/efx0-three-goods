"""Conjecture RD (one round of vertex-disjoint improving chains, then a completion; k4/ksens.md §6) is false at k = 5:
the instance RD5 (n = 4, m = 7, strict values, one agent with five relevant goods, the others with at most four),
found by climb.py round1 from the kgen-n4 seed (results/k4_ksens/climb_round1_n4k6_kgen.log, k = 6) and shrunk by
dropping goods (results/k4_ksens/rd_shrink.log).

    agent 0: goods 1, 3, 5, 0, 4 worth 57, 44, 33, 26, 24
    agent 1: goods 1, 2, 3 worth 12, 11, 6
    agent 2: goods 1, 2, 3, 4 worth 9, 8, 6, 1
    agent 3: goods 2, 5, 0, 6 worth 53, 47, 36, 4
    order (0, 3, 1, 2): picks 1, 3, 4, 2 (agent 0 takes 1, agent 3 takes 2, agent 1 takes 3, agent 2 takes 4); junk {0, 5, 6}

Two independent checks that no state one round reaches (the empty round included) has a complete EFX0 completion, free
or with one absorber:
  1. ocsat.py, the round encoded in SAT (OC.holds(..., multi=True)), on sdclib's EFX0 clauses;
  2. brute.py: every round enumerated from the definition (brute.Inst.rounds), every complete allocation checked
     against the raw EFX0 definition (numpy).
Also reported: the least number of sequential chains (ocseq.py, and brute force for two chains), MD, SD-C, OC1 over
every order, and the same instance with agent 0's fifth good removed (k = 4), where everything holds.

    python3 k4/ksens/refute_rd_k5.py"""
import json, time
import _paths
import ocsat, ocseq, brute

SETS = [[0, 3, 4, 5, 1], [1, 2, 3], [1, 3, 4, 2], [0, 2, 6, 5]]
VALS = [[26, 44, 24, 33, 57], [12, 11, 6], [9, 6, 1, 8], [36, 53, 4, 47]]
ORDER = (0, 3, 1, 2)

if __name__ == '__main__':
    print('$ python3 k4/ksens/refute_rd_k5.py')
    m, n = 7, 4; t0 = time.time()
    print('RD5 =', json.dumps((SETS, VALS)), 'k', max(map(len, SETS)))
    I = brute.Inst(SETS, VALS, m); O = ocsat.OC(SETS, VALS, m); Q = ocseq.Seq(SETS, VALS, m)
    Y = tuple(I.sd(ORDER)); b = ocsat.bases_of(Y, n); base = [frozenset([g]) for g in Y]
    print('order', ORDER, 'picks', Y, 'junk', [g for g in range(m) if g not in Y], '; complete EFX0 allocations:', len(I.efx0_list()))
    rd = I.rounds(base); ch = I.chains(base)
    sat = {'round free': O.holds(b, chain='any', multi=True), 'round A=1': O.holds(b, chain='any', A=1, multi=True),
           'one chain free': O.holds(b, chain='any'), 'one chain A=1': O.holds(b, chain='any', A=1)}
    bf = {'round states': len(rd), 'with a free completion': sum(1 for s in rd if I.completes(s)),
          'with a one-absorber completion': sum(1 for s in rd if I.completes(s, 1)), 'one-chain states': len(ch)}
    print('SAT (ocsat):', sat)
    print('brute force:', bf)
    two = sum(1 for s in ch for s2 in I.chains([frozenset(x) for x in s]) if I.completes(s2))
    print('least sequential chains: ocseq free %s, one absorber %s; brute force: two-chain states with a free completion %d' % (
        next(c for c in range(4) if Q.holds(b, c)), next(c for c in range(4) if Q.holds(b, c, 1)), two))
    print('MD for this order (brute):', I.dominated(Y))
    a = ocsat.report(SETS, VALS, m); bb, _ = brute.report(SETS, VALS, m)
    mism = sum(1 for y in a for k in ('md', 'ext', 'ext1', 'oc', 'oc1') if a[y][k] != bb[y][k])
    print('every order: %d starts; OC1 fails on %d, MD on %d; SD-C %s; ocsat/brute mismatches %d' % (
        len(a), sum(1 for r in a.values() if not r['oc1']), sum(1 for r in a.values() if not r['md']),
        any(r['ext'] for r in a.values()), mism))
    assert not any(sat.values()) and bf['with a free completion'] == 0 and bf['with a one-absorber completion'] == 0 and two > 0
    # the k = 4 version: drop agent 0's least valuable good (good 4)
    S4 = [[0, 3, 5, 1], [1, 2, 3], [1, 3, 4, 2], [0, 2, 6, 5]]; V4 = [[26, 44, 33, 57], [12, 11, 6], [9, 6, 1, 8], [36, 53, 4, 47]]
    O4 = ocsat.OC(S4, V4, m)
    bad4 = [y for y in ocsat.starts(S4, V4, m) if not O4.holds(ocsat.bases_of(y, n), chain='any', multi=True)]
    bad41 = [y for y in ocsat.starts(S4, V4, m) if not O4.holds(ocsat.bases_of(y, n), chain='any', A=1)]
    print('k = 4 version (agent 0 without good 4):', json.dumps((S4, V4)), '; starts failing one round: %d; failing OC1: %d' % (len(bad4), len(bad41)))
    print('OK: RD and RD1 fail at k = 5 (n = 4, m = 7) from order', ORDER, '; two chains suffice; %.0f s' % (time.time() - t0))
