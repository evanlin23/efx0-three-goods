"""OC1^max (and OC1, OC, one round) fail at k = 4 (k4/ksens.md §8): the 11 strict n = 4 core profiles of the
certifier session (compute/k4-oc1max-cert, results/k4_oc1max/oc1max_cex_n4.json and brute_verify_cex_n4.log there,
found by its ordinal CEGAR k4/oc1cert/cegar.py; k4/sdc.md §31 on that branch), replayed with this workstream's two
independent checkers:
  1. ocsat.py (SAT on sdclib's EFX0 clauses; one chain, one round with multi=True);
  2. brute.py (every chain / round enumerated from the definition, every completion checked against the raw EFX0
     definition by numpy enumeration of all n^m allocations).
For each instance and its maximum-matching start: no completion (one absorber, or free) at the picks, after any one
chain (ocsat lets an agent pass an empty base, brute force both with and without), or after one round; the least number
of sequential chains (ocseq.py), and the same two-chain repair checked by brute force; MD and SD-C over every order.

    python3 k4/ksens/refute_oc1max_k4.py"""
import json, time, itertools
import _paths
import ocsat, ocseq, brute
from maxmatch import nu

CEX = [  # (sets, vals, picks) as listed in the certifier's brute_verify_cex_n4.log
    ([[0, 1, 2, 5], [1, 2, 5, 6], [3, 4, 5, 6], [3, 4, 6]], [[2, 10, 4, 7], [10, 3, 4, 8], [3, 5, 6, 7], [3, 2, 4]], [1, 2, 5, 6]),
    ([[0, 4, 5, 6], [1, 2, 3, 5], [1, 3, 5, 6], [2, 4, 6]], [[2, 3, 10, 6], [3, 10, 6, 8], [5, 3, 7, 6], [4, 3, 2]], [4, 5, 6, 2]),
    ([[0, 1, 2, 6], [1, 2, 5, 6], [3, 4, 5, 6], [3, 4, 5, 6]], [[2, 5, 4, 8], [5, 3, 6, 7], [10, 3, 8, 6], [10, 2, 3, 6]], [6, 5, 3, 4]),
    ([[0, 1, 2, 6], [1, 2, 4, 5], [3, 4, 5, 6], [3, 4, 5, 6]], [[2, 7, 4, 10], [3, 5, 6, 7], [3, 5, 6, 7], [1, 4, 6, 8]], [6, 4, 5, 3]),
    ([[0, 1, 4, 5], [1, 3, 5, 6], [2, 3, 4, 6], [2, 4, 5, 6]], [[2, 3, 10, 6], [7, 10, 6, 2], [3, 10, 8, 6], [5, 8, 6, 4]], [1, 3, 4, 5]),
    ([[0, 1, 4, 5], [1, 4, 5, 6], [2, 3, 4, 6], [2, 3, 5, 6]], [[1, 8, 6, 4], [8, 4, 2, 7], [3, 5, 6, 7], [4, 5, 2, 8]], [1, 5, 4, 6]),
    ([[0, 2, 3, 6], [1, 2, 4, 5], [1, 4, 5, 6], [3, 4, 5, 6]], [[2, 10, 6, 7], [4, 8, 5, 2], [5, 7, 3, 6], [3, 10, 2, 6]], [2, 4, 6, 3]),
    ([[0, 4, 5, 6], [1, 2, 3, 6], [1, 3, 5, 6], [2, 4, 5, 6]], [[2, 3, 6, 10], [6, 10, 3, 8], [4, 5, 6, 8], [8, 6, 4, 5]], [4, 6, 5, 2]),
    ([[0, 2, 4, 5], [0, 2, 5, 6], [1, 3, 4, 6], [1, 3, 5, 6]], [[8, 4, 1, 6], [8, 2, 4, 7], [5, 4, 2, 8], [5, 3, 6, 7]], [0, 2, 6, 5]),
    ([[0, 2, 3, 6], [1, 4, 5, 7], [2, 3, 6, 7], [4, 5, 6, 7]], [[2, 10, 7, 4], [2, 5, 4, 8], [10, 3, 4, 8], [4, 5, 6, 8]], [2, 7, 3, 6]),
    ([[0, 2, 5, 7], [1, 5, 6, 7], [2, 3, 4, 6], [3, 4, 6, 7]], [[2, 10, 7, 6], [2, 3, 10, 6], [10, 6, 3, 8], [5, 3, 7, 6]], [2, 5, 6, 7]),
]

if __name__ == '__main__':
    print('$ python3 k4/ksens/refute_oc1max_k4.py'); t0 = time.time(); n = 4; ok_all = True
    for c, (S, V, P) in enumerate(CEX):
        m = 1 + max(max(s) for s in S); I = brute.Inst(S, V, m); O = ocsat.OC(S, V, m); Q = ocseq.Seq(S, V, m)
        orders = [o for o in itertools.permutations(range(n)) if tuple(I.sd(o)) == tuple(P)]
        Y = tuple(P); b = ocsat.bases_of(Y, n); base = [frozenset([g]) for g in Y]
        sat = [O.holds(b, chain='none', A=1), O.holds(b, chain='none'), O.holds(b, chain='any', A=1), O.holds(b, chain='any'),
               O.holds(b, chain='any', A=1, multi=True), O.holds(b, chain='any', multi=True)]
        ch = I.chains(base); ch0 = I.chains(base, empty_pass=False); rd = I.rounds(base)
        bf = [I.completes(base, 1), I.completes(base), any(I.completes(s, 1) for s in ch), any(I.completes(s) for s in ch),
              any(I.completes(s, 1) for s in rd), any(I.completes(s) for s in rd)]
        seq1 = next((k for k in range(4) if Q.holds(b, k, 1)), None); seqf = next((k for k in range(4) if Q.holds(b, k)), None)
        two = sum(1 for s in ch for s2 in I.chains([frozenset(x) for x in s]) if I.completes(s2, 1))
        a = ocsat.report(S, V, m); bb, _ = brute.report(S, V, m)
        mism = sum(1 for y in a for k in ('md', 'ext', 'ext1', 'oc', 'oc1') if a[y][k] != bb[y][k])
        ok = (orders and sum(1 for g in Y if g is not None) == nu(S, V) and not any(sat) and not any(bf) and seq1 == 2
              and two > 0 and mism == 0)
        ok_all &= bool(ok)
        print('#%d %s orders %s nu %d; SAT [picks A1, picks free, chain A1, chain free, round A1, round free] %s; '
              'brute %s; one-chain states %d (official rule %d), round states %d; least chains A1 %s free %s; '
              'two-chain states with a one-absorber completion (brute) %d; every order: OC1 fails on %d of %d starts, '
              'MD fails on %d, SD-C %s; ocsat/brute mismatches %d; %s' % (
              c + 1, json.dumps((S, V)), orders[:2], nu(S, V), sat, bf, len(ch), len(ch0), len(rd), seq1, seqf, two,
              sum(1 for r in a.values() if not r['oc1']), len(a), sum(1 for r in a.values() if not r['md']),
              any(r['ext'] for r in a.values()), mism, 'OK' if ok else 'NOT CONFIRMED'), flush=True)
        O.close(); Q.close()
    print('all 11 confirmed: OC1^max, OC^max and one round fail at k = 4 (n = 4); two chains repair each:', ok_all,
          '; %.0f s' % (time.time() - t0))
