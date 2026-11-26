"""Cross-check of ocseq.py (c chains in one SAT call) against ocsat.py (c <= 1) and kchains.py's breadth-first search
(c = 2) on random instances, every start, free and one-absorber completions.

    python3 k4/ksens/xcheck_ocseq.py SEED T n K mmax [KIND]"""
import sys, random, collections, time, json
import _paths
import ocsat, ocseq, kchains
from gen import gen

if __name__ == '__main__':
    seed, T, n, K, mmax = map(int, sys.argv[1:6]); kind = sys.argv[6] if len(sys.argv) > 6 else 'pairs'
    rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/ksens/xcheck_ocseq.py', *sys.argv[1:], flush=True)
    while C['instances'] < T:
        sets, vals = gen(kind, rng, n, K); m = 1 + max(max(s) for s in sets)
        if m > mmax: continue
        C['instances'] += 1; O = ocsat.OC(sets, vals, m); Q = ocseq.Seq(sets, vals, m)
        for Y in ocsat.starts(sets, vals, m):
            b = ocsat.bases_of(Y, n); C['starts'] += 1
            for A in (None, 1):
                a0, a1 = O.holds(b, chain='none', A=A), O.holds(b, chain='any', A=A)
                q0, q1 = Q.holds(b, 0, A), Q.holds(b, 1, A)
                if (a0, a1) != (q0, q1):
                    C['MISMATCH c<=1'] += 1; print('MISMATCH c<=1', A, json.dumps((sets, vals)), Y, (a0, a1), (q0, q1), flush=True)
                if not a1:
                    C['starts needing 2+ chains (A=%s)' % A] += 1
                    L, capped = kchains.reach(O, b, 10 ** 6)
                    a2 = any(O.holds(s, chain='need', A=A) for s in L); q2 = Q.holds(b, 2, A)
                    C['c=2 compared'] += 1
                    if a2 != q2:
                        C['MISMATCH c=2'] += 1; print('MISMATCH c=2', A, json.dumps((sets, vals)), Y, a2, q2, flush=True)
        O.close(); Q.close()
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
