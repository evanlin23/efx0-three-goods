"""Cross-check of the three round implementations (k4/ksens.md §6): ocsat.OC.holds(multi=True), ocseq.Seq.holds(1,
multi=True) and brute.Inst.rounds (enumeration from the definition), on random PW-family instances (every start, free
and one-absorber completions; brute force only where n^m is small).

    python3 k4/ksens/xcheck_rounds.py SEED T n K [SEEDFILE]   (SEEDFILE: instances of that file with n agents instead)"""
import sys, random, collections, time, json
import _paths
import ocsat, ocseq, brute
from gen import gen

if __name__ == '__main__':
    seed, T, n, K = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/ksens/xcheck_rounds.py', *sys.argv[1:], flush=True)
    if len(sys.argv) > 5:
        from climb import load_seeds
        pool = [x for x in load_seeds(sys.argv[5]) if len(x[0]) == n][:T]
    else:
        pool = [gen('pwfam', rng, n, K) for t in range(T)]
    for sets, vals in pool:
        m = 1 + max(max(s) for s in sets)
        O = ocsat.OC(sets, vals, m); Q = ocseq.Seq(sets, vals, m); I = brute.Inst(sets, vals, m) if n ** m <= 3 * 10 ** 6 else None
        for Y in ocsat.starts(sets, vals, m):
            b = ocsat.bases_of(Y, n); C['starts'] += 1
            rd = I.rounds([frozenset([g]) if g is not None else frozenset() for g in Y]) if I else None
            for A in (None, 1):
                a = O.holds(b, chain='any', A=A, multi=True); q = Q.holds(b, 1, A, multi=True)
                r = any(I.completes(s, A) for s in rd) if I else None
                C['compared'] += 1; C['round repairs %s' % a] += 1
                if a != q or (r is not None and r != a):
                    C['MISMATCH'] += 1; print('MISMATCH', A, json.dumps((sets, vals)), Y, a, q, r, flush=True)
                if r is not None: C['with brute force'] += 1
        O.close(); Q.close()
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
