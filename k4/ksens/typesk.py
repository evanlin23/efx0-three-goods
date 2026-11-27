"""Strict additive order types of d goods found on a grid (k4/ksens.md §8): the sign vectors of all disjoint pairs
realized by strictly decreasing integer vectors in [1, B]^d (the ranking v_0 > ... > v_{d-1} fixed).  For d <= 5
types5.py / kcegar.reps prove the grid complete (bound d times the largest (d-1)-minor of a {-1, 0, 1} matrix).  For
d = 6 that bound is 6 * 48 = 288, too large to scan, so a smaller grid gives a subset of the types; the counts for
growing B show how close it is to all of them.

    python3 k4/ksens/typesk.py d B [B ...]     writes results/k4_ksens/types{d}_B{maxB}.json.gz"""
import sys, itertools, json, gzip, time
import numpy as np


def scan(d, B):
    P = [(S, T) for S in range(1, 1 << d) for T in range(S + 1, 1 << d) if S & T == 0]
    masks = np.array([[S >> g & 1 for g in range(d)] for S in range(1 << d)], dtype=np.int64)
    Si = np.array([S for S, T in P]); Ti = np.array([T for S, T in P]); seen = {}; buf = []
    def flush(buf):
        X = np.array(buf, dtype=np.int64); sums = X @ masks.T; D = sums[:, Si] - sums[:, Ti]
        ok = (D != 0).all(1); X, D = X[ok], D[ok]
        keys, idx = np.unique(np.packbits(D > 0, axis=1), axis=0, return_index=True)
        for kb, i in zip(map(bytes, keys), idx):
            v = tuple(int(x) for x in X[i]); key = (max(v), sum(v), v)
            if kb not in seen or key < seen[kb][0]: seen[kb] = (key, v)
    for t in itertools.combinations(range(B, 0, -1), d):
        buf.append(t)
        if len(buf) == 1 << 20: flush(buf); buf = []
    if buf: flush(buf)
    return {kb: kv[1] for kb, kv in seen.items()}, len(P)


if __name__ == '__main__':
    d = int(sys.argv[1]); Bs = [int(a) for a in sys.argv[2:]]; t0 = time.time(); res = None
    print('$ python3 k4/ksens/typesk.py', *sys.argv[1:], flush=True)
    for B in Bs:
        res, npairs = scan(d, B)
        print('d = %d, B = %d: %d strict types with a fixed ranking (%d disjoint pairs; %.0f s)' % (d, B, len(res), npairs,
              time.time() - t0), flush=True)
    reps = sorted(res.values())
    json.dump({'k': d, 'grid': max(Bs), 'ranking': 'decreasing', 'reps': reps},
              gzip.open('results/k4_ksens/types%d_B%d.json.gz' % (d, max(Bs)), 'wt'))
    print('wrote results/k4_ksens/types%d_B%d.json.gz (%d representatives)' % (d, max(Bs), len(reps)))
