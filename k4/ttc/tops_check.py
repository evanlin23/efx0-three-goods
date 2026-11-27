"""Profiles in which every perfect SD outcome has exactly one receiver (k4/ttc.md §14.7): is every top good then the
top of a second agent?  Random strict core profiles (search4.domain) on every STRIDE-th n-agent core hypergraph with
nu = n, R profiles each.

    python3 k4/ttc/tops_check.py N STRIDE R"""
import sys, os, itertools, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ttclib as T, oc1max_n6 as O, core_climb as CC
n = int(sys.argv[1]); stride = int(sys.argv[2]); R = int(sys.argv[3]); rng = random.Random(7); C = collections.Counter()
k = 0
for n4 in range(0, n + 1):
    for m in range(4, 3 * n + 1):
        for sets in O.S4.cores(n, m, n4 == n, None if n4 == n else n4):
            k += 1
            if k % stride or CC.nu(sets) < n: continue
            for _ in range(R):
                vals = O.profile(sets, rng); E = T.Enc(sets, vals, m); outs = set()
                for pi in itertools.permutations(range(n)):
                    Y = tuple(T.sd(E, list(pi))[0])
                    if all(y is not None for y in Y): outs.add(Y)
                C['profiles'] += 1
                if all(n - len(T.frozen_set(E, T.base_of(E, Y))) == 1 for Y in outs):
                    top = [max(sets[i], key=lambda g: E.v[i][g]) for i in range(n)]; cnt = collections.Counter(top)
                    sh = all(cnt[t] >= 2 for t in top)
                    C['all one receiver: tops all shared' if sh else 'all one receiver: SOME TOP UNSHARED'] += 1
                    if not sh and C['shown'] < 3:
                        C['shown'] += 1; print('unshared', sets, vals, top)
for k_ in sorted(C): print(k_, C[k_])
