"""Cross-check of k3max.py (k4/ksens.md §8) against ocsat.py (SAT, sdclib's EFX0 clauses, its own chain encoding) on
random (hypergraph, strict profile) pairs at k = 3: for every maximum-matching start, k3max's classification without
its witness cache (exact backtracking at the picks; else every one-chain state, official move rule) must agree with
ocsat: 'complete at the picks' iff OC.holds(chain='none', A=1); 'one chain' implies OC.holds(chain='any', A=1) (ocsat
also lets an agent pass on an empty base, so it can only be more permissive).

    python3 k4/ksens/k3max_xcheck.py n SAMPLES SEED [MMIN]      SAMPLES = 0: every hypergraph and every profile"""
import sys, random, itertools, collections
import _paths
import k3max, brute, ocsat

if __name__ == '__main__':
    n, T, seed = map(int, sys.argv[1:4]); rng = random.Random(seed)
    print('$ python3 k4/ksens/k3max_xcheck.py', *sys.argv[1:], flush=True)
    mmin = int(sys.argv[4]) if len(sys.argv) > 4 else n
    H = [(m, s) for m in range(mmin, 3 * n + 1) for s in k3max.hypergraphs(n, m)]
    C = collections.Counter()
    if T: jobs = ((m, s, [rng.choice(k3max.TYPES[len(x)]) for x in s]) for m, s in (rng.choice(H) for _ in range(T)))
    else: jobs = ((m, s, list(p)) for m, s in H for p in itertools.product(*[k3max.TYPES[len(x)] for x in s]))
    for m, sets, prof in jobs:
        V = [[0] * m for _ in range(n)]
        for i, (s, ty) in enumerate(zip(sets, prof)):
            for g, x in zip(s, ty): V[i][g] = x
        vals = [[V[i][g] for g in s] for i, s in enumerate(sets)]
        prefs = [sorted(s, key=lambda g, i=i: -V[i][g]) for i, s in enumerate(sets)]
        v_ = k3max.nu(sets); O = ocsat.OC(sets, vals, m); I = brute.Inst(sets, vals, m)
        Ys = set(k3max.sd(prefs, o) for o in itertools.permutations(range(n)))
        if Ys != k3max.sd_all(prefs): C['SD MISMATCH'] += 1; print('SD MISMATCH', sets, vals, flush=True)
        for Y in Ys:
            if sum(1 for g in Y if g is not None) != v_: continue
            base = [frozenset([g]) if g is not None else frozenset() for g in Y]
            if k3max.find_completion(V, base, m, 1) is not None: mine = 'picks'
            elif any(k3max.find_completion(V, st, m, 1) is not None for st in I.chains(base, empty_pass=False)): mine = 'chain'
            else: mine = 'FAIL'
            b = ocsat.bases_of(Y, n); s0 = O.holds(b, chain='none', A=1); s1 = s0 or O.holds(b, chain='any', A=1)
            sat = 'picks' if s0 else 'chain' if s1 else 'FAIL'
            C['starts'] += 1; C[mine] += 1
            if mine != sat and not (mine == 'FAIL' and sat == 'chain'):
                C['MISMATCH'] += 1; print('MISMATCH', mine, sat, sets, vals, Y, flush=True)
        O.close()
    print(dict(C))
