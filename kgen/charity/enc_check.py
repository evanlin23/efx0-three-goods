"""Check the SAT encoding of chlib.Enc against the raw definitions: for random instances and random complete
assignments of goods to agents or the pool, the encoding with every x-variable fixed is satisfiable exactly when the
raw checks (EFX0 and strong / weak charity) accept.  Assignments are biased toward small bundles so that both answers
occur often.

    python3 kgen/charity/enc_check.py SEED INSTANCES PER"""
import sys, random, collections
from pysat.solvers import Cadical153
from chlib import Inst, Enc, rand_inst, efx0, pool_ok

if __name__ == '__main__':
    seed, T, PER = map(int, sys.argv[1:4]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 kgen/charity/enc_check.py', *sys.argv[1:])
    for t in range(T):
        n = rng.randint(2, 5); m = rng.randint(n, 10)
        I = rand_inst(rng, n, m, 1, rng.randint(2, 6), vmax=rng.choice([5, 20, 100]), cover=False)
        for strong in (True, False):
            E = Enc(I, strong=strong)
            s = Cadical153(bootstrap_with=E.cl)
            for _ in range(PER):
                pp = rng.random()
                asg = [I.n if rng.random() < pp else rng.randrange(I.n) for g in range(I.m)]
                X = [set(g for g in range(I.m) if asg[g] == i) for i in range(I.n)]
                raw = efx0(I, X) and pool_ok(I, X, strong=strong)
                sat = s.solve(assumptions=[E.x[g][asg[g]] for g in range(I.m)])
                C['%s raw=%s sat=%s' % ('strong' if strong else 'weak', raw, sat)] += 1
            s.delete()
    for k in sorted(C): print(k, C[k])
    bad = sum(v for k, v in C.items() if ('raw=True sat=False' in k or 'raw=False sat=True' in k))
    print('mismatches', bad)
