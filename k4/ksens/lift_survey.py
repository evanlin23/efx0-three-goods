"""Lifts of the hard k = 4 instances (k4/ksens.md §6): every instance of results/k4_ksens/seeds_k4_hard.txt (the DE4
screen set with the GM4 family, T3, Q2, the logged OC and MD climb results), n <= NMAX, with L new low goods added to
each agent (climb.lift: each new good valued below the agent's lowest good, some shared with an existing good), REP
random lifts each; every order: SD-C, MD, OC, OC1.

    python3 k4/ksens/lift_survey.py L REP SEED [NMAX]"""
import sys, json, random, collections, time
import _paths
import ocsat
from climb import load_seeds, lift

if __name__ == '__main__':
    L, REP, seed = map(int, sys.argv[1:4]); NMAX = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/ksens/lift_survey.py', *sys.argv[1:], flush=True)
    seeds = [s for s in load_seeds(_paths.ROOT + '/results/k4_ksens/seeds_k4_hard.txt') if 2 <= len(s[0]) <= NMAX]
    for sets0, vals0 in seeds:
        for r in range(REP):
            sets, vals = lift(sets0, vals0, L, rng); m = 1 + max(max(s) for s in sets)
            res = ocsat.report(sets, vals, m); C['instances'] += 1; C['starts'] += len(res)
            for k in ('md', 'ext', 'ext1', 'oc', 'oc1'): C['starts %s' % k] += sum(r_[k] for r_ in res.values())
            if not any(r_['ext'] for r_ in res.values()):
                C['SD-C fails'] += 1; print('FAIL SD-C', json.dumps((sets, vals)), flush=True)
            for k in ('md', 'oc', 'oc1'):
                bad = [Y for Y, r_ in res.items() if not r_[k]]
                if bad:
                    C['instances failing %s' % k] += 1
                    if C['shown ' + k] < 3:
                        C['shown ' + k] += 1
                        print('FAIL', k.upper(), json.dumps((sets, vals)), 'picks', bad[0], 'order', res[bad[0]]['order'], flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
