"""As k3_leader_r.py, but the original run is itself random: random insertion choices and random R1 order (any run of
Phase 1, as in proofs/lb_last_step.md, where nothing depends on these choices).  Values: random strict balanced
realizations of random tie-heavy profiles, and plain random cores.

    python3 k4/sdc/k3_leader_r2.py SEED N n m CONT"""
import sys, random, collections, json
import _paths
import k3algo as K
from k3_leader_r import run_from


def random_run(n, m, v, rng):
    """A random full run: every choice random; return (info, order)."""
    agents = list(range(n))
    # run_from with an empty prefix and a random first leader, random continuation
    return run_from(n, m, v, [], rng.randrange(n), rng)


def last_block_start_info(order, v):
    pool = set(g for i in range(len(v)) for g in v[i]); start = 0
    for t, i in enumerate(order):
        if all(g in pool for g in v[i]): start = t
        rr = [g for g in v[i] if g in pool]
        if rr: pool.discard(max(rr, key=lambda g: (v[i][g], -g)))
    return start


if __name__ == '__main__':
    seed, N, n, m, cont = map(int, sys.argv[1:6]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/k3_leader_r2.py', *sys.argv[1:])
    tries = 0
    while C['bad case'] < N and tries < 200000:
        tries += 1
        if rng.random() < 0.5:
            vt = K.random_hard(n, m, rng); P = K.profile_of(vt, n, list(range(m)))
            v = [{P[i][0]: 10, P[i][1]: 8, P[i][2]: 5} for i in range(n)]
        else:
            v = K.random_core(n, m, rng, vmax=30)
            if any(len(set(x.values())) < 3 for x in v): continue
        info, order = random_run(n, m, v, rng)
        if not info['branch'].startswith('rot'): continue
        C['bad case'] += 1
        s = last_block_start_info(order, v); r = info['r']
        assert r in order[s:]
        for t in range(cont):
            i2, o2 = run_from(n, m, v, order[:s], r, rng if t else None)
            C['reruns'] += 1
            ok = not i2['branch'].startswith('rot'); C['reruns without rotation'] += ok
            if not ok and C['shown'] < 3:
                C['shown'] += 1; print('ROTATES AGAIN', json.dumps(([sorted(x.items()) for x in v], order, r, o2)))
    print('tries', tries, dict(C))
