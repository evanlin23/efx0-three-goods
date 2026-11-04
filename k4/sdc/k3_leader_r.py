"""K4.SDC.K3: in LB+'s bad case, re-run the last block with r (the last-processed agent that is not upgraded, the end of
every need chain from the leader k*) as its leader, keeping the earlier blocks; continue Phase 1 with R1 priority.  Does
the new run avoid the bad case (LB+ then needs no rotation, and its output completes the new SD outcome)?  Also tries
random R1 continuations after r.

    python3 k4/sdc/k3_leader_r.py SEED N n m [CONT]"""
import sys, random, collections, json
import _paths
import k3algo as K


def run_from(n, m, v, prefix, leader, rng=None):
    """Phase 1: prefix, then leader (an insertion step), then R1 priority (lost agents first); ties by index, or at
    random if rng.  Then LB+'s Phase 2 (k3algo._lbplus_fast) on this run."""
    agents = list(range(n)); goods = list(range(m))
    a, b, c = {}, {}, {}
    for i in agents:
        a[i], b[i], c[i] = K.sort3(lambda g: v[i][g], None, sorted(v[i]))
    rank = {i: {a[i]: 0, b[i]: 1, c[i]: 2} for i in agents}
    holders = collections.defaultdict(list)
    for i in agents:
        for g in (a[i], b[i], c[i]): holders[g].append(i)
    pool = set(goods); order, Y, blk = [], {}, {}; nblk = 0; done = set()
    def take(i, full):
        nonlocal nblk
        if full: nblk += 1
        done.add(i); order.append(i); blk[i] = nblk
        y = next((g for g in (a[i], b[i], c[i]) if g in pool), None); Y[i] = y
        if y is not None: pool.discard(y)
    def isfull(i): return all(g in pool for g in (a[i], b[i], c[i]))
    for i in prefix: take(i, isfull(i))
    assert isfull(leader)
    take(leader, True)
    while len(done) < n:
        rest = [i for i in agents if i not in done]
        lost = [i for i in rest if not isfull(i)]
        cand = lost if lost else rest
        i = rng.choice(cand) if rng else min(cand)
        take(i, not lost)
    info = {'peeled': 0, 'branch': None, 'core_n': n, 'core_m': m}
    X = [None] * m
    X, info = K._lbplus_fast(agents, goods, order, a, b, c, rank, holders, Y, blk, X, info)
    assert K.raw_efx0(n, m, v, X)
    return info, order


def last_block_start(order, v):
    pool = set(g for i in range(len(v)) for g in v[i]); start = 0
    for t, i in enumerate(order):
        if all(g in pool for g in v[i]): start = t
        rr = [g for g in v[i] if g in pool]
        if rr: pool.discard(max(rr, key=lambda g: (v[i][g], -g)))
    return start


if __name__ == '__main__':
    seed, N, n, m = map(int, sys.argv[1:5]); cont = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/k3_leader_r.py', *sys.argv[1:])
    while C['bad case'] < N:
        vt = K.random_hard(n, m, rng); P = K.profile_of(vt, n, list(range(m)))
        v = [{P[i][0]: 10, P[i][1]: 8, P[i][2]: 5} for i in range(n)]
        X, info = K.fast(n, m, v)
        if not info['branch'].startswith('rot') or info['peeled']: continue
        C['bad case'] += 1
        order = info['order']; s = last_block_start(order, v); r = info['r']
        i2, o2 = run_from(n, m, v, order[:s], r)
        C['leader r, R1 by index: no rotation'] += not i2['branch'].startswith('rot')
        if i2['branch'].startswith('rot') and C['shown'] < 3:
            C['shown'] += 1; print('ROTATES AGAIN', json.dumps(([sorted(x.items()) for x in v], order, r, o2)))
        for t in range(cont):
            i3, _ = run_from(n, m, v, order[:s], r, rng)
            C['leader r, random R1 continuation: runs'] += 1
            C['leader r, random R1 continuation: no rotation'] += not i3['branch'].startswith('rot')
    print(dict(C))
