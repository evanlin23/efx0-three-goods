"""Survey of the rotation cases of K3S (index leaders): which first leaders work, with and without adversarial later
leaders, and how they relate to the failed run (k*, chain, r, B*, leaders).  One process.

  python survey.py cores 4          every profile of every core with n <= 4
  python survey.py small 3 6        every ranking profile n = 3, m = 6
"""
import sys, os, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', '..'))
from fl import run, index_leader, first_then_index, all_runs, bad_case


def rand_profiles(K, seed, maxn):
    """K random ranking profiles, n in 3..maxn, m in n+1..2n+3 (goods nobody ranks are worthless)"""
    import random
    rng = random.Random(seed)
    for _ in range(K):
        n = rng.randint(3, maxn); m = rng.randint(n + 1, 2 * n + 3)
        yield n, m, [tuple(rng.sample(range(m), 3)) for _ in range(n)]


def cases(argv):
    if argv[0] == 'rand':
        return rand_profiles(int(argv[1]), int(argv[2]), int(argv[3]))
    if argv[0] == 'cores':
        from lbx import core_profiles
        minn = int(argv[2]) if len(argv) > 2 else 2
        sample = int(argv[3]) if len(argv) > 3 else 0
        return core_profiles(int(argv[1]), sample=sample, minn=minn)
    from test_k3s import gen_small
    return gen_small(int(argv[1]), int(argv[2]))


def main(argv):
    c = collections.Counter(); ex = {}
    for n, m, rank in cases(argv):
        st = run(n, m, rank, index_leader)
        if st.ok: continue
        c['rot'] += 1
        k, chain = bad_case(st)
        Bstar = st.blocks[-1]
        W = [x for x in range(n) if run(n, m, rank, first_then_index(x)).ok]
        c['nleaders=%d' % len(st.leaders)] += 1
        c['W nonempty'] += bool(W)
        # adversarial later leaders: x is robust if every run with first leader x works
        R = []
        for x in range(n):
            if all(s.ok for _, s in all_runs(n, m, rank, prefix=(x,))): R.append(x)
        c['robust first leader exists'] += bool(R)
        anyseq = any(s.ok for _, s in all_runs(n, m, rank))
        c['some leader sequence works'] += anyseq
        roles = {'r': st.r, 'k*': k, 'x1': chain[1] if len(chain) > 1 else None}
        for nm, a in roles.items():
            c['%s works' % nm] += a in W
            c['%s robust' % nm] += a in R
        c['W meets chain'] += bool(set(W) & set(chain))
        c['W meets chain minus k*'] += bool(set(W) & set(chain[1:]))
        c['W meets B*'] += bool(set(W) & set(Bstar))
        c['W meets B* minus k*'] += bool(set(W) & (set(Bstar) - {k}))
        c['W meets non-leaders'] += bool(set(W) - set(st.leaders))
        c['W subset non-leaders'] += set(W) <= set(range(n)) - set(st.leaders)
        c['some non-leader of the failed run fails'] += bool((set(range(n)) - set(st.leaders)) - set(W))
        if not W: ex.setdefault('W empty', (rank, m))
        if not R: ex.setdefault('no robust', (rank, m))
        if st.r not in W: ex.setdefault('r fails', (rank, m, st.r, W))
        if not set(W) & set(chain[1:]): ex.setdefault('chain-k fails', (rank, m, chain, W))
    print(' '.join(argv))
    for key in sorted(c): print('  %-40s %d' % (key, c[key]))
    for key, v in ex.items(): print('  example', key, v)


if __name__ == '__main__':
    main(sys.argv[1:])
