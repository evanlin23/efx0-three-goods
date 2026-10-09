"""Stress test of Conjecture FL on DISJOINT UNIONS of two instances on which K3S (index leaders) needs the rotation.

Why unions: with later leaders by index, the component that does not contain the first leader is drafted by index,
so it fails internally (Lemma T: one exposed leader more than free agents other than its r).  The component of the
first leader must then make up for it, and exposure for an absorber OUTSIDE a component is different from exposure
for its own r (Y_r no longer protects; its own r, if it holds its top with b and c left over, becomes exposed).

Components: every rotation case among the ranking profiles with n = 3, m = 5 (and optionally the cores n <= 4).
The union puts component 1 on agents 0..n1-1 and goods 0..m1-1, component 2 after them (shuffle=1: agents of the
union in a random interleaving).

Reports, over unions: K3S index fails; FL (some first leader, later by index) fails; FLa (some first leader, later
leaders arbitrary: some sequence extending it) fails; SEQ (some leader sequence at all) fails; the rules of
rules.py.
"""
import sys, os, collections, random, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', '..'))
from fl import run, index_leader, first_then_index, all_runs
from rules import RULES, RUNNERS


def failing(src):
    return [(n, m, rank) for n, m, rank in src if not run(n, m, rank, index_leader).ok]


def union(c1, c2, perm=None):
    n1, m1, r1 = c1; n2, m2, r2 = c2
    rank = [tuple(r) for r in r1] + [tuple(g + m1 for g in r) for r in r2]
    n = n1 + n2
    if perm is not None: rank = [rank[perm[i]] for i in range(n)]
    return n, m1 + m2, rank


def main(argv):
    from test_k3s import gen_small
    from lbx import core_profiles
    comps = failing(gen_small(3, 5))
    if 'cores' in argv: comps += failing(core_profiles(4))
    shuffle = 'shuffle' in argv
    limit = int(next((a.split('=')[1] for a in argv if a.startswith('limit=')), 10 ** 9))
    rng = random.Random(1)
    pairs = list(itertools.product(range(len(comps)), repeat=2))
    rng.shuffle(pairs); pairs = pairs[:limit]
    c = collections.Counter({'unions': 0, 'index works': 0, 'FL fails': 0, 'FLa fails': 0, 'sec_small fails': 0,
                             'iter_r fails': 0}); ex = {}
    for a, b in pairs:
        perm = None
        if shuffle:
            perm = list(range(comps[a][0] + comps[b][0])); rng.shuffle(perm)
        n, m, rank = union(comps[a], comps[b], perm)
        c['unions'] += 1
        st = run(n, m, rank, index_leader)
        if st.ok: c['index works'] += 1; continue
        W = [x for x in range(n) if run(n, m, rank, first_then_index(x)).ok]
        if len(st.leaders) >= 2:
            c['index run has >= 2 leaders'] += 1
            if st.leaders[-1] in W: c['... and k* (its last leader) works first'] += 1
            else: ex.setdefault('k* fails', (n, m, rank, st.leaders, W))
        if not W:
            c['FL fails'] += 1; ex.setdefault('FL', (n, m, rank))
            fla = any(any(t.ok for _, t in all_runs(n, m, rank, prefix=(x,))) for x in range(n))
            if not fla: c['FLa fails'] += 1; ex.setdefault('FLa', (n, m, rank))
        for nm in ('sec_small',):
            if not run(n, m, rank, RULES[nm]).ok: c[nm + ' fails'] += 1; ex.setdefault(nm, (n, m, rank))
        if not RUNNERS['iter_r'](n, m, rank).ok: c['iter_r fails'] += 1; ex.setdefault('iter_r', (n, m, rank))
    print(' '.join(argv), dict(c), flush=True)
    for k, v in ex.items(): print('  example', k, v)


if __name__ == '__main__':
    main(sys.argv[1:])
