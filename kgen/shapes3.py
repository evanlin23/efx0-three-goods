"""Which move shapes repair the hard starts of OC1 at n = 3 (kgen/oc3.c, shapes())?  Agents are renamed by their
position in the order (1 = first picker, 2, 3).  For every start whose picks have no one-absorber completion, collect
the shapes (t = 1 chains x0 -> x1, t = 2 chains x0 -> x1 -> x2, t = 0 at x; with the absorber) that some EFX0
allocation realizes; report how many hard starts each shape, and each shape family, covers.

    python3 kgen/shapes3.py SEED N MMIN MMAX"""
import sys, random, collections, json, time, os, multiprocessing as mp
from oc3lib import shapes, ORD, picks
from gen3 import gen

KINDS = ['general', 'zeros', 'ident', 'junk', 'klim:3', 'klim:4', 'klim:6', 'ties']


def role(shape, absorber, order):
    pos = {a: k + 1 for k, a in enumerate(order)}
    s = (shape[0],) + tuple(pos[x] for x in shape[1:])
    return s, (pos[absorber] if absorber is not None else 0)


def job(args):
    seed, kind, m = args
    if kind.startswith('klim'): m = min(m, 3 * int(kind.split(':')[1]))
    rng = random.Random(seed); v = gen(kind, m, rng); sh = shapes(v); out = []
    for o, S in enumerate(sh):
        if any(s[0] == ('none',) for s in S): continue
        y = picks(v, ORD[o])
        val = lambda i, g: v[i][g] if g is not None else 0
        # wants[i][j]: i prefers j's pick to its own
        wants = [[j != i and y[j] is not None and val(i, y[j]) > val(i, y[i]) for j in range(3)] for i in range(3)]
        frozen = [any(wants[i][j] for i in range(3)) for j in range(3)]
        pos = {a: k + 1 for k, a in enumerate(ORD[o])}
        R = []
        for s, a in S:
            r, ar = role(s, a, ORD[o])
            feat = set()
            if s[0] == 't1':
                x0, x1 = s[1], s[2]; z = 3 - x0 - x1
                if frozen[x0]: feat.add('x0 frozen')
                if wants[x1][x0]: feat.add('x1 wants y_x0')
                if a is None or a == z: feat.add('absorber z or none')
                if a == z: feat.add('absorber z')
                if a is None: feat.add('no absorber')
                if not frozen[z]: feat.add('z unfrozen')
            R.append((r, ar, frozenset(feat)))
        out.append(R)
    return v, out


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); t0 = time.time()
    print('$ python3 kgen/shapes3.py', *sys.argv[1:], flush=True)
    tasks = [(seed * 1000003 + t, KINDS[t % len(KINDS)], rng.randint(lo, hi)) for t in range(N)]
    C = collections.Counter(); F = collections.Counter(); hard = 0; uncovered = collections.Counter(); ex = {}
    fam = {
        't1, absorber z or none': lambda s, a, ft: 'absorber z or none' in ft,
        't1, absorber z': lambda s, a, ft: 'absorber z' in ft,
        't1, no absorber': lambda s, a, ft: 'no absorber' in ft,
        't1, x0 frozen': lambda s, a, ft: 'x0 frozen' in ft,
        't1, x1 wants y_x0': lambda s, a, ft: 'x1 wants y_x0' in ft,
        't1, x1 wants y_x0, absorber z or none': lambda s, a, ft: {'x1 wants y_x0', 'absorber z or none'} <= ft,
        't1, x0 frozen, absorber z or none': lambda s, a, ft: {'x0 frozen', 'absorber z or none'} <= ft,
        't1, z unfrozen, absorber z or none': lambda s, a, ft: {'z unfrozen', 'absorber z or none'} <= ft,
        'strict (t>=1)': lambda s, a, ft: s[0] in ('t1', 't2'),
        't1 only': lambda s, a, ft: s[0] == 't1',
        't2 only': lambda s, a, ft: s[0] == 't2',
        't1, first agent keeps (z = 1)': lambda s, a, ft: s[0] == 't1' and 1 not in s[1:],
        't1, last agent keeps (z = 3)': lambda s, a, ft: s[0] == 't1' and 3 not in s[1:],
        't1 or t2 starting at agent 1': lambda s, a, ft: s[0] in ('t1', 't2') and s[1] == 1,
        't1 2->3 or 3->2': lambda s, a, ft: s in [('t1', 2, 3), ('t1', 3, 2)],
        'absorber is the last agent': lambda s, a, ft: a == 3,
        'absorber is chain end x_t': lambda s, a, ft: s[0] in ('t1', 't2') and a == s[-1],
        'absorber off the chain or none': lambda s, a, ft: s[0] in ('t1', 't2') and (a == 0 or a not in s[1:]),
    }
    with mp.Pool(os.cpu_count()) as pool:
        for v, out in pool.imap_unordered(job, tasks, chunksize=8):
            for S in out:
                hard += 1
                for s in {s for s, a, ft in S}: C[s] += 1
                for name, f in fam.items():
                    if any(f(s, a, ft) for s, a, ft in S): F[name] += 1
                    elif name not in ex: ex[name] = (v, S)
                    else: uncovered[name] += 0
    print('hard starts (picks have no one-absorber completion):', hard)
    print('-- shapes by order position (starts covered):')
    for s, c in C.most_common(): print('  %-20s %d' % (s, c))
    print('-- families (starts covered of %d):' % hard)
    for name in fam: print('  %-40s %d' % (name, F[name]))
    print('-- an uncovered start per family:')
    for name, (v, S) in ex.items(): print('  ', name, json.dumps(v), S)
    print('time %.0f s' % (time.time() - t0))
