"""k = 4 analogue of k3_leader*.py: for an R1-priority run whose SD outcome does not extend, re-run the last block with
another leader (continuation: R1 priority, ties by index).  Which leaders work?  Roles: the last-processed agent of the
block (LAST), the last-processed terminal, i.e. agent whose pick nobody else wants (TERM), any other agent (OTHER).

    python3 k4/sdc/k4_leader.py SRC N SEED     SRC: screen, or json:FILE of [sets, vals] lines"""
import sys, os, json, random, collections
import _paths
from sdclib import Enc
from sdc_orders import completable


def run(E, prefix, leader, rng=None):
    left = set(range(E.m)); Y = [None] * E.n; done = []; dset = set()
    def take(i):
        av = [g for g in E.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: (E.v[i][h], -h)); Y[i] = g; left.discard(g)
        done.append(i); dset.add(i)
    for i in prefix: take(i)
    if leader is not None: take(leader)
    while len(done) < E.n:
        rest = [i for i in range(E.n) if i not in dset]
        lost = [i for i in rest if any(g not in left for g in E.R[i])]
        cand = lost if lost else rest
        take(rng.choice(cand) if rng else min(cand))
    return Y, done


def blocks(E, order):
    left = set(range(E.m)); starts = []
    for t, i in enumerate(order):
        if all(g in left for g in E.R[i]): starts.append(t)
        av = [g for g in E.R[i] if g in left]
        if av: left.discard(max(av, key=lambda h: (E.v[i][h], -h)))
    return starts


def wanted(E, Y):
    w = set()
    for i in range(E.n):
        vy = E.v[i][Y[i]] if Y[i] is not None else 0
        for j in range(E.n):
            if j != i and Y[j] is not None and E.v[i].get(Y[j], 0) > vy: w.add(j)
    return w


def instances(src):
    if src == 'screen':
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from ss_screen import screen_set
        S = screen_set(); os.chdir(cwd)
        for name, I in S:
            yield name, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m
    else:
        for k, line in enumerate(open(src[5:])):
            sets, vals = json.loads(line)[:2]
            yield src + ':%d' % k, sets, vals, 1 + max(max(s) for s in sets)


if __name__ == '__main__':
    src, N, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/k4_leader.py', *sys.argv[1:])
    for name, sets, vals, m in instances(src):
        E = Enc(sets, vals, m)
        for t in range(N):
            Y, order = run(E, [], rng.randrange(E.n), rng)
            if completable(E, Y): continue
            C['bad runs'] += 1
            s = blocks(E, order)[-1]; prefix, B = order[:s], order[s:]
            w = wanted(E, Y)
            last = B[-1]; terms = [i for i in B if i not in w and Y[i] is not None]; term = terms[-1] if terms else None
            work = [y for y in B if completable(E, run(E, prefix, y)[0])]
            C['some agent of the last block works'] += bool(work)
            C['LAST works'] += last in work
            C['TERM works'] += term in work
            C['last block size %d, working leaders %d' % (len(B), len(work))] += 1
            if not work and C['shown'] < 3:
                C['shown'] += 1; print('NONE', name, json.dumps((sets, vals, order)), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
