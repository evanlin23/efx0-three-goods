"""Order rules from the n = 2 failures ("the claimant that needs its top most goes first").  At every step, among the
agents allowed (R1: agents that lost a good first; or all), take the agent maximizing a need score of its favourite
remaining good y, with the remaining goods ranked y > y2 > y3 > ...:
  need2 = v(y) - v(y2) - v(y3)            (top versus its next two)
  needall = v(y) - sum of the rest          (top versus everything else left)
Ties by index.  Does the one resulting order extend?

    python3 k4/sdc/sdc_need.py screen|suite"""
import sys, os, json, glob, collections
import _paths
from sdclib import Enc
from sdc_orders import completable


def score(E, i, left, kind):
    av = sorted((E.v[i][g] for g in E.R[i] if g in left), reverse=True)
    if not av:
        return -10**9
    if kind == 'need2':
        return av[0] - sum(av[1:3])
    return av[0] - sum(av[1:])


def rule_order(E, kind, r1):
    left = set(range(E.m)); Y = [None] * E.n; done = []
    while len(done) < E.n:
        rest = [i for i in range(E.n) if i not in done]
        lost = [i for i in rest if any(g not in left for g in E.R[i])] if r1 else []
        cand = lost if lost else rest
        i = max(cand, key=lambda j: (score(E, j, left, kind), -j))
        av = [g for g in E.R[i] if g in left]
        if av:
            g = max(av, key=lambda h: (E.v[i][h], -h)); Y[i] = g; left.discard(g)
        done.append(i)
    return Y, done


def instances(src):
    out = []
    if src == 'screen':
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from ss_screen import screen_set
        for name, I in screen_set():
            out.append((name, I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m))
        os.chdir(cwd)
    else:
        for f in sorted(glob.glob(os.path.join(_paths.ROOT, 'k4/suite/instances/*.json'))):
            d = json.load(open(f))
            if d.get('vals') and d.get('sets'):
                out.append((d.get('id'), d['sets'], d['vals'], d.get('m') or 1 + max(max(s) for s in d['sets'])))
    return out


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); fails = collections.defaultdict(list)
    print('$ python3 k4/sdc/sdc_need.py', *sys.argv[1:])
    for name, sets, vals, m in instances(src):
        E = Enc(sets, vals, m); C['instances'] += 1
        for kind in ('need2', 'needall'):
            for r1 in (True, False):
                Y, order = rule_order(E, kind, r1)
                ok = completable(E, Y); key = kind + (' R1' if r1 else ' plain')
                C[key + ' extends'] += ok
                if not ok: fails[key].append(name)
    for k in sorted(C, key=str): print(k, C[k])
    for k, v in fails.items(): print('fails', k, v[:8])
