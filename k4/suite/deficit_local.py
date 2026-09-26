"""Route 1 test (k4/strategy.md §2.1): is the removal-only deficit locally improvable?

DEF-LOCAL_k: every min-frozen P in 𝒫 with def(P) > 0 has a min-frozen P' whose bases differ from P's for at most k
agents and def(P') < def(P) (def = +infinity when no owner has a safe bundle). For each instance, prints the least k
that works for every such P (k* = max over P of the distance to the nearest min-frozen P' with a smaller deficit).
usage: python3 k4/suite/deficit_local.py [IDS...]   (default: every suite instance with omega >= 1)"""
import json, glob, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import model as M

INF = 10 ** 9


def kstar(d, cap=6):
    I = M.Inst(d['sets'], d['vals'], d.get('m'))
    I.preallocs()
    if I.omega <= 0: return None, 'omega<=0'
    mp = [Bs for Bs, NA in I.minP]
    df = {Bs: (lambda x: INF if x is None else x)(I.deficit(Bs)) for Bs in mp}
    worst = 0; stuck = []
    for Bs in mp:
        if df[Bs] <= 0: continue
        dist = min((sum(1 for a, b in zip(Bs, B2) if a != b) for B2 in mp if df[B2] < df[Bs]), default=None)
        if dist is None: stuck.append(Bs); continue
        worst = max(worst, dist)
    if stuck: worst = float('inf')   # a global minimum with def > 0: C4min fails, no finite k works
    mn = min(df.values())
    return worst, 'min def %s, %d min-frozen P, %d with def > 0, %d global minima of def > 0' % (
        mn if mn < INF else 'inf', len(mp), sum(1 for x in df.values() if x > 0), len(stuck))


if __name__ == '__main__':
    ids = set(sys.argv[1:])
    for f in sorted(glob.glob(os.path.join(HERE, 'instances', '*.json'))):
        d = json.load(open(f))
        if ids and d['id'] not in ids: continue
        if 'kind' in d: continue   # local configurations of k4/MINCEX.md, not complete instances
        if len(d['sets']) > 6: continue
        k, det = kstar(d)
        print('%-36s n=%d  k*=%s  %s' % (d['id'], len(d['sets']), k, det), flush=True)
