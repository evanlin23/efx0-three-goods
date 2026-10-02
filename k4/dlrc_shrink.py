#!/usr/bin/env python3
"""Shrink DL_RC failures (compute/k4-rc): delete goods from a failing profile's core and re-evaluate with k4/dlrc.c.

For each profile of an inst list (k4/dlrc_failures.py's OUT_inst.json) and each set of at most --depth goods to delete
(by default only goods private to an agent of degree 4), the smaller hypergraph (goods relabelled 0..m'-1, every agent
keeping its values on its remaining goods) is kept if check4.is_core accepts it and every agent's values stay strict
and balanced (all subset sums distinct, max < sum of the others) and satisfy the private-pair condition; it is
evaluated with dlrc.c (-H). Prints every smaller profile where DL_RC fails, and writes them as an inst list.

usage: python3 k4/dlrc_shrink.py IN_inst.json OUT_inst.json [--depth=D] [--any] (--any: any good, not only private)"""
import itertools, json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4
import dlrc_hunt as H


def strict_balanced(v):
    sums = [sum(v[g] for g in range(len(v)) if S >> g & 1) for S in range(1, 1 << len(v))]
    return len(set(sums)) == len(sums) and max(v) < sum(v) - max(v)


def shrink(d, drop):
    keep = [g for g in range(d['m']) if g not in drop]
    rel = {g: i for i, g in enumerate(keep)}
    sets, vals = [], []
    for S, V in zip(d['sets'], d['vals']):
        sets.append([rel[g] for g in S if g in rel]); vals.append([v for g, v in zip(S, V) if g in rel])
    m = len(keep)
    ok, _ = check4.is_core(len(sets), m, sets, False)
    if not ok or not all(strict_balanced(V) for V in vals): return None
    deg = [sum(g in S for S in sets) for g in range(m)]
    for S, V in zip(sets, vals):
        priv = [v for g, v in zip(S, V) if deg[g] == 1]
        if len(priv) == 2 and sum(priv) >= sum(V) - sum(priv): return None
    return {'sets': sets, 'm': m, 'vals': vals}


def main(argv):
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    args = [a for a in argv if not a.startswith('--')]
    print('# command: python3 k4/dlrc_shrink.py ' + ' '.join(argv), flush=True)
    print('# dlrc.c sha256 ' + H.SHA, flush=True)
    H.build()
    insts = json.load(open(args[0])); depth = int(opt.get('depth', 1))
    out, seen, tried = [], set(), 0
    for d in insts:
        deg = [sum(g in S for S in d['sets']) for g in range(d['m'])]
        cand = [g for g in range(d['m']) if 'any' in opt or (deg[g] == 1 and any(g in S and len(S) == 4 for S in d['sets']))]
        for k in range(1, depth + 1):
            for drop in itertools.combinations(cand, k):
                e = shrink(d, set(drop))
                if e is None: continue
                key = json.dumps([e['sets'], e['vals']])
                if key in seen: continue
                seen.add(key); tried += 1
                core = {'sets': e['sets'], 'm': e['m'], 'doms': [[dict(zip(S, V))] for S, V in zip(e['sets'], e['vals'])]}
                h, _ = H.evaluate(core, [[0] * len(e['sets'])])
                if h[0]['rcf']:
                    e['id'] = '%s minus goods %s' % (d['id'], list(drop)); e['H'] = h[0]
                    out.append(e)
                    print('DL_RC FAILS', json.dumps(e), flush=True)
    json.dump(out, open(args[1], 'w'))
    print('# %d smaller profiles evaluated, %d with a DL_RC failure (m: %s)' % (tried, len(out), sorted(set(e['m'] for e in out))),
          flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
