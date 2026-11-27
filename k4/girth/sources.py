"""Instance sources for k4/girth (degree <= 4 instances, mostly with short cycles).

    cores(n, pure=None)     the certified k = 4 cores of results/k4_certs_{n}*.json.gz (hypergraphs only)
    profiles(sets, m)       the strict balanced type domains of k4/check4.py (core_domains), one dict per type
    screen()                k4/de4/ss_screen.py's screen set (A131, B131, C127, D3, GM4-*, suite instances n<=5)
    suite()                 every k4/suite/instances/*.json with values
"""
import glob
import gzip
import json
import os
import sys
from functools import lru_cache

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from lss import Inst


def cores(n, pure=None):
    out = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'results', 'k4_certs_%d*.json.gz' % n))):
        if 'ties' in f:
            continue
        d = json.load(gzip.open(f))
        if pure is not None and d.get('pure') != pure:
            continue
        for c in d['cores']:
            out.append((os.path.basename(f), c['idx'], c['sets'], c['m']))
    return out


@lru_cache(maxsize=None)
def _types(d):
    sys.path.insert(0, os.path.join(ROOT, 'k4'))
    from check4 import strict_balanced_types
    return tuple(tuple(v) for v in strict_balanced_types(d))


def domains(sets, m):
    """per agent, the list of value dicts of its strict balanced types (PP4: p + q < s + t), as k4/check4.py"""
    deg = [sum(g in S for S in sets) for g in range(m)]
    doms = []
    for S in sets:
        priv = [g for g in S if deg[g] == 1]
        dom = []
        for v in _types(len(S)):
            vals = dict(zip(S, v))
            if len(priv) == 2 and vals[priv[0]] + vals[priv[1]] >= sum(v) - vals[priv[0]] - vals[priv[1]]:
                continue
            dom.append(vals)
        doms.append(dom)
    return doms


def screen():
    cwd = os.getcwd()
    de4 = os.path.join(ROOT, 'k4', 'de4')
    sys.path.insert(0, de4)
    os.chdir(de4)
    try:
        from ss_screen import screen_set
        S = screen_set()
    finally:
        os.chdir(cwd)
    return [(name, Inst(J.sets, [[J.v[i][g] for g in J.sets[i]] for i in range(J.n)], J.m)) for name, J in S]


def suite():
    out = []
    for f in sorted(glob.glob(os.path.join(ROOT, 'k4/suite/instances/*.json'))):
        d = json.load(open(f))
        if d.get('vals') and d.get('sets'):
            m = d.get('m') or 1 + max(max(s) for s in d['sets'])
            out.append((d.get('id'), Inst(d['sets'], d['vals'], m)))
    return out
