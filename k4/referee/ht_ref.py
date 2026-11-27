#!/usr/bin/env python3
"""Referee check (in passing) of Proposition HT (k4/girth.md at 90c116f): for t >= 2 the hypergraph of H_t
(k4/c4.md §7, rebuilt from its text here) is linear and agent l lies on no Berge 3-cycle; for t = 1, l lies on one.
Also runs LSS (k4/referee/girth_ref.py, written from LSS's text) with vertex 0 = l on random additive and monotone
profiles of H_t, raw EFX0 at the end."""
import sys, random, json, itertools
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import girth_ref as G

def ht(t):
    goods = {}
    def g(name):
        if name not in goods:
            goods[name] = len(goods)
        return goods[name]
    R = []
    R.append({g(("g", 1)), g("z"), g("u"), g("u'")})            # l
    for j in range(1, t + 1):
        for i in range(1, 4):
            R.append({g(("a", j, i)), g(("b", j, i)), g(("c", j, i)), g(("g", j))})
        e = ("g", j + 1) if j < t else "z"
        R.append({g(("a", j, 1)), g(("a", j, 2)), g(("a", j, 3)), g(e)})
    return [frozenset(r) for r in R], len(goods)

out = []
for t in range(1, 7):
    R, m = ht(t)
    n = len(R)
    inst = G.Inst(n, R, None); inst.m = m
    lin = G.linear(inst); l3 = G.on_3cycle(inst, 0)
    rng = random.Random(t); fails = 0; runs = 0
    if lin and not l3:
        for rep in range(40):
            f = G.additive(n, R, rng) if rep % 2 == 0 else G.monotone(n, R, rng)
            I = G.Inst(n, R, f); I.m = m
            r, X = G.lss(I, 0, rng); runs += 1
            if r:
                fails += 1
    out.append(dict(t=t, n=n, m=m, linear=lin, l_on_3cycle=l3, lss_runs=runs, lss_fail=fails))
    print(json.dumps(out[-1]))
