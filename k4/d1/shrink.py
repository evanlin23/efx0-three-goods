"""Shrink a counterexample to the canonical form of Finding D1 (k4/d1.md §5): keep a one-absorber-hard start with
D = {k} at which no canonical chain from k, with any minimal improving H0, leaves an S* completion owned by k.
Greedy: drop a good from a set, drop a good entirely, or lower a value (values kept positive), as long as the property
holds for some order.  Then report the instance with values renormalised to ranks where possible.

    python3 k4/d1/shrink.py '<json [sets, vals]>'
"""
import sys, os, json, itertools, random
STRICT = os.environ.get("STRICT", "1") == "1"
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from d1lib import (Inst, sd_picks, Start, one_absorber, canonical_chains, pool, minimal_improving, apply_chain, sstar)


def bad_orders(sets, vals):
    used = sorted(set(g for s in sets for g in s)); rl = {g: i for i, g in enumerate(used)}
    sets = [[rl[g] for g in s] for s in sets]
    I = Inst(sets, vals, len(used)); out = []; seen = set()
    if any(len(s) == 0 or len(s) > 4 for s in sets): return []
    if STRICT and any(len(set(v)) < len(v) for v in vals): return []
    for od in itertools.permutations(range(I.n)):
        Y = sd_picks(I, od)
        if Y in seen: continue
        seen.add(Y); S = Start(I, Y)
        if len(S.D) != 1: continue
        k = S.D[0]; ch = canonical_chains(S, k)
        if not ch: continue
        if one_absorber(I, S.B): continue
        if any(sstar(I, apply_chain(S, p, H0), k) for p in ch for H0 in minimal_improving(S, k, pool(S, p))): continue
        out.append((od, Y))
    return out


def norm(sets, vals):
    used = sorted(set(g for s in sets for g in s)); rl = {g: i for i, g in enumerate(used)}
    return [[rl[g] for g in s] for s in sets], [list(v) for v in vals]


if __name__ == '__main__':
    sets, vals = json.loads(sys.argv[1]); sets, vals = norm(sets, vals)
    assert bad_orders(sets, vals), 'not a counterexample'
    changed = True; rng = random.Random(1)
    while changed:
        changed = False
        # drop a relevant good from one agent
        for i in range(len(sets)):
            for j in range(len(sets[i])):
                s2 = [list(s) for s in sets]; v2 = [list(v) for v in vals]
                s2[i].pop(j); v2[i].pop(j); s2, v2 = norm(s2, v2)
                if bad_orders(s2, v2): sets, vals, changed = s2, v2, True; break
            if changed: break
        if changed: continue
        # lower values
        for i in range(len(vals)):
            for j in range(len(vals[i])):
                for d in (vals[i][j] - 1, vals[i][j] // 2):
                    if d < 1 or d == vals[i][j]: continue
                    v2 = [list(v) for v in vals]; v2[i][j] = d
                    if bad_orders(sets, v2): vals, changed = v2, True; break
                if changed: break
            if changed: break
    print(json.dumps((sets, vals)), 'm', 1 + max(max(s) for s in sets), 'orders', bad_orders(sets, vals))
