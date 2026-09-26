#!/usr/bin/env python3
"""C4min on the instances of PR #36's attempts (attempts/k4_c4x_attempts.py, INSTANCES: the smallest profiles where
simpler potentials fail) and of PR #30's n = 5 GM4 profiles (results/k4_c4min_hunt_seeds_gm4.json): f*, sigma, d*,
the number of min-frozen pre-allocations and of those with deficit <= 0, by k4/c4min_hunt.c -1 and by the brute force
k4/c4min_brute.py (n <= 4). The INSTANCES list is read from attempts/k4_c4x_attempts.py (PR #36)."""
import ast, json, os, subprocess
import c4min_common as cc
import c4min_brute


def instances():
    src = open(os.path.join(cc.ROOT, 'attempts', 'k4_c4x_attempts.py')).read()
    tree = ast.parse(src)
    for node in tree.body:
        if isinstance(node, ast.Assign) and getattr(node.targets[0], 'id', '') == 'INSTANCES':
            return ast.literal_eval(node.value)


def main():
    seen = set()
    rows = [(f'{i[0]}: {i[1]}', i[2], i[3]) for i in instances()]
    rows += [(s['source'], s['sets'], [tuple(v) for v in s['vals']]) for s in json.load(open(os.path.join(cc.ROOT, 'results', 'k4_c4min_hunt_seeds_gm4.json')))]
    for name, sets, values in rows:
        key = json.dumps([sets, values])
        if key in seen: continue
        seen.add(key)
        m = 1 + max(max(S) for S in sets)
        vals = [dict(zip(S, v)) for S, v in zip(sets, values)]
        h = cc.hunt_one(sets, m, vals)
        line = f'{name}: n {len(sets)} m {m} sigma {h["sigma"]} fstar {h["fstar"]} dstar {h["dstar"]} minfrozen {h["minfrozen"]} good {h["good"]}'
        if len(sets) <= 4:
            b = c4min_brute.brute(sets, vals, m)
            same = all(b[k] == h[k] for k in ('fstar', 'dstar', 'minfrozen', 'good'))
            line += f' | brute force {"agrees" if same else "DISAGREES " + json.dumps(b)}'
        print(line, flush=True)
    print(f'{len(seen)} distinct profiles')


if __name__ == '__main__':
    main()
