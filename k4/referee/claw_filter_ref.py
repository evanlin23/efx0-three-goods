#!/usr/bin/env python3
"""Referee spot check of K4.MC9's effect on the candidate lists (k4/TWINS.md §4 at ea71fb54; twins_filter.has_claw /
gamma_claw read, not run). Own core-level predicate: a claw is a good G valued by exactly three agents, each of kind
P3 (three relevant goods, exactly one of them private, i.e. of degree 1), G not private. Applied after my K4.MC8
predicate (twins_prune_ref.excluded_core). Counts on the beta = 4 core list (TWINS.md: 3,166 -> 2,079) and on the hunt
session's beta = 5, n = 6 list (20,882 -> 20,553); the n = 6 survivors are compared with twins' list
results/k4_twins/mc_n6_b5_mc9.json.gz as sets of cores (goods relabelled canonically per core is not attempted: the
lists share the hunt session's labelling)."""
import sys, json, gzip
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from twins_prune_ref import degs, kind, excluded_core, load

def has_claw(sets):
    deg = degs(sets)
    for G, d in deg.items():
        if d != 3:
            continue
        vs = [S for S in sets if G in S]
        if all(kind(S, deg) == 'P3' for S in vs):
            return True
    return False

def main(paths, compare=None):
    for p in paths:
        cores = load(p); c = Counter(cores=len(cores)); left = []
        for s in cores:
            if excluded_core(s):
                c["excluded_MC8"] += 1; continue
            c["after_MC8"] += 1
            if has_claw(s):
                c["excluded_MC9_claw"] += 1; continue
            c["after_MC9"] += 1; left.append(s)
        out = dict(source=f"K4.MC9 claw filter on {p.rsplit('/', 1)[-1]}", **dict(sorted(c.items())))
        if compare and "n6" in p:
            theirs = load(compare)
            A = {json.dumps(sorted(map(sorted, s))) for s in left}; B = {json.dumps(sorted(map(sorted, s))) for s in theirs}
            out.update(theirs=len(theirs), same_set_of_cores=A == B, mine_not_theirs=len(A - B), theirs_not_mine=len(B - A))
        print(json.dumps(out))

if __name__ == "__main__":
    main(sys.argv[1].split(","), sys.argv[2] if len(sys.argv) > 2 else None)
