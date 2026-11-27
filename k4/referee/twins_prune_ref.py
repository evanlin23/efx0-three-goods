#!/usr/bin/env python3
"""Referee spot check of K4.MC8's candidate filter and its Γ′-level prune (k4/TWINS.md §1 on proof/k4-twins at
450a58f; twins_filter.excluded / gamma_prune). Own code, written from TWINS.md's table and definitions; twins_filter.py
was read, not run or imported. Candidate lists are read as data.

Core-level predicate (mine): agents e != f sharing at least two goods of degree 2 (a double edge); kinds from the core
(P3, Q3, P4, Q4 by number of goods and private goods); c = number of further common goods; excluded iff the unordered
kind pair and c are certified in TWINS.md's table: {Q3,Q3}, {Q3,P4}, {P4,P4} with c in {0, 1}; {Q3,Q4}, {P4,Q4} with
c = 1.
Γ′ level (mine): G′ = each agent's shared goods (degree >= 2). Prune G′ iff EVERY completion (each G′-degree-3 agent
given 0 or 1 private good, G′-degree-4 agents none, G′-degree-2 agents one or two) is excluded by the core predicate;
also record whether SOME completion is excluded, and compare with the rule stated in gamma_prune's docstring
((3,3) any closure, or (3,4) sharing a third good).
  cores : counts on the beta = 4 core list (expect 2,392 excluded of 5,558) and on the hunt session's beta = 5, n = 6
          list (expect 9,455 excluded of 30,337, 20,882 left).
  gamma : on the G′ of every core of those lists: all-or-none over completions, and agreement with the stated rule.
"""
import gzip, json, sys, itertools
from collections import Counter

CERT = {(frozenset({'Q3'}), 0), (frozenset({'Q3'}), 1), (frozenset({'Q3', 'P4'}), 0), (frozenset({'Q3', 'P4'}), 1),
        (frozenset({'P4'}), 0), (frozenset({'P4'}), 1), (frozenset({'Q3', 'Q4'}), 1), (frozenset({'P4', 'Q4'}), 1)}

def degs(sets):
    return Counter(g for S in sets for g in S)

def kind(S, deg):
    p = sum(1 for g in S if deg[g] == 1)
    return {(3, 1): 'P3', (3, 0): 'Q3', (4, 1): 'P4', (4, 0): 'Q4'}.get((len(S), p), 'other')

def excluded_core(sets):
    deg = degs(sets)
    for i, j in itertools.combinations(range(len(sets)), 2):
        sh = set(sets[i]) & set(sets[j])
        if sum(1 for g in sh if deg[g] == 2) >= 2:
            if (frozenset({kind(sets[i], deg), kind(sets[j], deg)}), len(sh) - 2) in CERT:
                return True
    return False

def gprime(sets):
    deg = degs(sets)
    return [sorted(g for g in S if deg[g] >= 2) for S in sets]

def completions(nb):
    m0 = 1 + max((g for N in nb for g in N), default=-1)
    opts = []
    for N in nb:
        d = len(N)
        opts.append({2: [1, 2], 3: [0, 1], 4: [0]}.get(d, [0]))
    for choice in itertools.product(*opts):
        sets = []; nxt = m0
        for N, k in zip(nb, choice):
            sets.append(list(N) + list(range(nxt, nxt + k))); nxt += k
        yield sets

def stated_rule(nb):
    deg = degs(nb)
    for i, j in itertools.combinations(range(len(nb)), 2):
        di, dj = sorted((len(nb[i]), len(nb[j])))
        sh = set(nb[i]) & set(nb[j])
        if sum(1 for g in sh if deg[g] == 2) < 2:
            continue
        if (di, dj) == (3, 3) or ((di, dj) == (3, 4) and len(sh) >= 3):
            return True
    return False

def load(path):
    d = json.load(gzip.open(path))
    recs = d if isinstance(d, list) else d.get("cores", d.get("candidates", d.get("records", [])))
    return [r["sets"] for r in recs]

def main(paths):
    for path in paths:
        S = load(path)
        c = Counter(cores=len(S))
        seen = set()
        for sets in S:
            ex = excluded_core(sets); c["excluded"] += ex
            nb = gprime(sets); key = json.dumps(nb)
            if key in seen:
                continue
            seen.add(key)
            comp = [excluded_core(x) for x in completions(nb)]
            c["distinct_Gprime"] += 1
            allx, anyx = all(comp), any(comp)
            c["Gprime_all_completions_excluded"] += allx
            c["Gprime_mixed_completions"] += (anyx and not allx)
            sr = stated_rule(nb)
            c["stated_rule_prunes"] += sr
            c["stated_rule_MISMATCH_with_all_completions"] += (sr != allx)
        c["left"] = c["cores"] - c["excluded"]
        print(json.dumps(dict(source=path.rsplit('/', 1)[-1], **dict(sorted(c.items())))))

if __name__ == "__main__":
    main(sys.argv[1:])
