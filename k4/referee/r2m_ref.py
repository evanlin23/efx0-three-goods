#!/usr/bin/env python3
"""Referee replay of the certifier's refutation of TTC's R2-M and R2* (k4/ttc.md §14.6 on claude/k4-ttc; failures
results/k4_oc1max/r2m_fails_n4.jsonl on main, commit c0de02c). Own code (cert_ref.py helpers: SD, one-absorber
completion, §29 moves, raw EFX0); nothing from k4/oc1cert/ or k4/sdc/ is run or imported.

Definitions (ttc.md §14.6): a perfect SD start Y of a strict connected k = 4 core; frozen = some other agent values
y_j above its own pick; receivers U = the others; D = frozen agents valuing a junk good; hard = no one-absorber
completion of the picks. A canonical chain is an official §29 chain (x_0, ..., x_t), t >= 1, with x_0 in D, x_1
valuing y_{x_0} above y_{x_1}, x_t in U (H_0 inside (J + B_{x_t}) ∩ R_{x_0} and improving; each x_i takes
B_{x_{i-1}} + H_i, H_i inside J ∩ R_{x_i}, gaining; H sets disjoint).
  R2-M: after some canonical chain, a complete raw-EFX0 allocation extending the bases in which nobody receives two
        or more junk goods and agents other than x_0 holding two or more base goods receive none (S^c(x_0), rest <= 1).
  R2*: the same with only "nobody receives two or more junk goods".
  R2 : the picks, or the bases after one official move (addition or chain), have a one-absorber completion.
Per start: core conditions, perfect (some order gives the picks), |U| >= 2, hard; R2-M and R2* fail (no canonical
chain admits such a completion); R2 holds.
"""
import itertools, json, sys
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, complete, oc_depth, subsets, mk
from oc1p_ref import core_check

def canonical_chain_states(v, Y, D, U):
    n = len(Y); m = len(v[0]); B = [{y} for y in Y]; J = set(range(m)) - set(Y)
    R = [rel(v, i) for i in range(n)]
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            if seq[0] not in D or seq[-1] not in U or not v[seq[1]][Y[seq[0]]] > v[seq[1]][Y[seq[1]]]:
                continue
            def rec(i, used, nb):
                if i > t:
                    pool = ((J - used) | B[seq[-1]]) & R[seq[0]]
                    for H0 in subsets(pool):
                        if H0 and val(v, seq[0], H0) > val(v, seq[0], B[seq[0]]):
                            c = [set(b) for b in nb]; c[seq[0]] = set(H0); yield seq, c
                    return
                xi, pr = seq[i], seq[i - 1]
                for Hi in subsets((J - used) & R[xi]):
                    if val(v, xi, B[pr] | Hi) > val(v, xi, B[xi]):
                        c = [set(b) for b in nb]; c[xi] = B[pr] | Hi
                        yield from rec(i + 1, used | Hi, c)
            yield from rec(1, set(), [set(b) for b in B])

def constrained_completion(v, B, x0=None):
    """every agent receives <= 1 junk good; if x0 is given, agents other than x0 with >= 2 base goods receive none."""
    n = len(B); m = len(v[0]); Jp = sorted(set(range(m)) - set().union(*B))
    elig = [i for i in range(n) if x0 is None or i == x0 or len(B[i]) <= 1]
    for f in itertools.permutations(elig, len(Jp)) if len(Jp) <= len(elig) else []:
        X = [set(b) for b in B]
        for g, a in zip(Jp, f):
            X[a].add(g)
        if efx0(v, X):
            return X
    return None

def replay(d):
    sets, vals, Y = d["sets"], d["vals"], d["picks"]
    v = mk(sets, vals); n = len(v); m = len(v[0])
    agents, conn, allrel = core_check(v)
    core = conn and allrel and all(a["balanced_privates_ok"] and a["strict"] for a in agents.values())
    perfect_orders = sum(1 for o in itertools.permutations(range(n)) if sd(v, list(o)) == list(Y))
    B = [{y} for y in Y]; J = set(range(m)) - set(Y)
    p = [v[i][Y[i]] for i in range(n)]
    F = {j for j in range(n) if any(i != j and v[i][Y[j]] > p[i] for i in range(n))}
    U = [i for i in range(n) if i not in F]
    D = {j for j in F if any(v[j][g] > 0 for g in J)}
    hard = complete(v, B) is None
    chains = list(canonical_chain_states(v, Y, D, U))
    r2m = any(constrained_completion(v, c, seq[0]) is not None for seq, c in chains)
    r2s = any(constrained_completion(v, c) is not None for seq, c in chains)
    r2 = oc_depth(v, Y, 1) is not None
    return dict(core=core, perfect_orders=perfect_orders, receivers=U, hard=hard, canonical_chain_states=len(chains),
                R2M_holds=r2m, R2star_holds=r2s, R2_holds=r2)

def main(path):
    c = Counter(); hg = set(); bad = []
    for line in open(path):
        d = json.loads(line)
        r = replay(d); c["starts"] += 1; hg.add(json.dumps(d["sets"]))
        c["core"] += r["core"]; c["perfect"] += r["perfect_orders"] > 0; c["two_or_more_receivers"] += len(r["receivers"]) >= 2
        c["hard"] += r["hard"]; c["R2M_fails"] += not r["R2M_holds"]; c["R2star_fails"] += not r["R2star_holds"]
        c["R2_holds"] += r["R2_holds"]
        ok = r["core"] and r["perfect_orders"] > 0 and len(r["receivers"]) >= 2 and r["hard"] and not r["R2M_holds"] and r["R2_holds"]
        if not ok:
            bad.append((d, r))
        if c["starts"] <= 5:
            print(json.dumps(dict(start=c["starts"], sets=d["sets"], vals=d["vals"], picks=d["picks"], **r)))
    print(json.dumps(dict(source="R2-M / R2* refutation replay", distinct_hypergraphs=len(hg), **dict(sorted(c.items())))))
    for b in bad[:5]:
        print("NOT REPLAYED", b)

if __name__ == "__main__":
    main(sys.argv[1])
