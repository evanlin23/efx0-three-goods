#!/usr/bin/env python3
"""Check of multi's claim (k4/oc1max_multi.md §17 at d10b8f20): on matching's 280 5_pure ROUND-RSD witnesses, 146 of
the 410 rounds use a chain that is not an E-prefix under any SD order of the round's start; (H) holds in all 410.
Own code: for each round, the current instance, every order giving its start, my E-prefixes; (H) of SD-E(round):
every agent outside K that wants a released head pick at the start values its good after the round above that pick."""
import itertools, json, gzip, sys
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, sd, mk
from round_rsd_ref import load_rows
from sphir_ref import e_prefixes

R = load_rows([sys.argv[2]]); W = json.load(gzip.open(sys.argv[1]))["witnesses"]; c = Counter()
for w in W:
    sets, vals, picks = R[w["k"]]; v0 = mk(sets, vals); n = len(v0); m = len(v0[0])
    S = [{y} for y in picks]; present = list(range(n)); goods = list(range(m))
    for rd in w["rounds"]:
        A = present; G = goods; gi = {g: i for i, g in enumerate(G)}; ai = {a: i for i, a in enumerate(A)}
        v = [[v0[a][g] for g in G] for a in A]; Y = [gi[next(iter(S[a]))] for a in A]
        orders = [o for o in itertools.permutations(range(len(A))) if sd(v, list(o)) == Y]
        chains = [[ai[a] for a in st["P"]] for st in rd["settled"]]
        def is_pref(P, o):
            E = e_prefixes(v, Y, list(o), P[0]); return len(P) >= 2 and len(E) >= len(P) - 1 and E[len(P) - 2] == P
        c["rounds"] += 1
        per_chain = all(any(is_pref(P, o) for o in orders) for P in chains)
        common = any(all(is_pref(P, o) for P in chains) for o in orders)
        c["round_all_chains_E_prefix_some_order_each"] += per_chain
        c["round_all_chains_E_prefix_one_common_order"] += common
        c["round_with_a_non_E_prefix_chain"] += not per_chain
        # (H)
        new = [set(s) for s in S]
        for st in rd["settled"]:
            P = st["P"]
            for i in range(1, len(P)):
                new[P[i]] = set(S[P[i - 1]])
            new[st["k"]] = set(st["T"])
        Ts = set(g for st in rd["settled"] for g in st["T"]); K = {st["k"] for st in rd["settled"]}
        released = [next(iter(S[st["P"][-1]])) for st in rd["settled"] if next(iter(S[st["P"][-1]])) not in Ts]
        H = all(not (v0[a][g] > val(v0, a, S[a])) or val(v0, a, new[a]) > v0[a][g] for a in present if a not in K for g in released)
        c["H_holds"] += H
        present = [a for a in present if a not in K]; goods = [g for g in goods if g not in Ts]; S = new
print(json.dumps(dict(source="multi's E-prefix claim on matching's 280 5_pure ROUND-RSD witnesses", **dict(sorted(c.items())))))
