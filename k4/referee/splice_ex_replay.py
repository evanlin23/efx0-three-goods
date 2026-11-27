#!/usr/bin/env python3
"""Replay, with my own code, the SPLICE exceptions that kgen-rounds' random logs print (EXCEPTION lines of
results/kgen_rounds/splice_search_random_*.log at 7ffbfd2e, read as data): for each, (i) the picks are the SD outcome of
the stated order; (ii) E(k) is my earliest-wanter chain; (iii) the stated X is a complete raw-EFX0 allocation and is one
of my REC-S configurations; (iv) X is not a RNDOZ / RNDPZ witness (my round_witness); (v) my (EX) predicate and form."""
import json, sys
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import efx0, sd, mk
from rec_s_ref import earliest_wanter_chain
from splice_ref import round_witness, recs_configs
from splice_ex_ref import ex_pred

c = Counter()
for line in open(sys.argv[1]):
    d = json.loads(line); r = d["repair"]
    v = mk(d["sets"], d["vals"]); Y = d["picks"]; m = len(v[0])
    X = [set(x) for x in r["X"]]; k = r["k"]; E = r["P1"]; T = set(r["T"]); P2 = r["P2"]
    c["exceptions"] += 1
    c["picks_are_SD_of_order"] += sd(v, r["order"]) == Y
    c["E_is_my_earliest_wanter_chain"] += earliest_wanter_chain(v, list(Y), r["order"], k) == E
    c["X_complete_partition"] += sum(map(len, X)) == m and set().union(*X) == set(range(m))
    c["X_raw_EFX0"] += efx0(v, X)
    c["X_among_my_RECS_configs"] += any(kk == k and EE == E and TT == T and PP == P2 and XX == X
                                        for _, kk, EE, TT, PP, _, XX in recs_configs(v, Y, [r["order"]]))
    c["RNDOZ_witness"] += round_witness(v, Y, X, "RNDOZ"); c["RNDPZ_witness"] += round_witness(v, Y, X, "RNDPZ")
    ex, form = ex_pred(v, Y, X, k, E, T, P2)
    c["my_EX"] += ex; c[f"form_{form}"] += 1
print(json.dumps(dict(source="replay of kgen-rounds' printed SPLICE exceptions", **dict(sorted(c.items())))))
