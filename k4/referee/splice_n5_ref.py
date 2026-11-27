#!/usr/bin/env python3
"""Referee check of Lemma SPLICE's data claims at n = 5 (kgen/rounds.md §4.10 at 7ffbfd2e) and of
K4.MULTI.RECS.EXIST.N5 (no REC-S repair at 7 of the 280 stored OC1^max-failing starts of the certifier's 5_pure chunk:
#773, #963, #38, #419, #447, #813, #1073). Data: oc1_fails of results/k4_oc1max/n5/5_pure_s5o0_summary.jsonl.gz on
compute/k4-oc1max-cert, read as data. Own code (splice_ref.recs_configs = E(k) with an improving pool pair T, SD-E,
every relaxed Theorem S case, final allocation raw EFX0; splice_ex_ref.ex_pred; splice_ref.round_witness)."""
import itertools, json, gzip, sys
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import sd, mk
from splice_ref import round_witness, recs_configs
from splice_ex_ref import ex_pred

def one(args):
    idx, sets, vals, picks = args
    v = mk(sets, vals); n = len(v)
    orders = [list(o) for o in itertools.permutations(range(n)) if sd(v, list(o)) == list(picks)]
    c = Counter(orders=len(orders))
    for sigma, k, E, T, P2, H0, X in recs_configs(v, picks, orders):
        c["configs"] += 1
        w = round_witness(v, picks, X, "RNDOZ"); ex, form = ex_pred(v, picks, X, k, E, T, P2)
        c["RNDOZ_witness"] += w; c["EX"] += ex; c["mismatch"] += (ex == w)
        c["u0_keeps_own_pick"] += picks[P2[0]] in X[P2[0]]
    return idx, picks, c

def main(path, procs):
    rows = []
    for line in gzip.open(path, "rt"):
        d = json.loads(line)
        for s in d.get("oc1_fails", []):
            rows.append((d["idx"], d["sets"], s["vals"], s["picks"]))
    tot = Counter(); none = []
    with Pool(procs) as pool:
        for idx, picks, c in pool.imap_unordered(one, rows, chunksize=4):
            tot.update(c); tot["starts"] += 1
            if c["configs"] == 0:
                none.append((idx, picks))
    print(json.dumps(dict(source="SPLICE / REC-S existence on the 280 n = 5 5_pure OC1-failing starts", **dict(sorted(tot.items())))))
    print("starts with NO REC-S configuration:", len(none), sorted(none))

if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]))
