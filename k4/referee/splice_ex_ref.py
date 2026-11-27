#!/usr/bin/env python3
"""Referee check of Lemma SPLICE (kgen/rounds.md §4.10 at 7ffbfd2e): a REC-S repair's allocation X is a one-round
OC1' witness (RNDOZ) unless (EX). Own code (splice_ref.round_witness, rec_s_ref helpers). (EX) as stated: q = the agent
holding no pick in X (k when Y_z ∉ T; u0 when W contains no pick); (EX) iff Y_q lies with an agent v that keeps its own
pick and v_v(X_v - {Y_v}) <= v_v(Y_v). Forms: EX-a (u0 = z, Y_z ∉ T, u_s = x_1), EX-b (Y_z ∉ T, u_s = x_1, h = Y_k to
a w keeping its pick), EX-c (Y_z ∈ T, u0 = x_l, u_s = x_{l+1}, h = Y_{x_l} to a w keeping its pick).
Tests: (EX) ⟺ X is not a RNDOZ witness, on every REC-S configuration of random strict perfect starts and of the n = 4
export; and the note's constructed instance."""
import itertools, json, gzip, sys
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, sd, mk
from splice_ref import round_witness, recs_configs, rand_starts, load_export

def ex_pred(v, Y, X, k, E, T, P2):
    n = len(Y); picks = set(Y)
    z = E[-1]; u0 = P2[0]
    holds = [X[a] & picks for a in range(n)]
    q = None
    if Y[z] not in T:
        q = k
    elif not holds[u0]:
        q = u0
    if q is None:
        return False, None
    vv = next(b for b in range(n) if Y[q] in X[b])
    keeps = Y[vv] in X[vv]
    ex = keeps and val(v, vv, X[vv] - {Y[vv]}) <= v[vv][Y[vv]]
    form = None
    if ex:
        if u0 == z and Y[z] not in T and P2[-1] == E[1]:
            form = "EX-a"
        elif Y[z] not in T and P2[-1] == E[1] and vv != u0:
            form = "EX-b"
        elif Y[z] in T and u0 in E and E.index(u0) + 1 < len(E) and P2[-1] == E[E.index(u0) + 1]:
            form = "EX-c"
        else:
            form = "other"
    return ex, form

def analyse(args):
    v, Y, orders = args
    c = Counter()
    for sigma, k, E, T, P2, H0, X in recs_configs(v, Y, orders):
        c["configs"] += 1
        wit = round_witness(v, Y, X, "RNDOZ")
        ex, form = ex_pred(v, Y, X, k, E, T, P2)
        c["witness"] += wit; c["EX"] += ex
        c["EX_and_witness_MISMATCH"] += ex and wit
        c["notwitness_and_not_EX_MISMATCH"] += (not ex) and (not wit)
        if ex:
            c["EX_form_" + form] += 1
    return c

def main(kind, a, b, procs):
    it = load_export(a) if kind == "export" else rand_starts(int(a), int(b))
    c = Counter()
    with Pool(procs) as pool:
        for cc in pool.imap_unordered(analyse, it, chunksize=50):
            c.update(cc); c["starts"] += 1
    print(json.dumps(dict(source=f"Lemma SPLICE (EX) check on {kind} {a.rsplit('/', 1)[-1]} {b}", **dict(sorted(c.items())))))

def constructed():
    rows = [[0, 2289, 1831, 2530, 0, 1934, 0], [0, 836, 0, 2963, 0, 2033, 642], [0, 1387, 1223, 2254, 0, 0, 1149],
            [1362, 0, 271, 0, 72, 1386, 0]]
    Y = sd(rows, [2, 0, 3, 1])
    found = []
    for sigma, k, E, T, P2, H0, X in recs_configs(rows, Y, [[2, 0, 3, 1]]):
        ex, form = ex_pred(rows, Y, X, k, E, T, P2)
        found.append(dict(k=k, E=E, T=sorted(T), P2=P2, X=[sorted(x) for x in X], RNDOZ=round_witness(rows, Y, X, "RNDOZ"),
                          RNDPZ=round_witness(rows, Y, X, "RNDPZ"), EX=ex, form=form))
    print(json.dumps(dict(constructed_instance_picks=Y, configs=found)))

if __name__ == "__main__":
    if sys.argv[1] == "constructed":
        constructed()
    else:
        main(sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]))
