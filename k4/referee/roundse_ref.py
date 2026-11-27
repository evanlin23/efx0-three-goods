#!/usr/bin/env python3
"""Referee re-validation of K4.MULTI.ROUNDE.SEL2 (proof/k4-oc1max-multi-2 at 4f8a9922): the 583,680 E-prefix round
witnesses (results/k4_oc1max_multi/round_e_sel2_witnesses.json.gz) against the certifier's export
(results/k4_oc1max/n5/two_move_starts_n5_sel2.json.gz on compute/k4-oc1max-cert). Own code (cert_ref, oc1hall_ref,
rsd_ref helpers); check_rounds.py was read, not run or imported.

Per start, from the definitions of k4/oc1max_multi.md §17: the picks are SD of the witness order; per round at the
current state (present agents A, remaining goods G; one good each): every settled k is frozen among A and values a
junk good; its chain P (length >= 2) is a prefix of k's earliest-wanter chain under the order restricted to A (the
chain stops when the earliest wanter is already on it); chains vertex-disjoint; T ⊆ (J ∪ S_head) ∩ R_k, improving,
disjoint; the stored state is all of them applied at once; (H); the reduced state is SD of the order restricted to
A - K on G - ∪T; (L*) at the round's end for every agent of A; (P2) new T's vs earlier settled agents at their τ; (P3)
released head picks worth <= τ to every settled agent. Final: a partition, settled agents hold exactly T, present
agents keep their good and add junk only, at most one absorber, raw EFX0. Plus: the witness starts equal the export's
starts as a multiset, and the picks of each witness start are the export's."""
import json, gzip, sys, itertools, hashlib
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk
from oc1hall_ref import threatened
from rsd_ref import sd_sub

def e_chain(v, S, A, order, k, c):
    pos = {a: i for i, a in enumerate(order)}; E = [k]
    while True:
        last = E[-1]
        if len(S[last]) != 1:
            break
        (g,) = S[last]
        W = [i for i in A if i != last and v[i][g] > val(v, i, S[i])]
        if not W:
            break
        nxt = min(W, key=lambda i: pos[i])
        if nxt in E:
            c["E_chain_hits_a_cycle"] += 1; break
        E.append(nxt)
    return E

def check(st):
    c = Counter(); w = st["witness"]
    v = mk(st["sets"], st["vals"]); n = len(v); m = len(v[0]); order = w["order"]
    def fail(tag):
        c["FAIL_" + tag] += 1; return c
    if sorted(order) != list(range(n)) or sd(v, order) != list(st["picks"]):
        return fail("picks")
    S = [{y} for y in st["picks"]]; A = set(range(n)); G = set(range(m)); tau = {}
    for rd in w["rounds"]:
        J = G - set().union(*(S[a] for a in A))
        new = [set(s) for s in S]; usedA = set(); usedT = set(); K = []; released = []
        for s in rd["settled"]:
            k, P, T = s["k"], list(s["P"]), set(s["T"])
            if k not in A or len(S[k]) != 1:
                return fail("k")
            (g,) = S[k]
            if not any(i != k and v[i][g] > val(v, i, S[i]) for i in A) or not any(v[k][h] > 0 for h in J):
                return fail("k_not_dangerous")
            E = e_chain(v, S, A, order, k, c)
            if len(P) < 2 or P != E[:len(P)]:
                return fail("not_E_prefix")
            if usedA & set(P) or usedT & T:
                return fail("not_disjoint")
            z = P[-1]
            if not T or not T <= (J | S[z]) & rel(v, k) or not val(v, k, T) > val(v, k, S[k]):
                return fail("T")
            usedA |= set(P); usedT |= T; K.append(k)
            for i in range(1, len(P)):
                new[P[i]] = set(S[P[i - 1]])
                if not val(v, P[i], new[P[i]]) > val(v, P[i], S[P[i]]):
                    return fail("chain_gain")
            new[k] = set(T)
            (hz,) = S[z]
            if hz not in T:
                released.append(hz)
        if any(sorted(new[a]) != sorted(rd["state"][a]) for a in range(n)):
            return fail("state")
        rest = A - set(K)
        if any(v[a][y] > val(v, a, S[a]) and v[a][y] > val(v, a, new[a]) for a in rest for y in released):
            return fail("H")
        G2 = G - usedT
        if any(len(new[a]) != 1 for a in rest):
            return fail("not_single")
        sig = [a for a in order if a in rest]
        Ym = sd_sub(v, sig, rest, G2)
        if any(Ym[a] != next(iter(new[a])) for a in rest):
            return fail("SDE_round")
        for s in rd["settled"]:
            T = set(s["T"])
            if any(threatened(v, a, T, val(v, a, new[a])) for a in A if a != s["k"]):
                return fail("Lstar")
            if any(threatened(v, f, T, tf) for f, tf in tau.items()):
                return fail("P2")
        for k in K:
            tau[k] = val(v, k, new[k])
        if any(v[f][y] > tf for y in released for f, tf in tau.items()):
            return fail("P3")
        c[f"round_size_{len(K)}"] += 1
        A = rest; G = G2; S = new
    X = [set(x) for x in w["alloc"]]
    if sum(map(len, X)) != m or set().union(*X) != set(range(m)):
        return fail("partition")
    J = G - set().union(*(S[a] for a in A))
    if any(X[f] != S[f] for f in tau):
        return fail("settled_bundle")
    if any(not S[a] <= X[a] or not (X[a] - S[a]) <= J for a in A):
        return fail("extends")
    if sum(1 for a in A if len(X[a] - S[a]) >= 2) > 1:
        return fail("absorbers")
    if not efx0(v, X):
        return fail("EFX0")
    c["valid"] += 1; c[f"rounds_{len(w['rounds'])}_" + "_".join(str(len(r['settled'])) for r in w["rounds"])] += 1
    return c

def main(witpath, exportpath, procs):
    d = json.load(gzip.open(witpath)); W = d["starts"]
    e = json.load(gzip.open(exportpath))
    key = lambda a, b, cc: json.dumps([a, b, list(cc)])
    EX = Counter(key(H["sets"], s["vals"], s["picks"]) for H in e["hypergraphs"] for s in H["starts"])
    WI = Counter(key(s["sets"], s["vals"], s["picks"]) for s in W)
    c = Counter(witnesses=len(W), export_starts=sum(EX.values()), export_minus_witness=sum((EX - WI).values()),
                witness_minus_export=sum((WI - EX).values()), no_witness=sum(1 for s in W if s.get("witness") is None))
    del e, EX, WI
    for s in W:                       # single process: the witness file is large (forked workers ran out of memory)
        if s.get("witness"):
            c.update(check(s))
    print(json.dumps(dict(source="K4.MULTI.ROUNDE.SEL2 witnesses re-validated",
                          witness_sha256=hashlib.sha256(open(witpath, 'rb').read()).hexdigest()[:16],
                          export_sha256=hashlib.sha256(open(exportpath, 'rb').read()).hexdigest()[:16], **dict(sorted(c.items())))))

if __name__ == "__main__" and sys.argv[1] != "mut":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]))

def mutants(st):
    import copy
    w = st["witness"]
    a = copy.deepcopy(st); a["witness"]["order"] = w["order"][::-1]; yield "order_reversed", a
    a = copy.deepcopy(st); s0 = a["witness"]["rounds"][0]["settled"][0]; s0["T"] = s0["T"][:1]; yield "T_cut", a
    a = copy.deepcopy(st); X = a["witness"]["alloc"]; k = w["rounds"][0]["settled"][0]["k"]
    j = next(i for i in range(len(X)) if i != k and len(X[i]) >= 2) if any(i != k and len(X[i]) >= 2 for i in range(len(X))) else None
    if j is not None:
        X[k] = X[k] + [X[j][-1]]; X[j] = X[j][:-1]; yield "settled_agent_gets_a_good", a
    a = copy.deepcopy(st); X = a["witness"]["alloc"]; X[0], X[1] = X[1], X[0]; yield "bundles_0_1_swapped", a
    a = copy.deepcopy(st); s0 = a["witness"]["rounds"][0]["settled"][0]
    if len(s0["P"]) >= 2:
        s0["P"] = s0["P"][:1] + [x for x in range(len(st["sets"])) if x not in s0["P"]][:1]; yield "chain_head_replaced", a

def main_mut(witpath, step):
    d = json.load(gzip.open(witpath)); c = Counter()
    for t, st in enumerate(d["starts"]):
        if t % step:
            continue
        for name, a in mutants(st):
            r = check(a); c[name + "_tests"] += 1; c[name + "_ACCEPTED"] += r["valid"]
    print(json.dumps(dict(source=f"ROUNDE.SEL2 own mutants, every {step}th witness", **dict(sorted(c.items())))))

if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "mut":
    main_mut(sys.argv[2], int(sys.argv[3])); sys.exit()
