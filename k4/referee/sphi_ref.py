#!/usr/bin/env python3
"""Referee check of Theorem S^φ (K4.MULTI.SPHI; k4/oc1max_multi.md §16 on proof/k4-oc1max-multi-2 at 52f5b0b6).
Own code (rec_s_ref / cert_ref helpers); nothing from k4/oc1max_multi/ is run. Data read as data.

Settle-delete-recurse with at most two settlements, for every order giving the picks: at level l, every dangerous k,
its earliest-wanter chain E(k) whose head is not phantom-frozen (the §14 fix), every improving pool pair T that
threatens no existing phantom ((P2)), SD-E checked; (P1) and (P3) asserted at every level. At the last level every
Theorem S case (relaxed, longest chain) of the current instance: hypotheses (S-φ1) W threatens no phantom,
(S-φ2) v_φ(B'_r) <= τ_φ, and the head condition (h = Y_z ⟹ v_φ(Y_z) <= τ_φ); the full allocation of I₀ (phantoms
keep T_φ) tested by raw EFX₀. Counted: hypotheses without EFX₀ (must be 0: the theorem), EFX₀ without hypotheses, and
cases with (S-φ1) and (S-φ2) but not the head condition.
"""
import itertools, json, gzip, sys
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk
from multi_ref import frozen_set
from oc1hall_ref import threatened
from rec_s_ref import earliest_wanter_chain, reduce_inst, theorem_s_cases

def levels(v0, A, G, v, Y, sigma, phantoms, depth, c, out):
    """A: I0 indices of the current agents; G: I0 indices of the current goods; v, Y, sigma in current indices."""
    n = len(Y); m = len(v[0])
    # invariants
    for (pa, T, tau) in phantoms:
        for i in range(n):
            if any(v0[A[i]][g] >= val(v0, A[i], {G[Y[i]]}) and v0[A[i]][g] > 0 for g in T):
                c["P1_FAIL"] += 1
        J = set(range(m)) - set(Y)
        if any(v0[pa][G[g]] > tau for g in J):
            c["P3_FAIL"] += 1
    if phantoms:
        yield (A, G, v, Y, phantoms)
    if depth == 0:
        return
    B = [{y} for y in Y]; J = set(range(m)) - set(Y)
    F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
    for k in sorted(D):
        E = earliest_wanter_chain(v, list(Y), list(sigma), k)
        if E is None or E == "CYCLE":
            continue
        z = E[-1]
        if any(v0[pa][G[Y[z]]] > tau for pa, T, tau in phantoms):
            c["head_phantom_frozen_skipped"] += 1
            continue
        pool = J | {Y[z]}
        for T in itertools.combinations(sorted(pool & rel(v, k)), 2):
            T = set(T)
            if not val(v, k, T) > v[k][Y[k]]:
                continue
            TI = {G[g] for g in T}
            if any(threatened(v0, pa, TI, tau) for pa, _, tau in phantoms):
                c["P2_skipped"] += 1
                continue
            agents, goods, vm, Ym, B1 = reduce_inst(v, list(Y), E, T)
            sig = [agents.index(a) for a in sigma if a != k]
            if [sd(vm, sig)[i] for i in range(len(agents))] != list(Ym):
                c["SDE_FAIL"] += 1; continue
            yield from levels(v0, [A[a] for a in agents], [G[g] for g in goods], vm, Ym, sig,
                              phantoms + [(A[k], TI, val(v0, A[k], TI))], depth - 1, c, out)

EX = [None]

def check_start(args):
    v0, Y0, orders = args
    c = Counter(); EX[0] = None
    n0 = len(Y0); m0 = len(v0[0])
    for sigma in orders:
        for (A, G, v, Y, phantoms) in levels(v0, list(range(n0)), list(range(m0)), v0, list(Y0), list(sigma), [], 2, c, None):
            c[f"states_with_{len(phantoms)}_phantoms"] += 1
            for kq, sq, h, H0, r, Am in theorem_s_cases(v, Y):
                X = [set() for _ in range(n0)]
                for i, a in enumerate(A):
                    X[a] = {G[g] for g in Am[i]}
                for pa, T, tau in phantoms:
                    X[pa] = set(T)
                W = X[A[kq]]
                Br = {G[g] for g in Am[r]} - {G[h]}
                Sphi1 = not any(threatened(v0, pa, W, tau) for pa, _, tau in phantoms)
                Sphi2 = all(val(v0, pa, Br) <= tau for pa, _, tau in phantoms)
                z = sq[-1]
                headc = (h != Y[z]) or all(v0[pa][G[Y[z]]] <= tau for pa, _, tau in phantoms)
                hyp = Sphi1 and Sphi2 and headc
                ok = efx0(v0, X)
                tag = f"L{len(phantoms)}_"
                c[tag + "cases"] += 1; c[tag + "hyp"] += hyp; c[tag + "efx0"] += ok
                c[tag + "THEOREM_VIOLATION_hyp_not_efx0"] += hyp and not ok
                c[tag + "efx0_without_hyp"] += ok and not hyp
                c[tag + "S1_S2_but_not_head_condition"] += Sphi1 and Sphi2 and not headc
                c[tag + "S1_S2_not_head_and_not_efx0"] += Sphi1 and Sphi2 and not headc and not ok
                if Sphi1 and Sphi2 and not headc and not ok and EX[0] is None:
                    EX[0] = dict(v=v0, picks=list(Y0), order=list(sigma), phantoms=[(pa, sorted(T), tau) for pa, T, tau in phantoms],
                                 chain=[A[a] for a in sq], h=G[h], X=[sorted(x) for x in X])
    if EX[0] is not None:
        c["_ex_" + json.dumps(EX[0])] += 1
    return c

def load_export(path):
    d = json.load(gzip.open(path))
    for H in d["hypergraphs"]:
        for s in H["starts"]:
            v = mk(H["sets"], s["vals"]); Y = s["picks"]
            yield v, Y, [o for o in itertools.permutations(range(len(Y))) if sd(v, list(o)) == list(Y)]

def load_jsonl(path):
    f = gzip.open(path, "rt") if path.endswith(".gz") else open(path)
    for line in f:
        d = json.loads(line); n = len(d["sets"]); m = 1 + max(g for s in d["sets"] for g in s)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(d["sets"][i], d["vals"][i]):
                v[i][g] = x
        Y = sd(v, d["order"])
        yield v, Y, [o for o in itertools.permutations(range(n)) if sd(v, list(o)) == list(Y)]

def rand_starts(N, seed):
    import random
    rng = random.Random(seed)
    for _ in range(N):
        n = rng.randint(5, 6); m = rng.randint(n + 2, n + 4)
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            for g, x in zip(rng.sample(range(m), rng.choice([3, 4, 4])), rng.sample(range(1, 40), 4)):
                v[i][g] = x
        o = list(range(n)); rng.shuffle(o)
        Y = sd(v, o)
        if None in Y:
            continue
        yield v, Y, [o]

def main(kind, path, procs):
    if kind == "rand":
        a, b = path.split(":")
        it = rand_starts(int(a), int(b))
    else:
        it = load_export(path) if kind == "export" else load_jsonl(path)
    c = Counter()
    with Pool(procs) as pool:
        for cc in pool.imap_unordered(check_start, it, chunksize=50):
            c.update(cc); c["starts"] += 1
    exs = [k[4:] for k in c if k.startswith("_ex_")]
    for k in list(c):
        if k.startswith("_ex_"):
            del c[k]
    print(json.dumps(dict(source=f"Theorem S^phi on {path.rsplit('/', 1)[-1]}", **dict(sorted(c.items())))))
    for e in sorted(exs, key=len)[:2]:
        print("EXAMPLE", e)

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]))
