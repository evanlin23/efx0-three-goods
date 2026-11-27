#!/usr/bin/env python3
"""Referee check of Lemma SD-E and Theorem REC-S (K4.MULTI.SDE, K4.MULTI.RECS; k4/oc1max_multi.md §12, branch
proof/k4-oc1max-multi at 6c3fd95). Own code (oc1hall_ref / multi_ref / cert_ref / theorem_s_ref helpers), raw EFX0;
nothing from k4/oc1max_multi/ is run or imported. The failure files of that branch are read as data only.

SD-E: at the SD outcome Y of sigma (strict values), every frozen k, the earliest-wanter chain E(k) (x_l the
  sigma-earliest wanter of Y_{x_{l-1}} at the picks, up to an unwanted head z), every T ⊆ J ∪ {Y_z}: the state after
  E(k) with k taking T, restricted to I- (k and T deleted), equals SD(sigma - k) in I-.
  Mutations: 'anychain' (any canonical chain from k instead of E(k)); 'ties' (values with ties, SD tie-break by
  lowest good index).
REC-S: at perfect strict starts, every k in D, every improving pair T ⊆ (J ∪ {Y_z}) ∩ R_k for E(k):
  (L) checked (it should always hold here); in I- at B1-: every (k', longest canonical P', h in J- ∪ {Y_z'}) meeting
  Theorem S's relaxed hypotheses, every improving H0' ⊆ W' ∩ R_k', every receiver (z' if unfrozen after P', else
  every wanter of a'); (K) checked; if (K) holds, the composed repair is validated in I: move 1 (E(k), k takes T) and
  move 2 (P', k' takes H0') simulated as official moves (cert_ref.apply_move), completion one-absorber, a partition,
  raw EFX0.
  Mutations: 'noK' (drop (K)); 'anychain' (any canonical chain from k for P1, B1- not required to be an SD start).
"""
import itertools, random, sys, json, gzip
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from oc1hall_ref import val, threatened, efx0, sd
from multi_ref import frozen_set, canonical_chains, subsets
from cert_ref import apply_move
from theorem_s_ref import after_chain

def picks_state(Y):
    return [({y} if y is not None else set()) for y in Y]

def earliest_wanter_chain(v, Y, sigma, k):
    n = len(Y); p = [val(v, i, picks_state(Y)[i]) for i in range(n)]
    pos = {a: i for i, a in enumerate(sigma)}
    seq = [k]
    while True:
        prev = seq[-1]
        if Y[prev] is None:
            return None
        W = [a for a in range(n) if a != prev and v[a][Y[prev]] > p[a]]
        if not W:
            return seq if len(seq) >= 2 else None
        nxt = min(W, key=lambda a: pos[a])
        if nxt in seq:
            return "CYCLE"
        seq.append(nxt)

def reduce_inst(v, Y, seq, T):
    n = len(Y); m = len(v[0]); k = seq[0]
    B1 = after_chain(Y, seq, T)
    agents = [a for a in range(n) if a != k]
    goods = [g for g in range(m) if g not in T]
    gi = {g: i for i, g in enumerate(goods)}
    vm = [[v[a][g] for g in goods] for a in agents]
    Ym = [(gi[next(iter(B1[a]))] if B1[a] else None) for a in agents]
    return agents, goods, vm, Ym, B1

def theorem_s_cases(v, Y):
    """every (k', P', h, H0', r, A) meeting Theorem S (relaxed, h in J ∪ {Y_z}) at picks Y; H0' ⊆ W ∩ R_k'."""
    n = len(Y); m = len(v[0])
    B = picks_state(Y)
    J = set(range(m)) - set().union(*B); p = [val(v, i, B[i]) for i in range(n)]
    F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
    U = [u for u in range(n) if u not in F and Y[u] is not None]
    allch = list(canonical_chains(v, Y, F))
    for k in sorted(D):
        ch = [s for s in allch if s[0] == k]
        if not ch:
            continue
        L = max(len(s) for s in ch)
        for seq in [s for s in ch if len(s) == L]:
            z = seq[-1]; a = Y[seq[-2]]
            for h in sorted(J) + [Y[z]]:
                W = (J | {Y[z]}) - {h}
                if not val(v, k, W) > p[k]:
                    continue
                if any(threatened(v, d, W, p[d]) for d in D if d != k):
                    continue
                if any(threatened(v, u, W, p[u]) for u in U if u != z):
                    continue
                for H0 in subsets({g for g in W if v[k][g] > 0}):
                    if not val(v, k, H0) > p[k]:
                        continue
                    Bp = after_chain(Y, seq, H0)
                    Fp = frozen_set(v, Bp)
                    zval = v[z][a] + (0 if z in Fp else v[z][h])
                    if threatened(v, z, W, zval):
                        continue
                    recv = [z] if z not in Fp else [w for w in range(n) if w != z and v[w][a] > val(v, w, Bp[w])]
                    for r in recv:
                        A = [set(b) for b in Bp]; A[k] = set(W); A[r] = Bp[r] | {h}
                        yield k, seq, h, H0, r, A

def sde_tests(v, Y, sigma, c, ex, mut=None, tag=""):
    n = len(Y); m = len(v[0])
    B = picks_state(Y); J = set(range(m)) - set().union(*B)
    F = frozen_set(v, B)
    for k in sorted(F):
        if mut == "anychain":
            chains = [s for s in canonical_chains(v, Y, F) if s[0] == k]
        else:
            E = earliest_wanter_chain(v, Y, sigma, k)
            if E is None or E == "CYCLE":
                c[tag + "sde_no_chain_or_cycle"] += 1
                continue
            if E[-1] in F or any(x not in F for x in E[1:-1]):
                c[tag + "sde_chain_not_canonical"] += 1
            chains = [E]
        for seq in chains:
            z = seq[-1]
            for T in subsets(J | {Y[z]}):
                agents, goods, vm, Ym, B1 = reduce_inst(v, Y, seq, T)
                sig = [agents.index(a) for a in sigma if a != k]
                c[tag + "sde_tests"] += 1
                if [sd(vm, sig)[i] for i in range(len(agents))] != Ym:
                    c[tag + "sde_FAIL"] += 1
                    if len(ex) < 6:
                        ex.append(("SD-E", mut, v, Y, sigma, seq, sorted(T)))

def recs_tests(v, Y, sigma, c, ex, mut=None, tag=""):
    """returns True if REC-S (as stated) repairs this start."""
    n = len(Y); m = len(v[0])
    B = picks_state(Y); J = set(range(m)) - set().union(*B)
    p = [val(v, i, B[i]) for i in range(n)]
    F = frozen_set(v, B); D = {d for d in F if any(v[d][g] > 0 for g in J)}
    covered = False
    for k in sorted(D):
        if mut == "anychain":
            chains = [s for s in canonical_chains(v, Y, F) if s[0] == k]
        else:
            E = earliest_wanter_chain(v, Y, sigma, k)
            if E is None or E == "CYCLE":
                continue
            chains = [E]
        for seq in chains:
            z = seq[-1]
            for T in itertools.combinations(sorted((J | {Y[z]}) & {g for g in range(m) if v[k][g] > 0}), 2):
                T = set(T)
                if not val(v, k, T) > p[k]:
                    continue
                B1 = after_chain(Y, seq, T)
                Lh = all(v[i][g] < val(v, i, B1[i]) for i in range(n) if i != k and any(v[i]) for g in T)
                c[tag + "pairs"] += 1
                if not Lh:
                    c[tag + "L_fails"] += 1
                    continue
                agents, goods, vm, Ym, B1 = reduce_inst(v, Y, seq, T)
                sig = [agents.index(a) for a in sigma if a != k]
                isSD = [sd(vm, sig)[i] for i in range(len(agents))] == Ym
                if not isSD:
                    c[tag + "B1minus_not_SD"] += 1
                    if mut != "anychain":
                        continue
                for kq, sq, h, H0, r, Am in theorem_s_cases(vm, Ym):
                    Xq = [set() for _ in range(n)]
                    for i, a in enumerate(agents):
                        Xq[a] = {goods[g] for g in Am[i]}
                    Xq[k] = set(T)
                    K = not any(len(Xq[j]) >= 2 and threatened(v, k, Xq[j], val(v, k, T)) for j in range(n) if j != k)
                    c[tag + "S_cases_in_Iminus"] += 1
                    if not K:
                        c[tag + "K_fails"] += 1
                        if mut != "noK":
                            continue
                    # validate the composed repair in I with my own move simulation
                    B0 = picks_state(Y)
                    mv1 = dict(kind="chain", path=list(seq), H=[sorted(T)] + [[] for _ in seq[1:]])
                    S1 = apply_move(v, B0, mv1)
                    path2 = [agents[x] for x in sq]
                    mv2 = dict(kind="chain", path=path2, H=[sorted(goods[g] for g in H0)] + [[] for _ in sq[1:]])
                    S2 = apply_move(v, S1, mv2) if S1 is not None else None
                    key = tag + ("noK_" if (mut == "noK" and not K) else "") + ("" if isSD else "notSD_") + "repairs"
                    if set(path2) & set(seq[1:]):
                        c[tag + "P2_contains_E_agent"] += 1
                        if path2[0] in seq[1:]:
                            c[tag + "P2_owner_is_E_agent"] += 1
                        if path2[-1] in seq[1:]:
                            c[tag + "P2_head_is_E_agent"] += 1
                    c[key + "_tests"] += 1
                    ok = S1 is not None and S2 is not None
                    if ok:
                        part = sum(len(x) for x in Xq) == m and set().union(*Xq) == set(range(m))
                        within = all(S2[i] <= Xq[i] for i in range(n))
                        absorbers = sum(1 for i in range(n) if len(Xq[i] - S2[i]) >= 2)
                        ok = part and within and absorbers <= 1 and efx0(v, Xq)
                    if not ok:
                        c[key + "_FAIL"] += 1
                        if len(ex) < 6:
                            ex.append(("REC-S", mut, v, Y, sigma, seq, sorted(T), path2, sorted(goods[g] for g in H0),
                                       [sorted(x) for x in Xq], S1 is not None, S2 is not None))
                    elif K:
                        covered = True
    return covered

def strict_instance(rng, n, m, ties=False):
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        gs = rng.sample(range(m), rng.randint(2, min(4, m)))
        xs = [rng.randint(1, 5) for _ in gs] if ties else rng.sample(range(1, 40), len(gs))
        for g, x in zip(gs, xs):
            v[i][g] = x
    return v

def rand_run(N, seed, which, mut=None):
    rng = random.Random(seed); c = Counter(); ex = []
    for _ in range(N):
        n = rng.randint(3, 5); m = rng.randint(n + 1, n + 4)
        v = strict_instance(rng, n, m, ties=(mut == "ties"))
        orders = list(itertools.permutations(range(n))); rng.shuffle(orders)
        seen = set()
        for o in orders[:4]:
            yd = sd(v, o); Y = [yd[i] for i in range(n)]
            if tuple(Y) in seen or any(Y[i] is None and any(v[i]) for i in range(n)):
                continue
            seen.add(tuple(Y))
            if len(set(range(m)) - {y for y in Y if y is not None}) > 5:
                continue
            c["starts"] += 1
            if which == "sde":
                sde_tests(v, Y, list(o), c, ex, mut)
            else:
                c["recs_covered"] += recs_tests(v, Y, list(o), c, ex, mut)
    print(json.dumps(dict(source=f"{which} random strict perfect starts N={N} seed={seed} mutation={mut}", **dict(sorted(c.items())))))
    for e in ex[:6]:
        print("EXAMPLE", e)

def data_run(paths, mut=None):
    c = Counter(); ex = []
    for path in paths:
        f = gzip.open(path, "rt") if path.endswith(".gz") else open(path)
        for line in f:
            d = json.loads(line); n = len(d["sets"]); m = 1 + max(g for s in d["sets"] for g in s)
            v = [[0] * m for _ in range(n)]
            for i in range(n):
                for g, x in zip(d["sets"][i], d["vals"][i]):
                    v[i][g] = x
            yd = sd(v, d["order"]); Y = [yd[i] for i in range(n)]
            c["starts"] += 1
            if Y != d["picks"]:
                c["picks_mismatch"] += 1; continue
            if any(len({x for x in v[i] if x > 0}) != sum(1 for x in v[i] if x > 0) for i in range(n)):
                c["not_strict"] += 1
            if mut is None:
                sde_tests(v, Y, d["order"], c, ex)
            c["recs_covered"] += recs_tests(v, Y, d["order"], c, ex, mut)
    print(json.dumps(dict(source=f"SD-E and REC-S on {[p.rsplit('/', 1)[-1] for p in paths]} mutation={mut}", **dict(sorted(c.items())))))
    for e in ex[:6]:
        print("EXAMPLE", e)

if __name__ == "__main__":
    if sys.argv[1] == "data":
        mut = None if sys.argv[2] == "-" else sys.argv[2]
        data_run(sys.argv[3:], mut)
    else:
        rand_run(int(sys.argv[2]), int(sys.argv[3]), sys.argv[1], sys.argv[4] if len(sys.argv) > 4 else None)
