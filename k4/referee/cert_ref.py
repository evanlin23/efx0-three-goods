#!/usr/bin/env python3
"""Referee re-check (evidence, not a proof) of the certifier's n = 4 results (k4/oc1cert.md, branch
compute/k4-oc1max-cert at fa8e971). Own code: official moves (k4/sdc.md §29: additions; chains t >= 1 with nonempty
passed bases, H sets inside the receivers' relevant goods and inside the current junk, strict gains; x0 may take goods
of B_{xt}), one-absorber and free completions by brute force, raw EFX0. Nothing from k4/oc1cert/ or k4/sdc/ is run
or imported; the certificate and the counterexample file are read as data.

  cex  : the 11 OC1^max counterexamples (results/k4_oc1max/oc1max_cex_n4.json): SD order, perfect start, nu = 4, no
         one-absorber (and no free) completion at the picks or after any one move; two moves repair; the pattern of
         k4/oc1cert.md §1; and the same for 20 order-preserving perturbations of each profile (ordinality). Every
         certificate 'seq' witness of the core is validated at the counterexample start.
  sample: random cores of cert_4_depth2.json.gz, random strict profiles, every SD order whose picks form a maximum
         matching: (a) OC2^max decided by my forward search; (b) some certificate witness validates at that start
         under my own simulation of its moves. Also every validating witness is a genuine repair.
"""
import itertools, random, sys, json, gzip

def val(v, i, S):
    return sum(v[i][g] for g in S)

def efx0(v, X):
    n = len(X)
    for i in range(n):
        t = val(v, i, X[i])
        for j in range(n):
            if i != j and len(X[j]) >= 2:
                tot = val(v, i, X[j])
                if any(tot - v[i][h] > t for h in X[j]):
                    return False
    return True

def rel(v, i):
    return {g for g in range(len(v[i])) if v[i][g] > 0}

def sd(v, order):
    m = len(v[0]); G = set(range(m)); y = [None] * len(v)
    for i in order:
        R = [g for g in G if v[i][g] > 0]
        if R:
            g = max(R, key=lambda g: (v[i][g], -g)); y[i] = g; G.discard(g)
    return y

def nu(v):
    n = len(v); m = len(v[0]); match = {}
    def aug(i, seen):
        for g in range(m):
            if v[i][g] > 0 and g not in seen:
                seen.add(g)
                if g not in match or aug(match[g], seen):
                    match[g] = i
                    return True
        return False
    return sum(1 for i in range(n) if aug(i, set()))

def complete(v, B, free=False):
    n = len(B); m = len(v[0]); J = sorted(set(range(m)) - set().union(*B))
    for f in itertools.product(range(n), repeat=len(J)):
        if not free:
            cnt = [0] * n
            for a in f:
                cnt[a] += 1
            if sum(1 for x in cnt if x >= 2) > 1:
                continue
        X = [set(b) for b in B]
        for g, a in zip(J, f):
            X[a].add(g)
        if efx0(v, X):
            return X
    return None

def subsets(S):
    S = sorted(S)
    for k in range(len(S) + 1):
        for c in itertools.combinations(S, k):
            yield set(c)

def moves(v, B, rings=False):
    """every state one official move away from bases B (k4/sdc.md §29). rings=True adds the certifier's extra 'ring'
    kind: a cycle in which every agent takes its predecessor's whole base plus junk (x0 may then hold a good it values
    at 0), with strict gains for all."""
    n = len(B); m = len(v[0]); J = set(range(m)) - set().union(*B)
    R = [rel(v, i) for i in range(n)]
    out = []
    for x in range(n):
        for H in subsets(J & R[x]):
            if H:
                c = [set(b) for b in B]; c[x] |= H; out.append(c)
    for t in range(1, n):
        for seq in itertools.permutations(range(n), t + 1):
            if any(not B[x] for x in seq[:-1]):
                continue
            def rec(i, used, nb):
                if i > t:
                    pool = ((J - used) | B[seq[-1]]) & R[seq[0]]
                    for H0 in subsets(pool):
                        if H0 and val(v, seq[0], H0) > val(v, seq[0], B[seq[0]]):
                            c = [set(b) for b in nb]; c[seq[0]] = set(H0); out.append(c)
                    return
                xi, pr = seq[i], seq[i - 1]
                for Hi in subsets((J - used) & R[xi]):
                    if val(v, xi, B[pr] | Hi) > val(v, xi, B[xi]):
                        c = [set(b) for b in nb]; c[xi] = B[pr] | Hi
                        rec(i + 1, used | Hi, c)
            rec(1, set(), [set(b) for b in B])
    if rings:
        for r in range(2, n + 1):
            for cyc in itertools.permutations(range(n), r):
                if cyc[0] != min(cyc) or any(not B[x] for x in cyc):
                    continue
                def ring(i, used, nb):
                    if i == r:
                        out.append(nb); return
                    w, pred = cyc[i], cyc[i - 1]
                    for Hw in subsets((J - used) & R[w]):
                        if val(v, w, B[pred] | Hw) > val(v, w, B[w]):
                            c = [set(b) for b in nb]; c[w] = B[pred] | Hw
                            ring(i + 1, used | Hw, c)
                ring(0, set(), [set(b) for b in B])
    uniq = {}
    for c in out:
        uniq[tuple(frozenset(b) for b in c)] = c
    return list(uniq.values())

def oc_depth(v, Y, maxd=2):
    B = [({y} if y is not None else set()) for y in Y]
    if complete(v, B):
        return 0
    one = moves(v, B)
    if any(complete(v, b) for b in one):
        return 1
    if maxd >= 2:
        for b in one:
            if any(complete(v, b2) for b2 in moves(v, b)):
                return 2
    return None

def apply_move(v, B, mv):
    """apply one witness move to bases B; return new bases or None if illegal."""
    n = len(B); m = len(v[0]); J = set(range(m)) - set().union(*B)
    path, H = mv["path"], [set(h) for h in mv["H"]]
    R = [rel(v, i) for i in range(n)]
    if mv["kind"] == "add":
        x = path[0]
        if not H[0] or not H[0] <= J & R[x]:
            return None
        c = [set(b) for b in B]; c[x] |= H[0]; return c
    if mv["kind"] in ("chain", "ring"):
        t = len(path) - 1
        if t < 1 or len(set(path)) != len(path) or any(not B[x] for x in path[:-1]):
            return None
        used = set()
        c = [set(b) for b in B]
        for i in range(1, t + 1):
            xi = path[i]
            if not H[i] <= (J - used) & R[xi]:
                return None
            if not val(v, xi, B[path[i - 1]] | H[i]) > val(v, xi, B[xi]):
                return None
            used |= H[i]; c[xi] = B[path[i - 1]] | H[i]
        x0 = path[0]
        if not H[0] or not H[0] <= ((J - used) | B[path[-1]]) & R[x0] or not val(v, x0, H[0]) > val(v, x0, B[x0]):
            return None
        c[x0] = set(H[0]); return c
    return None

def witness_valid(v, Y, w):
    n = len(Y); m = len(v[0])
    if any(Y[int(a)] != g for a, g in w["picks"].items()):
        return False
    B = [({y} if y is not None else set()) for y in Y]
    mv = w["moves"] if w["kind"] == "seq" else ([] if w["kind"] == "picks" else [w])
    for x in mv:
        B = apply_move(v, B, x)
        if B is None:
            return False
    X = [set() for _ in range(n)]
    for g, a in enumerate(w["X"]):
        X[int(a)].add(g)
    if len(w["X"]) != m or any(not B[i] <= X[i] for i in range(n)):
        return False
    if sum(1 for i in range(n) if len(X[i] - B[i]) >= 2) > 1:
        return False
    return efx0(v, X)

def mk(sets, vals):
    m = 1 + max(max(s) for s in sets if s)
    v = [[0] * m for _ in sets]
    for i, (s, x) in enumerate(zip(sets, vals)):
        for g, a in zip(s, x):
            v[i][g] = a
    return v

def pattern(v, Y):
    n = len(Y); m = len(v[0]); J = set(range(m)) - set(Y)
    p = [v[i][Y[i]] for i in range(n)]
    F = {j for j in range(n) if any(i != j and v[i][Y[j]] > p[i] for i in range(n))}
    pairs = {}
    for i in F:
        for a, b in itertools.combinations(sorted(J & rel(v, i)), 2):
            if v[i][a] + v[i][b] > p[i]:
                pairs.setdefault((a, b), set()).add(i)
    shared = [k for k, s in pairs.items() if len(s) >= 2]
    priv2 = any(sum(1 for g in rel(v, i) if all(v[j][g] == 0 for j in range(n) if j != i)) >= 2 for i in range(n))
    return dict(unfrozen=n - len(F), shared_danger_pairs=len(shared), junk=len(J), agent_with_two_private=priv2)

def cex(cert):
    d = json.load(open(sys.argv[2]))
    insts = d["instances"]
    if isinstance(insts, str):
        import ast
        insts = ast.literal_eval(insts)
    cores = {(c["list"], tuple(map(tuple, c["sets"]))): c for c in cert["cores"]}
    rng = random.Random(1)
    for I in insts:
        v = mk(I["sets"], I["vals"]); n = len(v); m = len(v[0]); Y = I["picks"]
        orders = [o for o in itertools.permutations(range(n)) if sd(v, o) == list(Y)]
        strict = all(len({val(v, i, S) for S in subsets(rel(v, i))}) == 2 ** len(rel(v, i)) for i in range(n))
        B = [{y} for y in Y]
        one = moves(v, B)
        oner = moves(v, B, rings=True)
        r = dict(core=f"{I['list']}#{I['idx']}", m=m, sd_orders=len(orders), strict_balanced=strict, nu=nu(v),
                 perfect=all(y is not None for y in Y),
                 picks_complete_oa=bool(complete(v, B)), picks_complete_free=bool(complete(v, B, True)),
                 one_move_states=len(one), one_move_oa=sum(1 for b in one if complete(v, b)),
                 one_move_free=sum(1 for b in one if complete(v, b, True)),
                 one_move_states_with_rings=len(oner), with_rings_oa=sum(1 for b in oner if complete(v, b)),
                 with_rings_free=sum(1 for b in oner if complete(v, b, True)),
                 two_move_repairing_first_moves=sum(1 for b in one if any(complete(v, b2) for b2 in moves(v, b))),
                 efx0_allocations=sum(1 for f in itertools.product(range(n), repeat=m)
                                      if efx0(v, [{g for g in range(m) if f[g] == i} for i in range(n)])),
                 failing_orders=sum(1 for o in itertools.permutations(range(n)) if oc_depth(v, sd(v, o), 1) is None),
                 **pattern(v, Y))
        # ordinality: perturbations preserving every strict comparison of disjoint sets
        same = 0
        for _ in range(20):
            w = [[(1000 * x + rng.random() * 0.24) if x > 0 else 0 for x in row] for row in v]
            same += (sd(w, orders[0]) == list(Y)) and oc_depth(w, Y, 1) is None and oc_depth(w, Y, 2) == 2
        r["perturbations_still_failing_and_two_move"] = f"{same}/20"
        key = (I["list"], tuple(map(tuple, I["sets"])))
        c = cores.get(key)
        if c:
            seqw = [w for w in c["witnesses"] if w["kind"] == "seq"]
            r["cert_seq_witnesses"] = len(seqw)
            r["cert_seq_valid_here"] = sum(1 for w in seqw if witness_valid(v, Y, w))
            r["cert_nonseq_valid_here"] = sum(1 for w in c["witnesses"] if w["kind"] != "seq" and witness_valid(v, Y, w))
        else:
            r["cert_core_found"] = False
        print(json.dumps(r))

def core_values(rng, sets, i):
    """random values on sets[i] inside the certificate's domain (K4.CORE / K4.OT): strict (no two disjoint nonempty
    subsets with equal sums), strictly balanced (2 v(g) < v(R_i) for every g), and (C4): if i has two private goods
    p, q (relevant to no other agent), v(p) + v(q) < v(shared goods)."""
    s = sets[i]
    priv = [g for g in s if all(g not in sets[j] for j in range(len(sets)) if j != i)]
    while True:
        x = rng.sample(range(1, 60), len(s))
        if 2 * max(x) >= sum(x):
            continue
        sums = {}
        ok = True
        for k in range(1, len(s) + 1):
            for A in itertools.combinations(range(len(s)), k):
                sums[A] = sum(x[a] for a in A)
        for A, a in sums.items():
            for B, b in sums.items():
                if a == b and A != B and not set(A) & set(B):
                    ok = False
        if not ok:
            continue
        if len(priv) == 2:
            pv = sum(x[s.index(g)] for g in priv)
            if not pv < sum(x) - pv:
                continue
        return x

def sample(cert, N, seed):
    rng = random.Random(seed)
    cores = cert["cores"]
    c = dict(cores=0, profiles=0, starts=0, depth0=0, depth1=0, depth2=0, oc2_fail=0, covered=0, uncovered=0,
             valid_but_search_says_no=0, seq_valid=0)
    ex = []
    for _ in range(N):
        C = rng.choice(cores)
        sets = C["sets"]; n = len(sets)
        c["cores"] += 1
        for _p in range(3):
            vals = [core_values(rng, sets, i) for i in range(n)]
            v = mk(sets, vals)
            if len(v[0]) != C["m"]:
                v = [row + [0] * (C["m"] - len(row)) for row in v]
            c["profiles"] += 1
            nv = nu(v)
            seen = set()
            for o in itertools.permutations(range(n)):
                Y = sd(v, o)
                if tuple(Y) in seen or sum(1 for y in Y if y is not None) != nv:
                    continue
                seen.add(tuple(Y)); c["starts"] += 1
                dpt = oc_depth(v, Y, 2)
                if dpt is None:
                    c["oc2_fail"] += 1; ex.append(("oc2", sets, vals, Y))
                else:
                    c[f"depth{dpt}"] += 1
                vw = [w for w in C["witnesses"] if witness_valid(v, Y, w)]
                if vw:
                    c["covered"] += 1
                    c["seq_valid"] += any(w["kind"] == "seq" for w in vw)
                    if dpt is None:
                        c["valid_but_search_says_no"] += 1
                else:
                    c["uncovered"] += 1; ex.append(("uncovered", C["list"], C["idx"], sets, vals, Y))
    print(json.dumps(dict(source=f"certificate sample N={N} cores x 3 profiles, seed={seed}", **c)))
    for e in ex[:6]:
        print("EXAMPLE", e)

def near(cert, N, seed):
    """around the 11 counterexample cores: re-draw one or two agents' values (strict core values) of the counterexample
    profile; at every maximum-matching start that needs two moves, some certificate witness must validate."""
    rng = random.Random(seed)
    d = json.load(open(sys.argv[2]))
    insts = d["instances"]
    if isinstance(insts, str):
        import ast
        insts = ast.literal_eval(insts)
    cores = {(c["list"], tuple(map(tuple, c["sets"]))): c for c in cert["cores"]}
    c = dict(profiles=0, starts=0, depth0=0, depth1=0, depth2=0, oc2_fail=0, covered=0, uncovered=0,
             seq_needed_and_valid=0, valid_but_search_says_no=0)
    seqs_used = set()
    ex = []
    for _ in range(N):
        I = rng.choice(insts)
        C = cores[(I["list"], tuple(map(tuple, I["sets"])))]
        sets = I["sets"]; n = len(sets)
        vals = [list(x) for x in I["vals"]]
        for i in rng.sample(range(n), rng.choice([1, 1, 2])):
            vals[i] = core_values(rng, sets, i)
        v = mk(sets, vals); c["profiles"] += 1
        nv = nu(v); seen = set()
        for o in itertools.permutations(range(n)):
            Y = sd(v, o)
            if tuple(Y) in seen or sum(1 for y in Y if y is not None) != nv:
                continue
            seen.add(tuple(Y)); c["starts"] += 1
            dpt = oc_depth(v, Y, 2)
            if dpt is None:
                c["oc2_fail"] += 1; ex.append(("oc2", sets, vals, Y)); continue
            c[f"depth{dpt}"] += 1
            vw = [k for k, w in enumerate(C["witnesses"]) if witness_valid(v, Y, w)]
            if vw:
                c["covered"] += 1
                if dpt == 2:
                    sv = [k for k in vw if C["witnesses"][k]["kind"] == "seq"]
                    c["seq_needed_and_valid"] += bool(sv)
                    for k in sv:
                        seqs_used.add((C["list"], C["idx"], k))
            else:
                c["uncovered"] += 1; ex.append(("uncovered", I["list"], I["idx"], vals, Y))
    c["distinct_seq_witnesses_validated"] = len(seqs_used)
    print(json.dumps(dict(source=f"certificate near the 11 counterexamples N={N} seed={seed}", **c)))
    for e in ex[:6]:
        print("EXAMPLE", e)

if __name__ == "__main__":
    cert = json.load(gzip.open(sys.argv[1]))
    if sys.argv[3] == "cex":
        cex(cert)
    elif sys.argv[3] == "near":
        near(cert, int(sys.argv[4]), int(sys.argv[5]))
    else:
        sample(cert, int(sys.argv[3]), int(sys.argv[4]))
