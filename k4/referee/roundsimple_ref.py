#!/usr/bin/env python3
"""Referee check of Theorem ROUND-SIMPLE and Lemmas PG, GAIN (kgen/rounds.md §4.11 on proof/kgen-rounds at d79599ea,
PR #137). Own code (cert_ref, splice_ref.round_witness); nothing from kgen/ is run.

Instances: strict connected cores with DISTINCT SUBSET SUMS per agent (the setting), every perfect SD start; every
complete allocation X that is MD (v_a(X_a) >= p_a for all a) and raw EFX0. Pick graph f(a) = holder of Y_a; my own
classification of each weak component: fixed, ring, rho, rho-fix, ka, complex. Outside goods (the theorem's): worthless
junk of Y; at a ring start the end pick if unvalued (the start is chosen freely: the best choice is taken); at a rho
merge point v the end pick Y_{c_r} if unvalued; at a rho-fix keeper the tail-end pick. Hypothesis: X simple and at most
one agent with >= 2 outside goods. Test: X is a RNDOZ witness (my round_witness). Also GAIN: f(b) != b => v_b(X_b) > p_b."""
import itertools, json, gzip, sys, random
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, rel, sd, mk
from splice_ref import round_witness

def classify(f, n):
    indeg = Counter(f[a] for a in range(n))
    comp = list(range(n))
    def find(x):
        while comp[x] != x:
            comp[x] = comp[comp[x]]; x = comp[x]
        return x
    for a in range(n):
        comp[find(a)] = find(f[a])
    groups = {}
    for a in range(n):
        groups.setdefault(find(a), []).append(a)
    out = []
    for nodes in groups.values():
        x = nodes[0]; seen = []
        while x not in seen:
            seen.append(x); x = f[x]
        C = seen[seen.index(x):]; T = [a for a in nodes if a not in C]
        if not T:
            out.append(("fixed" if len(C) == 1 else "ring", C, None)); continue
        pickless = [a for a in nodes if indeg[a] == 0]
        junction = [c for c in C if indeg[c] == 2]
        path = len(pickless) == 1 and all(indeg[a] <= 1 for a in T) and len(junction) == 1 and \
            all(indeg[c] == 1 for c in C if c not in junction) and all(indeg[c] <= 2 for c in C)
        if not path:
            out.append(("complex", C, T)); continue
        if len(C) >= 2:
            out.append(("rho", C, (pickless[0], junction[0])))
        else:
            out.append(("rho-fix" if len(T) >= 2 else "ka", C, (pickless[0], junction[0])))
    return out

def outside_counts(v, Y, X, comps):
    """min over ring-start choices of the outside-goods count vector; returns list of candidate count dicts."""
    n = len(Y); m = len(v[0]); J = set(range(m)) - set(Y)
    base = Counter()
    for b in range(n):
        base[b] += sum(1 for g in X[b] & J if v[b][g] == 0)
    rings = []
    for kind, C, info in comps:
        if kind == "rho":
            q, vv = info
            # v's predecessor on the cycle: the cycle node c with f(c) = vv
            cr = next(c for c in C if c != vv and next(b for b in range(n) if Y[c] in X[b]) == vv) if len(C) > 1 else None
            if cr is not None and v[vv][Y[cr]] == 0:
                base[vv] += 1
        elif kind == "rho-fix":
            q, vv = info
            base[vv] += 1          # the tail-end pick at the keeper
        elif kind == "ring":
            rings.append(C)
    opts = []
    for starts in itertools.product(*rings):
        cnt = Counter(base)
        for C, a1 in zip(rings, starts):
            received = next(Y[c] for c in C if Y[c] in X[a1])
            if v[a1][received] == 0:
                cnt[a1] += 1
        opts.append(cnt)
    return opts or [base]

def strict_dss(rng, n, m):
    """random connected core with distinct subset sums per agent."""
    while True:
        v = [[0] * m for _ in range(n)]
        for i in range(n):
            k = rng.choice([3, 4, 4])
            gs = rng.sample(range(m), k)
            while True:
                xs = rng.sample(range(1, 60), k)
                sums = [sum(c) for r in range(1, k + 1) for c in itertools.combinations(xs, r)]
                if len(set(sums)) == len(sums):
                    break
            for g, x in zip(gs, xs):
                v[i][g] = x
        if all(any(v[i][g] for i in range(n)) for g in range(m)):
            return v

def check(args):
    v, Ys = args
    n = len(v); m = len(v[0]); c = Counter()
    for Y in Ys:
        p = [v[i][Y[i]] for i in range(n)]
        c["starts"] += 1; anyw = False; anywit = False
        for f in itertools.product(range(n), repeat=m):
            X = [set() for _ in range(n)]
            for g, a in enumerate(f):
                X[a].add(g)
            if any(val(v, i, X[i]) < p[i] for i in range(n)) or not efx0(v, X):
                continue
            c["MD_EFX0"] += 1
            pf = [next(b for b in range(n) if Y[a] in X[b]) for a in range(n)]
            c["GAIN_FAIL"] += any(pf[b] != b and not val(v, b, X[b]) > p[b] for b in range(n))
            comps = classify(pf, n)
            kinds = sorted(k for k, _, _ in comps)
            simple = all(k in ("fixed", "ring", "rho", "rho-fix") for k in kinds)
            one_abs = any(sum(1 for b in range(n) if cnt[b] >= 2) <= 1 for cnt in outside_counts(v, Y, X, comps))
            w = round_witness(v, Y, X, "RNDOZ"); anywit |= w
            for k in set(kinds):
                c[f"has_{k}"] += 1
            if simple and one_abs:
                c["hyp"] += 1; c["THEOREM_VIOLATION"] += not w; anyw = True
            elif simple:
                c["simple_two_absorbers"] += 1; c["simple_two_absorbers_witness"] += w
            else:
                c["not_simple"] += 1; c["not_simple_witness"] += w
                if "complex" not in kinds:
                    c["ka_witness" if w else "ka_not_witness"] += 1
        c["starts_with_a_simple_one_absorber_MD"] += anyw; c["starts_with_a_RNDOZ_witness"] += anywit
        c["starts_witness_but_no_simple_one_absorber_MD"] += anywit and not anyw
    return c

def rand_jobs(N, seed, nlo, nhi):
    rng = random.Random(seed)
    for _ in range(N):
        n = rng.randint(nlo, nhi); m = rng.randint(n + 2, 8 if n == 4 else 7)
        v = strict_dss(rng, n, m)
        Ys = {tuple(sd(v, list(o))) for o in itertools.permutations(range(n))}
        Ys = [list(Y) for Y in Ys if None not in Y]
        if Ys:
            yield v, Ys

def export_jobs(path, N, seed):
    d = json.load(gzip.open(path)); rows = [(H["sets"], s["vals"], s["picks"]) for H in d["hypergraphs"] for s in H["starts"]]
    rng = random.Random(seed)
    for sets, vals, Y in rng.sample(rows, N):
        v = mk(sets, vals)
        if len(v[0]) <= 8:
            yield v, [Y]

def main(kind, a, b, procs):
    it = rand_jobs(int(a), int(b), 4, 5) if kind == "rand" else export_jobs(a, int(b), 1)
    c = Counter()
    with Pool(procs) as pool:
        for cc in pool.imap_unordered(check, it, chunksize=2):
            c.update(cc)
    print(json.dumps(dict(source=f"Theorem ROUND-SIMPLE on {kind} {a.rsplit('/', 1)[-1]} {b}", **dict(sorted(c.items())))))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]))
