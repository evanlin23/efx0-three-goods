"""Independent checker for the UNSAT certificates of monotone/run_search.py.

Shares no code with monotone/synth.py, monotone/run_search.py or monotone/mono_lib.py.

A certificate for a hypergraph H = (R_1, ..., R_n) on goods 0..m-1 is a list L of complete allocations
(owner lists). Claim: for every normalized monotone profile (v_i depends only on S cap R_i), some X in L
is EFX0. By perturbation it suffices to treat nondegenerate profiles (no-EFX0 is an open condition, so a
counterexample stays one after a small strictly increasing perturbation that makes all 2^|R_i| values of
each agent distinct). A nondegenerate profile is, per agent, a strict total order on the subsets of R_i
extending strict inclusion. This checker encodes exactly that:
  variables  o_i[S][T]  (S < T as integers)  <=>  v_i(S) < v_i(T),   with o_i[T][S] := -o_i[S][T];
  inclusion  o_i[S][T] for S strict subset T;   transitivity: no 3-cycle, for every triple of subsets;
  for every X in L, the clause "X is not EFX0": the disjunction, over all i != j and g in X_j, of
     o_i[ X_i cap R_i ][ (X_j - g) cap R_i ]    (taken literally from the definition; a literal with both
     sides equal is impossible, since the two sets are disjoint, unless both are empty: then omitted).
UNSAT  <=>  the certificate is valid. Solver: Glucose 4 (synth.py uses CaDiCaL).

Usage: python3 monotone/check_cert.py results/monotone/*.jsonl
"""
import sys
import json
from pysat.solvers import Solver


def check(rec):
    n, m, R = rec["n"], rec["m"], rec["R"]
    L = rec["cert"]
    # basic sanity of the record
    for i in range(n):
        assert len(R[i]) == len(set(R[i])) and all(0 <= g < m for g in R[i])
    for X in L:
        assert len(X) == m and all(0 <= o < n for o in X), "certificate entry is not a complete allocation"
    nxt = [1]

    def new():
        nxt[0] += 1
        return nxt[0] - 1

    clauses = []
    var = []
    idx = []
    for i in range(n):
        r = len(R[i])
        N = 1 << r
        idx.append({g: t for t, g in enumerate(R[i])})
        vi = {}
        for S in range(N):
            for T in range(S + 1, N):
                vi[(S, T)] = new()
        var.append(vi)

    def lit(i, S, T):
        return var[i][(S, T)] if S < T else -var[i][(T, S)]

    for i in range(n):
        N = 1 << len(R[i])
        for S in range(N):
            for T in range(N):
                if S != T and S & T == S:
                    clauses.append([lit(i, S, T)])
        for a in range(N):
            for b in range(N):
                if b == a:
                    continue
                for c in range(N):
                    if c == a or c == b:
                        continue
                    clauses.append([-lit(i, a, b), -lit(i, b, c), -lit(i, c, a)])

    if rec.get("sb"):
        # symmetry breaking used by the search: goods valued by exactly the same agents are
        # interchangeable (a hypergraph automorphism), so WLOG the least such agent values the
        # singletons of the class increasingly in the goods' indices (monotone/threshold.md, section 3)
        cls = {}
        for g in range(m):
            cls.setdefault(tuple(a for a in range(n) if g in R[a]), []).append(g)
        for key, gs in cls.items():
            if key:
                a = min(key)
                for g, h in zip(sorted(gs), sorted(gs)[1:]):
                    clauses.append([lit(a, 1 << idx[a][g], 1 << idx[a][h])])

    def loc(i, goods):
        s = 0
        for g in goods:
            if g in idx[i]:
                s |= 1 << idx[i][g]
        return s

    for X in L:
        bundles = [[g for g in range(m) if X[g] == a] for a in range(n)]
        cl = []
        for i in range(n):
            own = loc(i, bundles[i])
            for j in range(n):
                if j == i:
                    continue
                for g in bundles[j]:
                    other = loc(i, [h for h in bundles[j] if h != g])
                    if own == other:
                        continue  # both empty: v_i(X_j - g) = 0 <= v_i(X_i), never a violation
                    cl.append(lit(i, own, other))
        if not cl:
            return True  # this allocation is EFX0 for every profile
        clauses.append(cl)
    with Solver(name="glucose4", bootstrap_with=clauses) as s:
        return not s.solve()


def main():
    tot = ok = 0
    for f in sys.argv[1:]:
        for line in open(f):
            rec = json.loads(line)
            if rec["status"] != "UNSAT":
                continue
            tot += 1
            if check(rec):
                ok += 1
            else:
                print("INVALID certificate:", f, rec["types"])
    print(f"{ok}/{tot} certificates valid")
    sys.exit(0 if ok == tot else 1)


if __name__ == "__main__":
    main()
