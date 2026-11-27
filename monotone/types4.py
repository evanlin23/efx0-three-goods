"""How many EFX0-relevant types does a 4-good agent have, monotone versus additive?

EFX0 only compares disjoint subsets of R_i (monotone/k3.md, Step 3). So the type of a nondegenerate agent with
|R_i| = r is its *disjoint signature*: for each unordered pair {A, B} of disjoint nonempty subsets of R_i,
which of the two is worth more. (Pairs with an empty side are fixed by strict monotonicity.)

- Monotone: all signatures of linear extensions of the Boolean lattice 2^[r]. Counted exactly by SAT:
  the order encoding (pairwise variables, inclusion, transitivity) on the 2^r subsets, with every model
  projected onto the disjoint-pair variables and blocked.
- Additive: signatures of nondegenerate additive valuations, found from integer weight vectors 1..W
  (a LOWER bound on the exact count; it stabilises as W grows).
For r = 3 both counts must agree (Lemma S3); r = 4 shows the gap.

Usage: python3 monotone/types4.py
"""
from itertools import product, combinations
from pysat.solvers import Solver


def disjoint_pairs(r):
    N = 1 << r
    return [(A, B) for A in range(1, N) for B in range(A + 1, N) if not (A & B)]


def monotone_signatures(r):
    N = 1 << r
    var = {}
    nxt = 1
    for S in range(N):
        for T in range(S + 1, N):
            var[(S, T)] = nxt
            nxt += 1

    def lit(S, T):
        return var[(S, T)] if S < T else -var[(T, S)]

    cl = []
    for S in range(N):
        for T in range(N):
            if S != T and S & T == S:
                cl.append([lit(S, T)])
    for a, b, c in combinations(range(N), 3):
        cl.append([-lit(a, b), -lit(b, c), -lit(c, a)])
        cl.append([-lit(a, c), -lit(c, b), -lit(b, a)])
    proj = [lit(A, B) for A, B in disjoint_pairs(r)]
    sigs = set()
    with Solver(name="cadical153", bootstrap_with=cl) as s:
        while s.solve():
            model = set(l for l in s.get_model() if l > 0)
            sig = tuple((l in model) if l > 0 else (-l not in model) for l in proj)
            sigs.add(sig)
            s.add_clause([-l if b else l for l, b in zip(proj, sig)])
    return sigs


def additive_signatures(r, W):
    pairs = disjoint_pairs(r)
    sigs = set()
    for w in product(range(1, W + 1), repeat=r):
        val = [sum(w[g] for g in range(r) if (S >> g) & 1) for S in range(1 << r)]
        if len(set(val)) < (1 << r):
            continue
        sigs.add(tuple(val[A] < val[B] for A, B in pairs))
    return sigs


def main():
    for r in (3, 4):
        mono = monotone_signatures(r)
        print(f"r = {r}: {len(disjoint_pairs(r))} disjoint pairs; monotone signatures (exact): {len(mono)}")
        for W in ((8, 12) if r == 3 else (12, 20, 30)):
            add = additive_signatures(r, W)
            assert add <= mono
            print(f"   additive signatures with weights 1..{W}: {len(add)} (lower bound)")


if __name__ == "__main__":
    main()
