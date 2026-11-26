"""Validation of the synthesis encodings (monotone/synth.py) against the raw definition.

1. Completeness of the allocation clauses and soundness of the value constraints, on the known
   counterexample (arXiv 2604.18216v4, Section 3.1; monotone/amm_check.py): with every agent's values
   pinned to (a nondegenerate strictification of) the paper's valuation, both encodings must be SAT.
   The strictification v' = 256 v + S (S read as a number) is injective, strictly monotone, and keeps
   every strict comparison of v, so it still has no EFX0 allocation.
2. For every UNSAT record in the given result files: draw random monotone valuation profiles on the
   hypergraph and check by brute force that some allocation of the certificate L is EFX0 (raw definition).
   This is EVIDENCE that the certificates mean what the encodings say; the UNSAT claims themselves rest
   on the two encodings.

Usage: python3 monotone/validate.py [results/monotone/*.jsonl ...] [--samples N]
"""
import sys
import os
import json
import random
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from synth import AgentEnc, alloc_clause
from mono_lib import bundles_of, table_from_restricted, efx0_violation, check_normalized_monotone
from amm_check import tables as amm_tables, v_value
from pysat.solvers import Solver
from pysat.formula import IDPool


def pinned_amm(enc):
    n, m = 3, 8
    V0 = amm_tables(v_value)
    vals = [[256 * V0[i][S] + S for S in range(256)] for i in range(3)]
    for i in range(3):
        assert check_normalized_monotone(8, vals[i]) is None
        assert len(set(vals[i])) == 256
    # ranks 0..255 (order-preserving), needed for the rank encoding with V = 256
    ranks = []
    for i in range(3):
        srt = sorted(range(256), key=lambda S: vals[i][S])
        rk = [0] * 256
        for p, S in enumerate(srt):
            rk[S] = p
        ranks.append(rk)
    pool = IDPool()
    clauses = []
    T = pool.id()
    clauses.append([T])
    R = [list(range(8))] * 3
    agents = [AgentEnc(R[i], pool, enc, 256, clauses, T) for i in range(3)]
    nalloc = 0
    for alloc in product(range(3), repeat=8):
        B = bundles_of(alloc, 3)
        cl = alloc_clause(n, m, agents, B)
        assert cl, alloc
        clauses.append(cl)
        nalloc += 1
    # pin the valuation
    for i in range(3):
        ag = agents[i]
        if enc == "rank":
            for S in range(256):
                for t in range(1, 256):
                    clauses.append([ag.x[S][t] if ranks[i][S] >= t else -ag.x[S][t]])
        else:
            for S in range(256):
                for U in range(S + 1, 256):
                    lit = ag.plit(S, U)
                    clauses.append([lit if vals[i][S] < vals[i][U] else -lit])
    with Solver(name="cadical153", bootstrap_with=clauses) as s:
        ok = s.solve()
    return ok, nalloc


def random_monotone(r, rng):
    """Random nondegenerate monotone valuation on 2^r: monotone closure of random values, tie-broken."""
    raw = [rng.random() for _ in range(1 << r)]
    raw[0] = 0.0
    v = [0.0] * (1 << r)
    for S in range(1 << r):
        best = raw[S]
        for g in range(r):
            if (S >> g) & 1:
                best = max(best, v[S & ~(1 << g)])
        v[S] = best
    # tie-break: strictly increasing perturbation
    return [v[S] + 1e-9 * (bin(S).count("1") + S / (1 << r)) for S in range(1 << r)]


def random_additive_like(r, rng):
    w = [rng.random() for _ in range(r)]
    return [sum(w[g] for g in range(r) if (S >> g) & 1) + 1e-9 * S for S in range(1 << r)]


def check_cert(rec, samples, rng):
    n, m, R = rec["n"], rec["m"], rec["R"]
    L = rec["cert"]
    fails = 0
    for _ in range(samples):
        gen = random_monotone if rng.random() < 0.7 else random_additive_like
        subs = [gen(len(R[i]), rng) for i in range(n)]
        tables = [table_from_restricted(m, R[i], subs[i]) for i in range(n)]
        if not any(efx0_violation(n, m, tables, bundles_of(X, n)) is None for X in L):
            fails += 1
    return fails


def main():
    files = [a for a in sys.argv[1:] if not a.startswith("--") and a.endswith(".jsonl")]
    samples = 200
    if "--samples" in sys.argv:
        samples = int(sys.argv[sys.argv.index("--samples") + 1])
    if "--amm" in sys.argv or not files:
        for enc in ("rank", "order"):
            ok, na = pinned_amm(enc)
            print(f"pinned counterexample, {enc} encoding, {na} allocation clauses: {'SAT' if ok else 'UNSAT'}")
            assert ok
    rng = random.Random(20261126)
    tot = bad = 0
    for f in files:
        for line in open(f):
            rec = json.loads(line)
            if rec["status"] != "UNSAT":
                continue
            fails = check_cert(rec, samples, rng)
            tot += 1
            if fails:
                bad += 1
                print("CERT FAILS on random profile:", f, rec["types"], fails)
    if files:
        print(f"random check of certificates: {tot} UNSAT records, {samples} profiles each, {bad} with a failure")


if __name__ == "__main__":
    main()
