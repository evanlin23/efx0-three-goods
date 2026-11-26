"""Driver: for every hypergraph with n agents, m goods, 3 <= |R_i| <= k (monotone/hypergraphs.py), decide
whether some monotone valuation profile has no EFX0 allocation (monotone/synth.py).

Per hypergraph:
  1. CEGAR with the order encoding plus symmetry breaking (sb_clauses). SAT => decode, verify by brute
     force with the raw definition, save. UNSAT => the allocations collected form a certificate L: no
     monotone profile obeying the symmetry breaking makes every allocation of L fail EFX0 (hence, by the
     symmetry argument, every monotone profile has an EFX0 allocation in the orbit of L).
  2. Both encodings (rank with V = 2^|R_i|, and order) on the clauses of L only, with the same symmetry
     breaking, must be UNSAT; otherwise the record is marked DISAGREE. monotone/check_cert.py re-checks
     L independently.
Writes one JSON line per hypergraph to the output file.

Usage: python3 monotone/run_search.py n m k out.jsonl [--jobs J]
"""
import sys
import os
import json
import time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hypergraphs import enumerate_hypergraphs, to_R
from synth import AgentEnc, alloc_clause, find_efx0, verify_counterexample
from mono_lib import table_from_restricted, bundles_of
from pysat.solvers import Solver
from pysat.formula import IDPool


def build(n, R, enc):
    pool = IDPool()
    clauses = []
    T = pool.id()
    clauses.append([T])
    agents = [AgentEnc(R[i], pool, enc, max(2, 1 << len(R[i])), clauses, T) for i in range(n)]
    return pool, clauses, agents


def sb_clauses(n, R, agents):
    """Symmetry breaking (monotone/threshold.md §3): goods valued by exactly the same agents form a class;
    permuting a class is a hypergraph automorphism, so WLOG the smallest agent of the class ranks the
    class's singletons in increasing order of the goods' indices."""
    m = 1 + max(g for r in R for g in r)
    classes = {}
    for g in range(m):
        key = tuple(i for i in range(n) if g in R[i])
        classes.setdefault(key, []).append(g)
    out = []
    for key, gs in classes.items():
        if not key:
            continue
        a = key[0]
        ag = agents[a]
        for g, h in zip(gs, gs[1:]):
            out.append([ag.lt(ag.local(1 << g), ag.local(1 << h))])
    return out


def cegar(n, m, R, enc="order", solver="cadical153", time_limit=None, sb=True):
    pool, clauses, agents = build(n, R, enc)
    if sb:
        clauses.extend(sb_clauses(n, R, agents))
    L = []
    t0 = time.time()
    with Solver(name=solver, bootstrap_with=clauses) as s:
        fed = len(clauses)
        while True:
            if not s.solve():
                return "UNSAT", L, None, time.time() - t0
            model = set(l for l in s.get_model() if l > 0)
            subs = [agents[i].decode(model) for i in range(n)]
            tables = [table_from_restricted(m, R[i], subs[i]) for i in range(n)]
            X = find_efx0(n, m, tables, R)
            if X is None:
                return "SAT", L, subs, time.time() - t0
            L.append(X)
            cl = alloc_clause(n, m, agents, X)
            if not cl:
                return "UNSAT", L, None, time.time() - t0
            # definitional clauses of lt literals created by alloc_clause
            for c in clauses[fed:]:
                s.add_clause(c)
            fed = len(clauses)
            s.add_clause(cl)
            if time_limit and time.time() - t0 > time_limit:
                return "TIMEOUT", L, None, time.time() - t0


def check_list_unsat(n, m, R, L, enc, solver="cadical153", sb=True):
    """Is 'every allocation in L fails EFX0' (plus symmetry breaking) unsatisfiable under encoding enc?"""
    pool, clauses, agents = build(n, R, enc)
    if sb:
        clauses.extend(sb_clauses(n, R, agents))
    for X in L:
        cl = alloc_clause(n, m, agents, X)
        if not cl:
            return True
        clauses.append(cl)
    with Solver(name=solver, bootstrap_with=clauses) as s:
        return not s.solve()


def job(args):
    n, m, types, time_limit = args
    R = to_R(types, n)
    status, L, subs, dt = cegar(n, m, R, "order", time_limit=time_limit, sb=True)
    rec = {"n": n, "m": m, "types": list(types), "R": R, "deg": [len(r) for r in R],
           "status": status, "time": round(dt, 2), "cert_size": len(L), "sb": True}
    if status == "SAT":
        ok, info = verify_counterexample(n, m, R, subs)
        rec["verified"] = ok
        rec["subs"] = subs
        rec["info"] = info if not ok else {"relevance": info["relevance"]}
    elif status == "UNSAT":
        # certificate: complete allocations as owner lists (owner of good 0, ..., good m-1)
        rec["cert"] = [[next(a for a in range(n) if (X[a] >> g) & 1) for g in range(m)] for X in L]
        rec["rank_on_cert_unsat"] = check_list_unsat(n, m, R, L, "rank")
        rec["order_on_cert_unsat"] = check_list_unsat(n, m, R, L, "order")
        if not (rec["rank_on_cert_unsat"] and rec["order_on_cert_unsat"]):
            rec["status"] = "DISAGREE"
    return rec


def main():
    n, m, k = map(int, sys.argv[1:4])
    out = sys.argv[4]
    jobs = 3
    time_limit = None
    if "--jobs" in sys.argv:
        jobs = int(sys.argv[sys.argv.index("--jobs") + 1])
    if "--time-limit" in sys.argv:
        time_limit = float(sys.argv[sys.argv.index("--time-limit") + 1])
    hs = enumerate_hypergraphs(n, m, k)
    print(f"n={n} m={m} k<={k}: {len(hs)} hypergraphs", flush=True)
    t0 = time.time()
    counts = {}
    with open(out, "w") as f, Pool(jobs) as pool:
        for rec in pool.imap_unordered(job, [(n, m, h, time_limit) for h in hs]):
            counts[rec["status"]] = counts.get(rec["status"], 0) + 1
            f.write(json.dumps(rec) + "\n")
            f.flush()
            if rec["status"] != "UNSAT":
                print("  ", rec["status"], rec["types"], rec["deg"], rec.get("verified"), rec["time"], flush=True)
    print(f"done in {time.time() - t0:.1f}s: {counts}", flush=True)


if __name__ == "__main__":
    main()
