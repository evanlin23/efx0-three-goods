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

Usage: python3 monotone/run_search.py n m k out.jsonl [--jobs J] [--time-limit S] [--np] [--no-rank-check] [--hg cached.json] [--warm V] [--only-k]
"""
import sys
import os
import json
import time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hypergraphs import enumerate_hypergraphs, to_R
from synth import AgentEnc, alloc_clause, find_efx0, find_efx0_fast, verify_counterexample
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


def np_clauses(n, R, agents):
    """Non-peelability (monotone/threshold.md §2, item 8): in a counterexample with the fewest agents no
    agent can be peeled by L2's general step, so v_i(P) < v_i(R_i - P) for every P that is a single good
    of R_i or a nonempty set of goods private to i."""
    out = []
    for i in range(n):
        ag = agents[i]
        others = set(g for j in range(n) if j != i for g in R[j])
        priv = [g for g in R[i] if g not in others]
        full = ag.local(sum(1 << g for g in R[i]))
        Ps = set(ag.local(1 << g) for g in R[i])
        for mask in range(1, 1 << len(priv)):
            Ps.add(ag.local(sum(1 << priv[t] for t in range(len(priv)) if (mask >> t) & 1)))
        for P in Ps:
            if P != full:
                out.append([ag.lt(P, full & ~P)])
            else:
                out.append([])  # R_i itself private (or |R_i| = 1): i is always peelable
    return out


def cegar(n, m, R, enc="order", solver="cadical153", time_limit=None, sb=True, npl=False, V=None, seed=None):
    """CEGAR. V caps the rank encoding's value levels (V < 2^r is a restriction: SAT answers are still
    verified counterexamples, UNSAT answers are NOT exact). seed: allocations whose clauses start the loop."""
    if V is not None:
        pool = IDPool()
        clauses = []
        T = pool.id()
        clauses.append([T])
        agents = [AgentEnc(R[i], pool, enc, V, clauses, T) for i in range(n)]
    else:
        pool, clauses, agents = build(n, R, enc)
    L0 = []
    if seed:
        for X in seed:
            cl = alloc_clause(n, m, agents, X)
            if not cl:
                return "UNSAT", [X], None, 0.0
            clauses.append(cl)
            L0.append(X)
    if sb:
        clauses.extend(sb_clauses(n, R, agents))
    if npl:
        clauses.extend(np_clauses(n, R, agents))
    L = list(L0)
    t0 = time.time()
    with Solver(name=solver, bootstrap_with=clauses) as s:
        fed = len(clauses)
        while True:
            if not s.solve():
                return "UNSAT", L, None, time.time() - t0
            model = set(l for l in s.get_model() if l > 0)
            subs = [agents[i].decode(model) for i in range(n)]
            X = find_efx0_fast(n, m, R, subs)
            if X is None:
                # confirm with the independent Python search on full tables before reporting SAT
                tables = [table_from_restricted(m, R[i], subs[i]) for i in range(n)]
                X = find_efx0(n, m, tables, R)
                assert X is None, "C and Python inner searches disagree"
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


def check_list_unsat(n, m, R, L, enc, solver="cadical153", sb=True, npl=False):
    """Is 'every allocation in L fails EFX0' (plus symmetry breaking) unsatisfiable under encoding enc?"""
    pool, clauses, agents = build(n, R, enc)
    if sb:
        clauses.extend(sb_clauses(n, R, agents))
    if npl:
        clauses.extend(np_clauses(n, R, agents))
    for X in L:
        cl = alloc_clause(n, m, agents, X)
        if not cl:
            return True
        clauses.append(cl)
    with Solver(name=solver, bootstrap_with=clauses) as s:
        return not s.solve()


def job(args):
    n, m, types, time_limit, npl, rankcheck = args[:6]
    warm = args[6] if len(args) > 6 else None
    R = to_R(types, n)
    if warm:
        # phase 1: cheap restricted search (rank encoding, `warm` value levels); a SAT answer is a verified
        # counterexample; otherwise its allocations seed the exact phase 2
        st1, L1, subs1, dt1 = cegar(n, m, R, "rank", time_limit=time_limit, sb=True, npl=npl, V=warm)
        if st1 == "SAT":
            status, L, subs, dt = st1, L1, subs1, dt1
        else:
            status, L, subs, dt = cegar(n, m, R, "order", time_limit=time_limit, sb=True, npl=npl, seed=L1)
            dt += dt1
    else:
        status, L, subs, dt = cegar(n, m, R, "order", time_limit=time_limit, sb=True, npl=npl)
    rec = {"n": n, "m": m, "types": list(types), "R": R, "deg": [len(r) for r in R],
           "status": status, "time": round(dt, 2), "cert_size": len(L), "sb": True, "np": npl}
    if status == "SAT":
        ok, info = verify_counterexample(n, m, R, subs)
        rec["verified"] = ok
        rec["subs"] = subs
        rec["info"] = info if not ok else {"relevance": info["relevance"]}
    elif status == "UNSAT":
        # certificate: complete allocations as owner lists (owner of good 0, ..., good m-1)
        rec["cert"] = [[next(a for a in range(n) if (X[a] >> g) & 1) for g in range(m)] for X in L]
        rec["rank_on_cert_unsat"] = check_list_unsat(n, m, R, L, "rank", npl=npl) if rankcheck else None
        rec["order_on_cert_unsat"] = check_list_unsat(n, m, R, L, "order", npl=npl)
        if not (rec["rank_on_cert_unsat"] in (True, None) and rec["order_on_cert_unsat"]):
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
    npl = "--np" in sys.argv          # add non-peelability constraints (threshold.md §2, item 8)
    rankcheck = "--no-rank-check" not in sys.argv
    warm = int(sys.argv[sys.argv.index("--warm") + 1]) if "--warm" in sys.argv else None
    if "--hg" in sys.argv:  # cached output of enumerate_hypergraphs(n, m, k), as a JSON list
        hs = [tuple(h) for h in json.load(open(sys.argv[sys.argv.index("--hg") + 1]))]
    else:
        hs = enumerate_hypergraphs(n, m, k)
    if "--only-k" in sys.argv:
        # only hypergraphs whose largest |R_i| is exactly k (the others are in the k - 1 files)
        hs = [h for h in hs if max(len(r) for r in to_R(h, n)) == k]
    print(f"n={n} m={m} k<={k}: {len(hs)} hypergraphs", flush=True)
    t0 = time.time()
    counts = {}
    with open(out, "w") as f, Pool(jobs) as pool:
        for rec in pool.imap_unordered(job, [(n, m, h, time_limit, npl, rankcheck, warm) for h in hs]):
            counts[rec["status"]] = counts.get(rec["status"], 0) + 1
            f.write(json.dumps(rec) + "\n")
            f.flush()
            if rec["status"] != "UNSAT":
                print("  ", rec["status"], rec["types"], rec["deg"], rec.get("verified"), rec["time"], flush=True)
    print(f"done in {time.time() - t0:.1f}s: {counts}", flush=True)


if __name__ == "__main__":
    main()
