"""Can the three-agent, eight-good counterexample (arXiv 2604.18216v4 §3.1) be modified so that some agent
ignores some good, keeping 'no EFX0 allocation'?

Exploration: fix a set of agents to the paper's valuations (pinned), and let the remaining agents be arbitrary
monotone valuations on prescribed relevant sets R_i (each missing some goods). CEGAR (order encoding,
monotone/synth.py) decides whether such free valuations exist. SAT answers are decoded and re-verified by brute
force (monotone/synth.verify_counterexample). UNSAT answers here are about this restricted family only (the
pinned agents fixed); they say nothing about other instances.

Usage: python3 monotone/amm_modify.py [--level2]
"""
import sys
import os
import time
import json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pysat.solvers import Solver
from pysat.formula import IDPool
from synth import AgentEnc, alloc_clause, find_efx0, verify_counterexample
from mono_lib import table_from_restricted
from amm_check import tables as amm_tables, v_value, NAMES


class FixedAgent:
    """An agent whose valuation is given: lt literals are constants."""

    def __init__(self, R, sub, T):
        self.R = list(R)
        self.pos = {g: t for t, g in enumerate(self.R)}
        self.Rmask = sum(1 << g for g in self.R)
        self.sub = sub
        self.T = T

    def local(self, mask):
        out = 0
        for g in self.R:
            if (mask >> g) & 1:
                out |= 1 << self.pos[g]
        return out

    def lt(self, A, B):
        return self.T if self.sub[A] < self.sub[B] else -self.T

    def decode(self, model):
        return list(self.sub)


def run(free_R, pinned, time_limit=1800):
    """free_R: dict agent -> relevant goods (free agents); pinned: set of agents fixed to the paper's v."""
    n, m = 3, 8
    V0 = amm_tables(v_value)  # full 2^8 tables (R = all goods)
    pool = IDPool()
    clauses = []
    T = pool.id()
    clauses.append([T])
    agents, R = [], []
    for i in range(n):
        if i in pinned:
            R.append(list(range(8)))
            agents.append(FixedAgent(R[i], V0[i], T))
        else:
            R.append(sorted(free_R[i]))
            agents.append(AgentEnc(R[i], pool, "order", 2, clauses, T))
    t0 = time.time()
    it = 0
    with Solver(name="cadical153", bootstrap_with=clauses) as s:
        fed = len(clauses)
        while True:
            if not s.solve():
                return "UNSAT", it, time.time() - t0, None
            model = set(l for l in s.get_model() if l > 0)
            subs = [agents[i].decode(model) for i in range(n)]
            tables = [table_from_restricted(m, R[i], subs[i]) for i in range(n)]
            X = find_efx0(n, m, tables, R)
            if X is None:
                ok, info = verify_counterexample(n, m, R, subs)
                assert ok, info
                return "SAT", it, time.time() - t0, {"R": R, "subs": subs, "relevance": info["relevance"]}
            cl = alloc_clause(n, m, agents, X)
            if not cl:
                return "UNSAT", it, time.time() - t0, None
            for c in clauses[fed:]:
                s.add_clause(c)
            fed = len(clauses)
            s.add_clause(cl)
            it += 1
            if time.time() - t0 > time_limit:
                return "TIMEOUT", it, time.time() - t0, None


def level2(time_limit=1200):
    """Pin agent a only; agents b and c each ignore one good. Cases up to the symmetries of the instance
    that fix agent a: swapping the two goods of a type (A1/A2, B1/B2, C1/C2), and the relabelling that
    swaps (b, B) with (c, C)."""
    import itertools
    swap_type = {0: 1, 1: 0, 2: 3, 3: 2, 4: 5, 5: 4, 6: 6, 7: 7}
    sigma_goods = {0: 0, 1: 1, 2: 4, 3: 5, 4: 2, 5: 3, 6: 6, 7: 7}  # B <-> C
    def images(db, dc):
        out = set()
        for fa, fb, fc in itertools.product([0, 1], repeat=3):
            def f(g):
                t = g // 2 if g < 6 else None
                if t is not None and (fa, fb, fc)[t]:
                    return swap_type[g]
                return g
            out.add((f(db), f(dc)))
            out.add((sigma_goods[f(dc)], sigma_goods[f(db)]))
        return out
    seen = set()
    out = []
    for db in range(8):
        for dc in range(8):
            key = min(images(db, dc))
            if key in seen:
                continue
            seen.add(key)
            Rb = [g for g in range(8) if g != db]
            Rc = [g for g in range(8) if g != dc]
            st, it, dt, sol = run({1: Rb, 2: Rc}, pinned={0}, time_limit=time_limit)
            line = {"pinned": ["a"], "b_ignores": NAMES[db], "c_ignores": NAMES[dc], "status": st,
                    "iters": it, "time": round(dt, 1)}
            if sol:
                line["solution"] = sol
            print(json.dumps({k: v for k, v in line.items() if k != "solution"}), flush=True)
            out.append(line)
    with open("results/monotone/amm_modify_level2.jsonl", "w") as f:
        for line in out:
            f.write(json.dumps(line) + "\n")


def main():
    if "--level2" in sys.argv:
        level2()
        return
    out = []
    # agent c (index 2, type C) ignores one good; up to the relabelling symmetry fixing c's type, the
    # cases are: an A-good (A1), a B-good (B1), a C-good (C1), x, y. (Swapping types A, B together with
    # agents a, b maps the instance to itself and fixes c, so A1 and B1 are equivalent; we run both.)
    for d in [0, 2, 4, 6, 7]:
        Rc = [g for g in range(8) if g != d]
        st, it, dt, sol = run({2: Rc}, pinned={0, 1})
        line = {"pinned": ["a", "b"], "free": "c", "c_ignores": NAMES[d], "status": st, "iters": it,
                "time": round(dt, 1)}
        if sol:
            line["solution"] = sol
        print(json.dumps({k: v for k, v in line.items() if k != "solution"}), flush=True)
        out.append(line)
    os.makedirs("results/monotone", exist_ok=True)
    with open("results/monotone/amm_modify.jsonl", "w") as f:
        for line in out:
            f.write(json.dumps(line) + "\n")


if __name__ == "__main__":
    main()
