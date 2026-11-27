"""SAT synthesis of monotone instances with bounded relevance and no EFX0 allocation.

Question per hypergraph H = (R_1, ..., R_n) on goods [m]: are there normalized monotone valuations
v_i with v_i(S) = v_i(S cap R_i) such that NO complete allocation is EFX0?

Encoding.  For every allocation X we need some i != j, g in X_j with v_i(X_j - g) > v_i(X_i). Both
arguments are disjoint subsets of R_i, so we use literals lt_i(A, B) meaning v_i(A) < v_i(B) for
disjoint A, B subsets of R_i. Only the maximal candidate sets B matter: if X_j has a good outside R_i
the candidate is X_j cap R_i, otherwise X_j - g for g in X_j (B subset B' and v(A) < v(B) imply
v(A) < v(B')). Two independent encodings of "the lt literals are realised by a monotone valuation":

  rank  (order/unary encoding of integer values): x[S][t] <=> val(S) >= t, t = 1..V-1, ladder clauses,
        val(empty) = 0, weak monotonicity x[S][t] -> x[S+g][t]; lt(A, B) -> val(A) < val(B) as V clauses.
        Sound for SAT for any V (a model gives integer values that realise every true lt). Complete with
        V = 2^r: a counterexample can be perturbed to a nondegenerate one (no-EFX0 is an open condition),
        whose ranks lie in 0..2^r - 1.
  order (strict total preorder by pairwise variables): p[S][T] <=> v(S) < v(T) for S < T, p[T][S] :=
        -p[S][T]; inclusion units S < T for S strict subset T; transitivity (both cyclic orientations of
        every triple forbidden). Exact for nondegenerate valuations, which suffice (same perturbation).

Allocation clauses: all n^m allocations ("direct"), or lazily ("cegar": solve, decode the valuations,
search for an EFX0 allocation, add its clause, repeat).

Every SAT answer is decoded to explicit integer tables and checked by brute force with the raw EFX0
definition (monotone/mono_lib.py), independent of the encoding.
"""
import sys
import os
import time
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pysat.solvers import Solver
from pysat.formula import IDPool
from mono_lib import (table_from_restricted, check_normalized_monotone, relevant_goods,
                      all_efx0, bundles_of, efx0_violation)


class AgentEnc:
    def __init__(self, R, pool, enc, V, clauses, true_lit):
        self.R = list(R)
        self.r = len(R)
        self.N = 1 << self.r
        self.pos = {g: t for t, g in enumerate(self.R)}
        self.Rmask = sum(1 << g for g in self.R)
        self.enc = enc
        self.V = V
        self.pool = pool
        self.clauses = clauses
        self.T = true_lit
        self.ltc = {}
        N = self.N
        if enc == "rank":
            # x[S][t], t = 1..V-1
            self.x = [[None] + [pool.id() for _ in range(1, V)] for _ in range(N)]
            for S in range(N):
                for t in range(1, V - 1):
                    clauses.append([-self.x[S][t + 1], self.x[S][t]])
            clauses.append([-self.x[0][1]])  # val(empty) = 0
            for S in range(N):
                for g in range(self.r):
                    if not (S >> g) & 1:
                        S2 = S | (1 << g)
                        for t in range(1, V):
                            clauses.append([-self.x[S][t], self.x[S2][t]])
        elif enc == "order":
            self.p = {}
            for S in range(N):
                for T in range(S + 1, N):
                    self.p[(S, T)] = pool.id()
            for S in range(N):
                for T in range(N):
                    if S != T and (S & T) == S:  # S strict subset of T
                        clauses.append([self.plit(S, T)])
            for a in range(N):
                for b in range(a + 1, N):
                    for c in range(b + 1, N):
                        # forbid a<b<c<a and a<c<b<a
                        clauses.append([-self.plit(a, b), -self.plit(b, c), -self.plit(c, a)])
                        clauses.append([-self.plit(a, c), -self.plit(c, b), -self.plit(b, a)])
        else:
            raise ValueError(enc)

    def plit(self, S, T):
        return self.p[(S, T)] if S < T else -self.p[(T, S)]

    def local(self, mask):
        out = 0
        for g in self.R:
            if (mask >> g) & 1:
                out |= 1 << self.pos[g]
        return out

    def lt(self, A, B):
        """Literal for v(A) < v(B), A and B disjoint local masks, B nonempty."""
        key = (A, B)
        if key in self.ltc:
            return self.ltc[key]
        if self.enc == "order":
            lit = self.plit(A, B)
        else:
            if A == 0:
                lit = self.x[B][1]
            else:
                y = self.pool.id()
                V = self.V
                cl = self.clauses
                cl.append([-y, self.x[B][1]])
                for t in range(1, V - 1):
                    cl.append([-y, -self.x[A][t], self.x[B][t + 1]])
                cl.append([-y, -self.x[A][V - 1]])
                lit = y
        self.ltc[key] = lit
        return lit

    def decode(self, model_set):
        if self.enc == "rank":
            return [sum(1 for t in range(1, self.V) if self.x[S][t] in model_set) for S in range(self.N)]
        def true(l):
            return (l in model_set) if l > 0 else (-l not in model_set)
        vals = []
        for S in range(self.N):
            vals.append(sum(1 for T in range(self.N) if T != S and true(self.plit(T, S))))
        return vals


def alloc_clause(n, m, agents, B):
    """Clause 'allocation B (list of global masks) is not EFX0'. None if it can never be violated."""
    lits = set()
    for i in range(n):
        ag = agents[i]
        A = ag.local(B[i])
        for j in range(n):
            if j == i or B[j] == 0:
                continue
            Xj = B[j]
            if Xj & ~ag.Rmask:
                C = ag.local(Xj)
                if C:
                    lits.add(ag.lt(A, C))
            else:
                if bin(Xj).count("1") == 1:
                    continue
                for g in ag.R:
                    if (Xj >> g) & 1:
                        C = ag.local(Xj & ~(1 << g))
                        lits.add(ag.lt(A, C))
    return sorted(lits)


def find_efx0(n, m, tables, R):
    """Backtracking search for an EFX0 allocation with explicit tables; pruning: a violation
    v_i(X_j - g) > v_i(X_i + all unassigned goods) is final. Returns list of masks or None."""
    owner = [0] * m
    B = [0] * n
    full = (1 << m) - 1
    # order goods by degree (most-valued first)
    order = sorted(range(m), key=lambda g: -sum(1 for i in range(n) if g in R[i]))

    def ok_partial(unassigned):
        for i in range(n):
            best_own = tables[i][B[i] | unassigned]
            for j in range(n):
                if j == i:
                    continue
                Xj = B[j]
                if Xj == 0:
                    continue
                for g in range(m):
                    if (Xj >> g) & 1 and tables[i][Xj & ~(1 << g)] > best_own:
                        return False
        return True

    def rec(k, unassigned):
        if k == m:
            return efx0_violation(n, m, tables, B) is None
        g = order[k]
        un2 = unassigned & ~(1 << g)
        for i in range(n):
            B[i] |= 1 << g
            if ok_partial(un2) and rec(k + 1, un2):
                return True
            B[i] &= ~(1 << g)
        return False

    if rec(0, full):
        return list(B)
    return None


def synth(n, m, R, enc="rank", V=None, mode="direct", solver="cadical153", verbose=False,
          time_limit=None, symmetric_first=False):
    """Returns ('SAT', tables) or ('UNSAT', info)."""
    pool = IDPool()
    clauses = []
    T = pool.id()
    clauses.append([T])
    agents = []
    for i in range(n):
        Vi = V if V is not None else (1 << len(R[i]))
        agents.append(AgentEnc(R[i], pool, enc, max(Vi, 2), clauses, T))
    t0 = time.time()
    stats = {"allocs": 0, "iters": 0}
    if mode == "direct":
        seen = set()
        for alloc in product(range(n), repeat=m):
            B = bundles_of(alloc, n)
            cl = alloc_clause(n, m, agents, B)
            if not cl:
                return ("UNSAT", {"reason": "an allocation can never be violated", "alloc": alloc})
            key = tuple(cl)
            if key not in seen:
                seen.add(key)
                clauses.append(cl)
        stats["allocs"] = len(seen)
        with Solver(name=solver, bootstrap_with=clauses) as s:
            ok = s.solve()
            if not ok:
                stats["time"] = time.time() - t0
                return ("UNSAT", stats)
            model = set(l for l in s.get_model() if l > 0)
    else:
        s = Solver(name=solver, bootstrap_with=clauses)
        fed = len(clauses)
        while True:
            stats["iters"] += 1
            if not s.solve():
                stats["time"] = time.time() - t0
                s.delete()
                return ("UNSAT", stats)
            model = set(l for l in s.get_model() if l > 0)
            subs = [agents[i].decode(model) for i in range(n)]
            tables = [table_from_restricted(m, R[i], subs[i]) for i in range(n)]
            X = find_efx0(n, m, tables, R)
            if X is None:
                s.delete()
                break
            cl = alloc_clause(n, m, agents, X)
            if not cl:
                s.delete()
                return ("UNSAT", {"reason": "an allocation can never be violated", "alloc": X})
            for c in clauses[fed:]:  # definitional clauses of new lt literals
                s.add_clause(c)
            fed = len(clauses)
            s.add_clause(cl)
            if verbose and stats["iters"] % 200 == 0:
                print(f"   cegar iter {stats['iters']}  {time.time() - t0:.1f}s", flush=True)
            if time_limit and time.time() - t0 > time_limit:
                s.delete()
                return ("TIMEOUT", stats)
    subs = [agents[i].decode(model) for i in range(n)]
    tables = [table_from_restricted(m, R[i], subs[i]) for i in range(n)]
    stats["time"] = time.time() - t0
    return ("SAT", {"subs": subs, "tables": tables, **stats})


def verify_counterexample(n, m, R, subs):
    """Independent check from explicit sub-tables: monotone, normalized, relevance within R_i,
    and no EFX0 allocation (brute force over all n^m allocations)."""
    tables = [table_from_restricted(m, R[i], subs[i]) for i in range(n)]
    for i in range(n):
        err = check_normalized_monotone(m, tables[i])
        if err:
            return False, f"agent {i}: {err}"
    rel = [relevant_goods(m, tables[i]) for i in range(n)]
    for i in range(n):
        if not set(rel[i]) <= set(R[i]):
            return False, f"agent {i} relevance {rel[i]} not within {R[i]}"
    ex = all_efx0(n, m, tables, limit=1)
    if ex:
        return False, f"EFX0 allocation exists: {ex[0]}"
    return True, {"relevance": [len(x) for x in rel], "relevant": rel}


if __name__ == "__main__":
    # smoke test: n = 3, m = 8, everybody values everything
    n, m = 3, 8
    R = [list(range(8))] * 3
    for V in (8, 16):
        res = synth(n, m, R, enc="rank", V=V)
        print("V =", V, res[0], {k: v for k, v in res[1].items() if k not in ("subs", "tables")})
        if res[0] == "SAT":
            print("  verify:", verify_counterexample(n, m, R, res[1]["subs"]))


# ---------------------------------------------------------------------------------------------------------
# Fast inner search (C, monotone/efx0search.c via ctypes). Every allocation it returns is re-checked here
# with the raw definition on the agents' subset tables before use.
import ctypes
import subprocess

_LIB = None


def _lib():
    global _LIB
    if _LIB is None:
        here = os.path.dirname(os.path.abspath(__file__))
        src = os.path.join(here, "efx0search.c")
        bdir = os.path.join(here, "_build")
        os.makedirs(bdir, exist_ok=True)
        so = os.path.join(bdir, "efx0search.so")
        if not os.path.exists(so) or os.path.getmtime(so) < os.path.getmtime(src):
            tmp = so + f".{os.getpid()}"
            subprocess.check_call(["gcc", "-O2", "-shared", "-fPIC", "-o", tmp, src])
            os.replace(tmp, so)
        _LIB = ctypes.CDLL(so)
        _LIB.find_efx0.restype = ctypes.c_int
    return _LIB


def efx0_local_ok(n, m, R, subs, owner):
    """Raw EFX0 check of a complete allocation (owner list) from subset tables."""
    pos = [{g: t for t, g in enumerate(R[i])} for i in range(n)]
    bundles = [[g for g in range(m) if owner[g] == a] for a in range(n)]

    def v(i, goods):
        s = 0
        for g in goods:
            if g in pos[i]:
                s |= 1 << pos[i][g]
        return subs[i][s]

    for i in range(n):
        own = v(i, bundles[i])
        for j in range(n):
            if j != i:
                for g in bundles[j]:
                    if v(i, [h for h in bundles[j] if h != g]) > own:
                        return False
    return True


def find_efx0_fast(n, m, R, subs):
    """Returns bundles as bitmasks (like find_efx0) or None."""
    lib = _lib()
    pos = (ctypes.c_int * (n * m))(*[-1] * (n * m))
    for i in range(n):
        for t, g in enumerate(R[i]):
            pos[i * m + g] = t
    offs, flat = [], []
    for i in range(n):
        offs.append(len(flat))
        flat.extend(int(x) for x in subs[i])
    off = (ctypes.c_int * n)(*offs)
    vals = (ctypes.c_int * len(flat))(*flat)
    order = sorted(range(m), key=lambda g: -sum(1 for i in range(n) if g in R[i]))
    ordr = (ctypes.c_int * m)(*order)
    owner = (ctypes.c_int * m)()
    r = lib.find_efx0(n, m, pos, off, vals, ordr, owner)
    if r < 0:
        raise ValueError("instance too large for efx0search.c")
    if r == 0:
        return None
    own = list(owner)
    assert efx0_local_ok(n, m, R, subs, own), "C search returned a non-EFX0 allocation"
    B = [0] * n
    for g, a in enumerate(own):
        B[a] |= 1 << g
    return B
