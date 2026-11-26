"""Exhaustive ordinal certification of Conjecture DYN (k4/girth.md section 5) on small k = 4 cores, by covering the
profile space with classes of profiles on which the algorithm runs identically.

Statement certified, per core hypergraph H: for EVERY strict core profile (strict balanced order types, K4.OT, with
p + q < s + t for two private goods; the domains of k4/check4.py), SOME labeling makes the pipeline succeed:
    LSS's Algorithm 2 with the G1 repair, then dynamic parking with envy-cycle rotation (k4/girth.md section 5).

Written independently of lss.py: every decision of the pipeline is a comparison v_i(A) vs v_i(B) of two sets of one
agent's goods; it is answered by an oracle from a representative profile and RECORDED.  Such a comparison depends only
on A minus B and B minus A, which are disjoint, so on the agent's order type.  All profiles that agree with the
representative on every recorded comparison form a product of per-agent type sets (a box) and run identically, so the
run's outcome holds on the whole box.  Covering: a worklist of (box, remaining labelings); run the first labeling on a
representative of the box, record its class C; if it succeeds, C is certified; if not, C goes on with the remaining
labelings; the rest of the box is split into disjoint boxes and goes on with all labelings.  A box with no labeling left
is a counterexample candidate: its representative is re-checked with the independent implementation lss.pipeline-style
code (lss.Run.alg2_safe + lss.park_dynamic_ec) over every labeling.

    python3 k4/girth/dyncert.py N [FILE_GLOB_PART] [--limit=K] [--jobs=J]
writes results/k4_girth_dyncert_{N}.log: per core the number of profiles, runs, boxes, and any counterexample.
"""
import gzip
import itertools
import json
import multiprocessing as mp
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)

BUDGET = 200000          # node budget of the parking search (as lss.park_dynamic_ec)
CYCLE_CAP = 50           # at most this many envy cycles tried at a node (as lss.envy_cycles)


class Core:
    """hypergraph + per-agent type domains, with sign masks for the comparisons"""

    def __init__(self, sets, m, doms):
        self.n, self.m = len(sets), m
        self.sets = [sorted(S) for S in sets]
        self.R = [frozenset(S) for S in sets]
        self.edge = [frozenset(i for i in range(self.n) if g in self.R[i]) for g in range(m)]
        self.doms = doms                                   # doms[i]: list of dicts good -> value
        self.pos = [{g: k for k, g in enumerate(S)} for S in self.sets]
        # pair index: canonical (A, B) disjoint nonempty local bitmasks with A < B
        self.pidx = []
        self.plus = []                                     # plus[i][p] = bitmask of types with v(A) > v(B)
        for i, S in enumerate(self.sets):
            d = len(S)
            idx = {}
            for A in range(1, 1 << d):
                for B in range(A + 1, 1 << d):
                    if A & B == 0:
                        idx[(A, B)] = len(idx)
            self.pidx.append(idx)
            pl = [0] * len(idx)
            for t, vals in enumerate(doms[i]):
                vv = [vals[g] for g in S]
                for (A, B), p in idx.items():
                    a = sum(vv[k] for k in range(d) if A >> k & 1)
                    b = sum(vv[k] for k in range(d) if B >> k & 1)
                    assert a != b
                    if a > b:
                        pl[p] |= 1 << t
            self.plus.append(pl)
        self.full = [(1 << len(D)) - 1 for D in doms]


class Run:
    """one run of the pipeline on the representative profile `rep` (type index per agent) and labeling `lab`, with
    every comparison recorded"""

    def __init__(self, C, rep, lab):
        self.C, self.rep, self.lab = C, rep, lab
        self.vals = [C.doms[i][rep[i]] for i in range(C.n)]
        self.rec = [dict() for _ in range(C.n)]           # agent -> {pair index: sign of canonical pair}
        self.count = 0

    def local(self, i, S):
        p = self.C.pos[i]
        x = 0
        for g in S:
            if g in p:
                x |= 1 << p[g]
        return x

    def cmp(self, i, S, T):
        """sign of v_i(S) - v_i(T), recorded"""
        a, b = self.local(i, S), self.local(i, T)
        A, B = a & ~b, b & ~a
        if A == 0 and B == 0:
            return 0
        if A == 0:
            return -1
        if B == 0:
            return 1
        v = self.vals[i]
        S_ = self.C.sets[i]
        va = sum(v[S_[k]] for k in range(len(S_)) if A >> k & 1)
        vb = sum(v[S_[k]] for k in range(len(S_)) if B >> k & 1)
        s = 1 if va > vb else -1
        if A < B:
            self.rec[i][self.C.pidx[i][(A, B)]] = s
        else:
            self.rec[i][self.C.pidx[i][(B, A)]] = -s
        return s

    # ---- predicates
    def envied(self, X, j):
        return any(self.cmp(i, X[j], X[i]) > 0 for i in range(self.C.n) if i != j)

    def efx0(self, X):
        n = self.C.n
        for i in range(n):
            for j in range(n):
                if i == j or not X[j]:
                    continue
                for g in X[j]:
                    if self.cmp(i, X[j] - {g}, X[i]) > 0:
                        return False
        return True

    # ---- Algorithm 2 with the G1 repair
    def fixprop3(self, X, U):
        C = self.C
        while True:
            cand = [j for j in range(C.n) if any(self.cmp(j, {e}, X[j]) > 0 for e in sorted(U & C.R[j]))]
            if not cand:
                return
            j = max(cand, key=lambda a: self.lab[a])
            es = sorted(U & C.R[j])
            best = es[0]
            for e in es[1:]:
                if self.cmp(j, {e}, {best}) > 0:
                    best = e
            U |= X[j]
            X[j] = frozenset([best])
            U.discard(best)

    def alg2_safe(self, X, U):
        C = self.C
        self.fixprop3(X, U)
        stuck = set()
        while True:
            cand = [i for i in range(C.n) if i not in stuck and self.envied(X, i)
                    and self.cmp(i, U & C.R[i], X[i]) > 0]
            if not cand:
                break
            i = max(cand, key=lambda a: self.lab[a])
            Ui = sorted(U & C.R[i])
            best = None
            for k in range(len(Ui), 0, -1):
                for T in itertools.combinations(Ui, k):
                    T = frozenset(T)
                    if self.cmp(i, T, X[i]) <= 0:
                        continue
                    Y = list(X)
                    Y[i] = T
                    if self.efx0(Y) and (best is None or self.cmp(i, T, best) > 0):
                        best = T
            if best is None:
                stuck.add(i)
                continue
            U |= X[i]
            X[i] = best
            U -= best
            self.fixprop3(X, U)
            stuck = set()

    # ---- dynamic parking with envy-cycle rotation
    def cycles(self, Y):
        n = self.C.n
        succ = [[b for b in range(n) if b != a and self.cmp(a, Y[b], Y[a]) > 0] for a in range(n)]
        out = []

        def dfs(start, a, path, on):
            for b in succ[a]:
                if b == start:
                    out.append(list(path))
                    if len(out) >= CYCLE_CAP:
                        return
                elif b > start and b not in on:
                    on.add(b)
                    path.append(b)
                    dfs(start, b, path, on)
                    path.pop()
                    on.discard(b)
                if len(out) >= CYCLE_CAP:
                    return

        for s in range(n):
            dfs(s, s, [s], {s})
            if len(out) >= CYCLE_CAP:
                break
        return out

    def park(self, X, U):
        seen = set()
        C = self.C

        def rec(Y, left):
            if not left:
                return True
            key = (tuple(Y), left)
            if key in seen:
                return False
            seen.add(key)
            self.count += 1
            if self.count > BUDGET:
                return False
            N = [u for u in range(C.n) if not self.envied(Y, u)]
            for g in sorted(left, key=lambda h: (-len(C.edge[h]), h)):
                for u in N:
                    Z = list(Y)
                    Z[u] = Y[u] | {g}
                    if self.efx0(Z) and rec(Z, left - {g}):
                        return True
            if not N:
                for cyc in self.cycles(Y):
                    Z = list(Y)
                    for t, a in enumerate(cyc):
                        Z[a] = Y[cyc[(t + 1) % len(cyc)]]
                    if rec(Z, left):
                        return True
            return False

        return rec(list(X), frozenset(U))

    def go(self):
        C = self.C
        X = [frozenset() for _ in range(C.n)]
        U = set(range(C.m))
        self.alg2_safe(X, U)
        if not self.efx0(X):
            return False
        return self.park(X, U)

    def box(self, box):
        """the class: per agent, the types of `box` that agree with every recorded comparison"""
        out = []
        for i in range(self.C.n):
            mask = box[i]
            for p, s in self.rec[i].items():
                mask &= self.C.plus[i][p] if s > 0 else ~self.C.plus[i][p]
            out.append(mask)
        return tuple(out)


def labelings(C):
    out = []
    for z in range(C.n):
        nb = sorted(set().union(*(C.edge[g] for g in C.R[z])) - {z})
        rest = [a for a in range(C.n) if a != z and a not in nb]
        for p in itertools.permutations(nb):
            for q in itertools.permutations(rest):
                lab = [None] * C.n
                lab[z] = 0
                for t, a in enumerate(p):
                    lab[a] = 1 + t
                for t, a in enumerate(q):
                    lab[a] = 1 + len(p) + t
                out.append(lab)
    # default orders first (one per vertex 0), then the others
    return sorted(out, key=lambda L: (0 if all(L[a] < L[b] for a in range(C.n) for b in range(C.n)
                                               if a < b and L[a] != 0 and L[b] != 0) else 1))


def lowbit_index(mask):
    return (mask & -mask).bit_length() - 1


def popcount(x):
    return bin(x).count('1')


def certify(task):
    name, sets, m = task
    sys.path.insert(0, HERE)
    from sources import domains
    t0 = time.time()
    doms = domains(sets, m)
    C = Core(sets, m, doms)
    L = labelings(C)
    work = [(tuple(C.full), 0)]                            # (box, index of the next labeling to try)
    runs = 0
    cex = []
    total = 1
    for D in doms:
        total *= len(D)
    covered = 0
    while work:
        box, li = work.pop()
        if any(b == 0 for b in box):
            continue
        if li >= len(L):
            rep = [lowbit_index(b) for b in box]
            cex.append(rep)
            continue
        rep = [lowbit_index(b) for b in box]
        r = Run(C, rep, L[li])
        ok = r.go()
        runs += 1
        cls = r.box(box)
        assert all(cls[i] >> rep[i] & 1 for i in range(C.n))
        if ok:
            size = 1
            for x in cls:
                size *= popcount(x)
            covered += size
        else:
            work.append((cls, li + 1))
        # the rest of the box, split into disjoint boxes, with every labeling still to try from li
        prefix = list(cls)
        for a in range(C.n):
            rest = box[a] & ~cls[a]
            if rest:
                nb = tuple(prefix[:a]) + (rest,) + tuple(box[a + 1:])
                work.append((nb, li))
    return dict(name=name, profiles=total, covered=covered, runs=runs, cex=cex, time=time.time() - t0,
                sets=sets, m=m)


def verify_cex(sets, m, rep):
    """re-check a counterexample candidate with lss.py (independent code), every labeling"""
    from sources import domains
    from lss import Inst, Run as LRun, park_dynamic_ec, is_efx0, labels
    doms = domains(sets, m)
    ds = [doms[i][rep[i]] for i in range(len(sets))]
    I = Inst([sorted(d) for d in ds], [[d[g] for g in sorted(d)] for d in ds], m)
    ok = 0
    labs = []
    for z in range(I.n):
        nb = I.neighbours(z)
        rest = [a for a in range(I.n) if a != z and a not in nb]
        for p in itertools.permutations(nb):
            for q in itertools.permutations(rest):
                labs.append(labels(I, z, p, q))
    for lab in labs:
        r = LRun(I, lab)
        r.alg2_safe()
        if is_efx0(I, r.X) and park_dynamic_ec(I, r.X, r.U) is not None:
            ok += 1
    return I, ok, len(labs)


def main():
    n = int(sys.argv[1])
    part = sys.argv[2] if len(sys.argv) > 2 and not sys.argv[2].startswith('--') else ''
    limit = None
    jobs = mp.cpu_count()
    for a in sys.argv[2:]:
        if a.startswith('--limit='):
            limit = int(a[8:])
        if a.startswith('--jobs='):
            jobs = int(a[7:])
    from sources import cores
    tasks = [('%s#m%d#%d' % (f, m, idx), sets, m) for f, idx, sets, m in cores(n) if part in f]
    if limit:
        tasks = tasks[:limit]
    print('$ python3 k4/girth/dyncert.py', *sys.argv[1:], '(%d cores, %d jobs)' % (len(tasks), jobs), flush=True)
    t0 = time.time()
    tot = dict(profiles=0, covered=0, runs=0, cex=0, cores=0)
    with mp.Pool(jobs) as pool:
        for res in pool.imap_unordered(certify, tasks):
            tot['cores'] += 1
            tot['profiles'] += res['profiles']
            tot['covered'] += res['covered']
            tot['runs'] += res['runs']
            ncx = len(res['cex'])
            tot['cex'] += ncx
            status = 'CERTIFIED' if ncx == 0 and res['covered'] == res['profiles'] else 'NOT CERTIFIED'
            print('%-28s profiles %12d covered %12d runs %8d boxes-without-labeling %d %.1fs %s'
                  % (res['name'], res['profiles'], res['covered'], res['runs'], ncx, res['time'], status), flush=True)
            for rep in res['cex'][:3]:
                I, ok, nl = verify_cex(res['sets'], res['m'], rep)
                print('   counterexample candidate', I, 'type indices', rep, '| lss.py: %d of %d labelings complete'
                      % (ok, nl), flush=True)
    print('TOTAL', tot, '%.0fs' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
