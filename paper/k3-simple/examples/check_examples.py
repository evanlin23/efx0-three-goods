#!/usr/bin/env python3
"""Recompute every example and every computed number of paper/k3-simple (long.tex and main.tex).

    python3 paper/k3-simple/examples/check_examples.py          (from the repository root, or from anywhere)

Exit status 0 iff every check passes. One process, no pools; about 10 seconds. Output: check_output.txt (same folder)
is a copy of what this script prints.

This script is an independent implementation of the definitions of the paper (states, needs, validity, free agents,
the need digraph, exposure, valid absorbers, completions) and of algorithm DE (Draft and Exchange), written from the
paper's text. Every claim of the proofs that DE relies on is an assert. Allocations are checked against the raw
EFX0 definition with exact integer arithmetic. It cross-checks its results with `k3/simplify/po/hall/hall.py`.

Sections (as printed):
  [1] Example "EFX but not EFX0" and the failure of serial dictatorship at k = 3 (Introduction).
  [2] The n = 6, m = 10 instance (Overview; Section "A worked example"): the draft state, the failed absorbers,
      the absence of short moves, every dominating valid state, DE's exchange cycle, the completion, raw EFX0.
  [3] The n = 2, m = 3 example: protecting goods cannot be dropped (Remark after the Improvement Lemma).
  [4] The n = 6, m = 8 instance with shared protecting goods (Proposition "when short moves are not enough").
  [5] The family of rings: every rainbow cycle uses k exposure arcs (Remark), for k <= 4.
  [6] Limits of the shape (Proposition "limits"), by enumerating every allocation.
  [7] Re-run of the small rows of the evidence table with hall.py, and the same sets with this script's own code.
  [8] DE on random instances (evidence; peeling included; ties, top-heavy agents, fewer than three goods).
"""
import itertools
import os
import random
import sys
import time
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
HALL = os.path.join(ROOT, 'k3', 'simplify', 'po', 'hall')

FAILS = []
LOG = []


def out(s=''):
    print(s, flush=True)
    LOG.append(s)


def check(cond, msg):
    out(('  ok    ' if cond else '  FAIL  ') + msg)
    if not cond:
        FAILS.append(msg)


# ============================================================================================ raw definitions
def is_efx0(v, X):
    """v[i]: dict good -> value (missing = 0); X: list of sets (bundles). Raw definition, exact arithmetic."""
    n = len(X)
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in X[i])
        for j in range(n):
            if j == i or not X[j]:
                continue
            tot = sum(v[i].get(g, 0) for g in X[j])
            if tot - min(v[i].get(g, 0) for g in X[j]) > own:
                return False
    return True


def is_efx(v, X):
    """EFX: only goods the envious agent values positively may be removed."""
    n = len(X)
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in X[i])
        for j in range(n):
            if j == i:
                continue
            tot = sum(v[i].get(g, 0) for g in X[j])
            for h in X[j]:
                if v[i].get(h, 0) > 0 and tot - v[i][h] > own:
                    return False
    return True


def vals_from_rank(rank, trip=(4, 3, 2)):
    return [dict(zip(r, trip)) for r in rank]


# ============================================================================================ states
# rank[i] = (a_i, b_i, c_i); a state is a tuple of options: 0 nothing, 1 {a}, 2 {b}, 3 {c}, 4 the pair {b, c}
UT = {0: 0, 3: 1, 2: 2, 1: 3, 4: 4}       # utility u: nothing 0 < c 1 < b 2 < a 3 < pair 4


def held(r, o):
    return () if o == 0 else ((r[o - 1],) if o < 4 else (r[1], r[2]))


def needs(r, o):
    """N_i: goods ranked above the single good held; all three if nothing; none for a pair holder"""
    return set(r) if o == 0 else (set() if o == 4 else set(r[:o - 1]))


def disjoint(rank, opt):
    gs = [g for i, o in enumerate(opt) for g in held(rank[i], o)]
    return len(gs) == len(set(gs))


class State:
    def __init__(self, rank, m, opt):
        self.rank, self.m, self.opt, self.n = rank, m, tuple(opt), len(rank)
        assert disjoint(rank, opt)
        self.Y = [held(rank[i], o) for i, o in enumerate(opt)]
        self.holder = {g: i for i in range(self.n) for g in self.Y[i]}
        self.U = {i for i in range(self.n) if opt[i] == 4}
        self.N = [needs(rank[i], o) for i, o in enumerate(opt)]
        self.NA = set().union(*self.N) if self.n else set()
        self.J = set(range(m)) - set(self.holder)
        # valid: every needed good is the only good of an agent outside U
        self.valid = all(g in self.holder and opt[self.holder[g]] in (1, 2, 3) for g in self.NA)
        self.F = [i for i in range(self.n) if i not in self.U and (opt[i] == 0 or self.Y[i][0] not in self.NA)]

    def y(self, i):
        assert self.opt[i] in (1, 2, 3)
        return self.Y[i][0]

    def exposed(self, o):
        W = self.J | set(self.Y[o])
        return [x for x in range(self.n) if x != o and self.opt[x] == 1
                and self.rank[x][1] in W and self.rank[x][2] in W]

    def absorber_bf(self, o):
        """the definition, by brute force: None if o is not a valid absorber, else a smallest hitting set H"""
        if not (o in self.F or o in self.U):
            return None
        sets = []
        for x in self.exposed(o):
            s = frozenset(g for g in self.rank[x][1:] if g in self.J)
            if not s:
                return None
            sets.append(s)
        lim = len(self.F) - (1 if o in self.F else 0)
        univ = sorted(set().union(*sets)) if sets else []
        for k in range(0, min(lim, len(univ)) + 1):
            for H in itertools.combinations(univ, k):
                if all(s & set(H) for s in sets):
                    return list(H)
        return None

    def completable_bf(self):
        return [(o, self.absorber_bf(o)) for o in range(self.n) if self.absorber_bf(o) is not None]

    def needers(self, g):
        return [j for j in range(self.n) if j not in self.U and g in self.N[j]]

    def out_arcs(self, j):
        """need digraph D: j -> j' when j (not in U) holds a single good that j' (not in U) needs"""
        if j in self.U or self.opt[j] == 0:
            return []
        return self.needers(self.y(j))

    def completion(self, o, H):
        """bundles: H one good each to the free agents other than o (index order), the rest of J to o"""
        X = [set(self.Y[i]) for i in range(self.n)]
        others = [f for f in self.F if f != o]
        assert len(H) <= len(others)
        for g, f in zip(sorted(H), others):
            X[f].add(g)
        X[o] |= self.J - set(H)
        return X


def dominates(o2, o1):
    return all(UT[a] >= UT[b] for a, b in zip(o2, o1)) and any(UT[a] > UT[b] for a, b in zip(o2, o1))


def all_states(rank, m):
    n = len(rank)
    res = []
    for opt in itertools.product(range(5), repeat=n):
        if disjoint(rank, opt):
            res.append(opt)
    return res


def valid_states(rank, m):
    return [s for s in all_states(rank, m) if State(rank, m, s).valid]


# ============================================================================================ the exchanges
def apply_cycle(st, cyc, expo):
    """exchange along the cycle cyc = (w_0, ..., w_{k-1}): if the arc w_t -> w_{t+1} is an exposure arc (w_t in expo),
    w_{t+1} takes its pair; else w_{t+1} takes y_{w_t} alone. Returns the new option tuple, or None if two agents
    would hold the same good."""
    o2 = list(st.opt)
    k = len(cyc)
    for t in range(k):
        u, w = cyc[t], cyc[(t + 1) % k]
        if u in expo:
            o2[w] = 4
        else:
            o2[w] = st.rank[w].index(st.y(u)) + 1
    return tuple(o2) if disjoint(st.rank, o2) else None


def walk_to_cycle(succ, start):
    path, seen = [start], {start}
    while succ(path[-1]) not in seen:
        path.append(succ(path[-1]))
        seen.add(path[-1])
    return path[path.index(succ(path[-1])):]


def p2_violators(st):
    return [x for x in range(st.n) if st.opt[x] == 1 and st.rank[x][1] in st.J and st.rank[x][2] in st.J]


def pair_chain(st, x):
    """Lemma (need cycle; pair chain): x holds a_x with b_x, c_x junk. Walk need arcs from x; a repeat gives a need
    cycle, otherwise x takes its pair and a_x moves along the path."""
    path = [x]
    while st.out_arcs(path[-1]):
        w = st.out_arcs(path[-1])[0]
        if w in path:
            return apply_cycle(st, path[path.index(w):], set()), 'need cycle', 0
        path.append(w)
    o2 = list(st.opt)
    o2[x] = 4
    for t in range(1, len(path)):
        o2[path[t]] = st.rank[path[t]].index(st.y(path[t - 1])) + 1
    return tuple(o2), 'pair chain', 0


def stop_test(st):
    """under (P2): every agent holds a pair -> (0, []); a free agent holding nothing -> (o, []) (Lemma: an agent
    holding nothing absorbs); a free o with |H_o| <= |F| - 1 -> (o, H_o) (Lemma: protecting goods are forced).
    Returns None if no free agent is a valid absorber. Asserts the two lemmas."""
    if len(st.U) == st.n:
        return 0, []
    for o in st.F:
        if st.opt[o] == 0:
            assert not st.exposed(o)
            return o, []
        g = st.y(o)
        H = set()
        for x in st.exposed(o):
            bx, cx = st.rank[x][1], st.rank[x][2]
            assert g in (bx, cx)
            h = cx if bx == g else bx
            assert h in st.J
            H.add(h)
        if len(H) <= len(st.F) - 1:
            return o, sorted(H)
    return None


def protecting(st, o):
    """H_o as a dict junk good -> first exposed agent with that protecting good"""
    g = st.y(o)
    H = {}
    for x in st.exposed(o):
        bx, cx = st.rank[x][1], st.rank[x][2]
        H.setdefault(cx if bx == g else bx, x)
    return H


def exchange_cycle(st, trace=None):
    """Lemma (exchange cycle): distinct representatives h_o in H_o greedily (smallest good first, free agents in index
    order); sigma(o) = x_o for free o, sigma(j) = first out-neighbour in D otherwise; a cycle of sigma."""
    used, xo, rep = set(), {}, {}
    for o in st.F:
        H = protecting(st, o)
        assert len(H) >= len(st.F)
        h = min(g for g in H if g not in used)
        used.add(h)
        xo[o], rep[o] = H[h], h
    nonU = [i for i in range(st.n) if i not in st.U]

    def succ(j):
        s = xo[j] if j in xo else st.out_arcs(j)[0]
        assert s != j and s not in st.U
        return s
    cyc = walk_to_cycle(succ, nonU[0])
    expo = {u for u in cyc if u in xo}
    if trace is not None:
        trace.update(rep=rep, xo=xo, cyc=cyc, expo=expo)
    return apply_cycle(st, cyc, expo), ('exchange cycle' if expo else 'need cycle'), len(expo)


def improve(st, trace=None):
    """one step of DE's loop; returns (new options, kind, exposure arcs used) or ('stop', o, H)"""
    p2 = p2_violators(st)
    if p2:
        return pair_chain(st, p2[0])
    s = stop_test(st)
    if s is not None:
        return ('stop',) + s
    if not st.F:
        nonU = [i for i in range(st.n) if i not in st.U]
        assert nonU
        return apply_cycle(st, walk_to_cycle(lambda j: st.out_arcs(j)[0], nonU[0]), set()), 'need cycle', 0
    return exchange_cycle(st, trace)


def serial_dictatorship(rank):
    used, opt = set(), []
    for r in rank:
        o = next((t + 1 for t, g in enumerate(r) if g not in used), 0)
        if o:
            used.add(r[o - 1])
        opt.append(o)
    return tuple(opt)


def de_core(rank, m, stats=None, bf=False, start=None):
    """DE on a core (every agent ranks exactly three goods): serial dictatorship in index order (or the valid state
    `start`), then exchanges until the stop test holds, then the completion. Returns (bundles, absorber, number of
    exchanges, history)."""
    opt = serial_dictatorship(rank) if start is None else tuple(start)
    hist = [opt]
    steps = 0
    while True:
        st = State(rank, m, opt)
        assert st.valid
        r = improve(st)
        if r[0] == 'stop':
            _, o, H = r
            if bf:
                assert st.absorber_bf(o) is not None and len(st.absorber_bf(o)) == len(H)
            X = st.completion(o, H)
            return X, o, steps, hist
        o2, kind, ex = r
        assert o2 is not None
        st2 = State(rank, m, o2)
        assert st2.valid and dominates(o2, opt)
        assert sum(UT[a] for a in o2) > sum(UT[a] for a in opt)
        if stats is not None:
            stats[kind] += 1
            if kind == 'exchange cycle':
                stats['exposure arcs %d' % ex] += 1
        opt = o2
        hist.append(opt)
        steps += 1
        assert steps <= 4 * len(rank)


def de(v, n, m, stats=None):
    """DE on a general instance: v[i] dict good -> value (positive entries only matter). Returns the bundles."""
    A, G = list(range(n)), set(range(m))
    X = [set() for _ in range(n)]
    while len(A) >= 2:                                              # step 1: peel by rule R1
        pick = None
        for i in A:
            rel = sorted((g for g in G if v[i].get(g, 0) > 0), key=lambda g: (-v[i][g], g))
            if not rel:
                pick = (i, None)
                break
            if sum(v[i][g] for g in rel[1:]) <= v[i][rel[0]]:
                pick = (i, rel[0])
                break
        if pick is None:
            break
        i, p = pick
        A.remove(i)
        if p is not None:
            X[i] = {p}
            G.discard(p)
        if stats is not None:
            stats['peeled'] += 1
    if len(A) == 1:
        X[A[0]] = set(G)
        return X
    goods = sorted(G)
    idx = {g: k for k, g in enumerate(goods)}
    rank = []
    for i in A:
        rel = sorted((g for g in G if v[i].get(g, 0) > 0), key=lambda g: (-v[i][g], g))
        assert len(rel) == 3 and v[i][rel[0]] < v[i][rel[1]] + v[i][rel[2]]      # Lemma "when R1 applies to nobody"
        rank.append(tuple(idx[g] for g in rel))
    Xc, o, steps, _ = de_core(rank, len(goods), stats)
    if stats is not None:
        stats['cores'] += 1
        stats['max exchanges'] = max(stats['max exchanges'], steps)
        stats['runs with an exchange'] += steps > 0
    for k, i in enumerate(A):
        X[i] = {goods[g] for g in Xc[k]}
    return X


def simple_cycles(succs, nodes):
    """all simple cycles of a small digraph, each once (started at its smallest vertex)"""
    res = []
    for s in nodes:
        stack = [(s, [s])]
        while stack:
            u, path = stack.pop()
            for w in succs(u):
                if w == s:
                    res.append(list(path))
                elif w > s and w not in path:
                    stack.append((w, path + [w]))
    return res


def exchange_digraph(st):
    """need arcs, and exposure arcs o -> x (o free holding a good, x exposed for o) labelled by x's junk good"""
    label = {}
    for o in st.F:
        if st.opt[o] != 0:
            for h, x in [(h, x) for x in st.exposed(o) for h in
                         [st.rank[x][2] if st.rank[x][1] == st.y(o) else st.rank[x][1]] if h in st.J]:
                label[(o, x)] = h
    nonU = [i for i in range(st.n) if i not in st.U]

    def succs(u):
        return sorted(set(st.out_arcs(u)) | {x for (o, x) in label if o == u})
    return nonU, succs, label


def cycle_report(st):
    nodes, succs, label = exchange_digraph(st)
    rainbow, nonrainbow = [], []
    for c in simple_cycles(succs, nodes):
        arcs = [(c[t], c[(t + 1) % len(c)]) for t in range(len(c))]
        labs = [label[a] for a in arcs if a in label and a[1] not in st.out_arcs(a[0])]
        (rainbow if len(labs) == len(set(labs)) else nonrainbow).append((c, len(labs)))
    return rainbow, nonrainbow


def short_moves(st):
    """need cycles, pair chains, and cycles with exactly one exposure arc (the short moves)"""
    rainbow, _ = cycle_report(st)
    return [c for c in rainbow if c[1] <= 1], p2_violators(st)


# ============================================================================================ [1]
def section1():
    out('[1] Introduction: EFX but not EFX0; serial dictatorship at k = 3')
    a, b, c = 0, 1, 2
    v = [{a: 3, b: 2}, {c: 1}]
    X = [{b}, {a, c}]
    check(is_efx(v, X) and not is_efx0(v, X), 'X1 = {b}, X2 = {a, c} is EFX and not EFX0')
    check(sum(v[0][g] for g in [a]) == 3 > 2, 'removing c from X2 leaves {a}, worth 3 > 2 to agent 1')
    check(is_efx0(v, [{a}, {b, c}]), 'X1 = {a}, X2 = {b, c} is EFX0')
    # serial dictatorship: agent 1 values a, b, c at 4, 3, 2; agent 2 values only d
    v = [{0: 4, 1: 3, 2: 2}, {3: 1}]
    check(not is_efx0(v, [{0}, {1, 2, 3}]), 'agent 1 takes a, the last agent takes {b, c, d}: not EFX0 (5 > 4)')
    check(is_efx0(v, de(v, 2, 4)), 'DE on the same instance is EFX0 (agent 2 is peeled first)')


# ============================================================================================ [2]
NAMES6 = ['x1', "x1'", 'x2', "x2'", 'o1', 'o2']
RANK6 = [(0, 4, 6), (1, 4, 7), (2, 5, 8), (3, 5, 9), (2, 3, 4), (0, 1, 5)]


def section2():
    out('[2] The n = 6, m = 10 instance (goods g0..g9; agents x1, x1\', x2, x2\', o1, o2 in this order)')
    rank, m = RANK6, 10
    v = vals_from_rank(rank)
    # peeling: R1 applies to nobody (4 < 3 + 2 for everyone), every good is valued by someone
    check(all(4 < 3 + 2 for _ in rank) and set().union(*map(set, rank)) == set(range(m)),
          'strictly balanced (4 < 3 + 2): rule R1 applies to nobody; every good is valued')
    S = serial_dictatorship(rank)
    check(S == (1, 1, 1, 1, 3, 3), 'serial dictatorship in index order: x\'s take their tops, o1 takes g4 (its c), o2 takes g5 (its c)')
    st = State(rank, m, S)
    check(st.valid and st.NA == {0, 1, 2, 3} and st.J == {6, 7, 8, 9} and st.F == [4, 5] and not st.U,
          'valid; NA = {g0, g1, g2, g3}; J = {g6, g7, g8, g9}; F = {o1, o2}')
    check(sorted(st.exposed(4)) == [0, 1] and sorted(protecting(st, 4)) == [6, 7],
          'E_o1 = {x1, x1\'}, H_o1 = {g6, g7}')
    check(sorted(st.exposed(5)) == [2, 3] and sorted(protecting(st, 5)) == [8, 9],
          'E_o2 = {x2, x2\'}, H_o2 = {g8, g9}')
    check(not st.completable_bf(), 'not completable (definition, brute force over absorbers and hitting sets)')
    check(stop_test(st) is None and not p2_violators(st), '(P2) holds and the stop test fails (|H_o| = 2 = |F|)')
    # every completion of S (absorber o1 or o2, H of size <= 1 to the other) fails the raw EFX0 check
    comps = []
    for o in st.F:
        for H in [()] + [(h,) for h in sorted(st.J)]:
            comps.append(st.completion(o, list(H)))
    check(len(comps) == 10 and not any(is_efx0(v, X) for X in comps), 'all 10 completions of S fail raw EFX0')
    X = st.completion(4, [6])
    viol = sum(v[1].get(g, 0) for g in X[4]) - min(v[1].get(g, 0) for g in X[4])
    check(X[4] == {4, 7, 8, 9} and viol == 5 and sum(v[1].get(g, 0) for g in X[1]) == 4,
          'absorber o1 with H = {g6}: X_o1 = {g4, g7, g8, g9}, x1\' values it at 5 without g8, holds 4')
    # no short move
    sm, p2 = short_moves(st)
    Dcyc = [c for c in sm if c[1] == 0]
    check(not sm and not p2, 'no need cycle, no pair chain, no cycle with one exposure arc')
    rainbow, nonrainbow = cycle_report(st)
    check(len(rainbow) == 4 and all(c[1] == 2 for c in rainbow) and not nonrainbow,
          'the exchange digraph has 4 cycles, each rainbow with 2 exposure arcs')
    # every valid dominating state
    dom = [s for s in valid_states(rank, m) if dominates(s, S)]
    check(len(dom) == 4, f'exactly 4 valid states dominate S (found {len(dom)})')
    check(all(sum(1 for o in s if o == 4) == 2 for s in dom), 'each gives pairs to exactly two agents')
    check(all(State(rank, m, s).completable_bf() for s in dom), 'all 4 are completable')
    for s in sorted(dom):
        out('        dominating: ' + ', '.join(f'{NAMES6[i]}:{["-", "a", "b", "c", "pair"][o]}' for i, o in enumerate(s)))
    # DE's step: representatives, sigma, cycle
    tr = {}
    o2, kind, ex = exchange_cycle(st, tr)
    check(tr['rep'] == {4: 6, 5: 8} and tr['xo'] == {4: 0, 5: 2},
          'representatives h_o1 = g6 (x_o1 = x1), h_o2 = g8 (x_o2 = x2)')
    cyc = tr['cyc']
    k = cyc.index(4)
    cyc = cyc[k:] + cyc[:k]
    check(cyc == [4, 0, 5, 2], 'cycle o1 -> x1 -> o2 -> x2 -> o1 (exposure, need, exposure, need)')
    check(o2 == (4, 1, 4, 1, 1, 1) and kind == 'exchange cycle' and ex == 2,
          'exchange: x1 takes {g4, g6}, o2 takes g0, x2 takes {g5, g8}, o1 takes g2')
    st2 = State(rank, m, o2)
    check(st2.valid and dominates(o2, S) and st2.NA == set() and st2.J == {7, 9} and st2.F == [1, 3, 4, 5],
          'new state valid, dominating; NA = {}, J = {g7, g9}, F = {x1\', x2\', o1, o2}')
    su = [sum(UT[a] for a in s) for s in (S, o2)]
    check(su == [14, 20], f'sum of utilities 14 -> 20 (got {su})')
    check(not p2_violators(st2) and stop_test(st2) == (1, []) and st2.exposed(1) == [],
          'stop test: (P2) holds; x1\' is free with nobody exposed: absorber x1\', H = {}')
    X, o, steps, hist = de_core(rank, m, bf=True)
    check(steps == 1 and o == 1 and hist == [S, o2], 'DE: one exchange, absorber x1\'')
    want = [{4, 6}, {1, 7, 9}, {5, 8}, {3}, {2}, {0}]
    check(X == want, 'output: x1 {g4,g6}, x1\' {g1,g7,g9}, x2 {g5,g8}, x2\' {g3}, o1 {g2}, o2 {g0}')
    check(is_efx0(v, X), 'output is EFX0 (raw definition, values 4, 3, 2)')
    rng = random.Random(1)
    ok = True
    for _ in range(2000):
        vv = []
        for r in rank:
            c = rng.randint(1, 20)
            b = rng.randint(c, 20)
            a = rng.randint(b, b + c - 1)
            vv.append({r[0]: a, r[1]: b, r[2]: c})
        ok &= is_efx0(vv, X)
    check(ok, 'output is EFX0 for 2,000 random strictly balanced values consistent with the rankings (ties allowed)')
    check(sum(1 for B in X if len(B) > 2) == 1, 'only the absorber\'s bundle has more than two goods')
    # cross-check with hall.py
    sys.path.insert(0, HALL)
    import hall
    h2, hk = hall.improve(rank, m, S)
    check(h2 == o2 and hk == 'A-cycle', 'hall.py improve() returns the same exchange (kind A-cycle)')
    check(hall.cor_stop(hall.St(rank, m, o2)) == (1, []), 'hall.py stop rule: absorber x1\', H = {}')


# ============================================================================================ [3]
def section3():
    out('[3] n = 2, m = 3: rankings (g0, g1, g2), (g1, g0, g2); both hold their tops')
    rank, m, S = [(0, 1, 2), (1, 0, 2)], 3, (1, 1)
    st = State(rank, m, S)
    check(st.valid and st.F == [0, 1] and st.J == {2}, 'valid, both free, J = {g2}')
    check(st.exposed(0) == [1] and st.exposed(1) == [0], 'each agent is exposed for the other')
    po = not any(dominates(s, S) for s in valid_states(rank, m))
    check(po, 'Pareto-optimal among valid states')
    check(st.absorber_bf(0) == [2] and st.absorber_bf(1) == [2], 'completable only with H = {g2}')
    X = st.completion(0, [2])
    check(X == [{0}, {1, 2}] and is_efx0(vals_from_rank(rank), X), 'completion X0 = {g0}, X1 = {g1, g2} is EFX0')
    v = vals_from_rank(rank)
    check(all(st.exposed(o) for o in st.F), 'no free agent has nobody exposed (so H cannot be dropped from the '
          'definition of a valid absorber)')


# ============================================================================================ [4]
def section4():
    out('[4] n = 6, m = 8 with shared protecting goods (agents o1, o2, x1, x1\', x2, x2\')')
    rank = [(4, 5, 0), (6, 7, 1), (4, 1, 2), (5, 3, 1), (6, 0, 2), (7, 3, 0)]
    m, S = 8, (3, 3, 1, 1, 1, 1)
    st = State(rank, m, S)
    check(st.valid and st.F == [0, 1] and st.J == {2, 3}, 'valid; F = {o1, o2}; J = {g2, g3}')
    check(sorted(st.exposed(1)) == [2, 3] and protecting(st, 1) == {2: 2, 3: 3},
          'E_o2 = {x1, x1\'} with protecting goods g2, g3')
    check(sorted(st.exposed(0)) == [4, 5] and protecting(st, 0) == {2: 4, 3: 5},
          'E_o1 = {x2, x2\'} with protecting goods g2, g3')
    check(not st.completable_bf(), 'not completable')
    sm, p2 = short_moves(st)
    check(not sm and not p2, 'no short move')
    rainbow, nonrainbow = cycle_report(st)
    check(len(rainbow) == 2 and len(nonrainbow) == 2, 'of the 4 cycles with two exposure arcs, 2 are rainbow')
    ok = True
    for c, _ in rainbow:
        expo = {u for u in c if u in (0, 1)}
        o2 = apply_cycle(st, c, expo)
        ok &= o2 is not None and State(rank, m, o2).valid and dominates(o2, S)
    for c, _ in nonrainbow:
        ok &= apply_cycle(st, c, {u for u in c if u in (0, 1)}) is None
    check(ok, 'rainbow cycles give valid dominating states; the others give one junk good to two agents')
    X, o, steps, _ = de_core(rank, m, bf=True)
    check(is_efx0(vals_from_rank(rank), X), f'DE from serial dictatorship: EFX0 after {steps} exchange(s)')
    X, o, steps, hist = de_core(rank, m, bf=True, start=S)
    check(is_efx0(vals_from_rank(rank), X) and steps == 1 and sum(a == 4 for a in hist[1]) == 2,
          'DE\'s loop started at this state: one exchange (two new pairs), then a completion, EFX0')


# ============================================================================================ [5]
def gen_tree(k, d, shared):
    """copied from k3/simplify/po/potential/test_exchange.py: k free agents o_i holding their c and needing the goods
    of the two roots of a binary need tree T_i of depth d; the leaves of T_i hold their tops and are exposed for
    o_{i-1}, with a private junk good, or one from a shared pool of k goods"""
    rank = [None] * k
    opt = [3] * k
    g = [0]

    def new():
        g[0] += 1
        return g[0] - 1
    own = [new() for _ in range(k)]
    pool = [new() for _ in range(k)] if shared else None
    leaves = {i: [] for i in range(k)}

    def build(i, depth):
        idx = len(rank)
        rank.append(None)
        opt.append(None)
        if depth == 0:
            top = new()
            leaves[i].append(idx)
            opt[idx] = 1
            rank[idx] = (top,)
            return top
        lft, rgt = build(i, depth - 1), build(i, depth - 1)
        c = new()
        rank[idx] = (lft, rgt, c)
        opt[idx] = 3
        return c
    for i in range(k):
        x, y = build(i, d - 1), build(i, d - 1)
        rank[i] = (x, y, own[i])
    for i in range(k):
        o = (i - 1) % k
        for s, idx in enumerate(leaves[i]):
            h = pool[s % k] if shared else new()
            top = rank[idx][0]
            rank[idx] = (top, own[o], h) if s % 2 == 0 else (top, h, own[o])
    return rank, tuple(opt), g[0]


def section5():
    out('[5] Rings of k free agents over need trees of depth d (family of the potential notes)')
    for k, d, shared in ((2, 1, False), (2, 1, True), (3, 2, False), (3, 2, True), (4, 2, True)):
        rank, opt, m = gen_tree(k, d, shared)
        st = State(rank, m, opt)
        rainbow, nonrainbow = cycle_report(st)
        ok = st.valid and stop_test(st) is None and not p2_violators(st) and len(st.U) < st.n
        ok &= bool(rainbow) and all(c[1] == k for c in rainbow)
        X, o, steps, _ = de_core(rank, m, start=opt)
        ok &= steps == 1
        tr = {}
        _, kind, ex = exchange_cycle(st, tr)
        ok &= is_efx0(vals_from_rank(rank), X) and ex == k
        check(ok, f'k={k} d={d} shared={shared}: n={st.n} m={m}; no free absorber; {len(rainbow)} rainbow cycles, '
                  f'all with {k} exposure arcs; DE\'s loop from this state: one exchange with {k} exposure arcs, '
                  f'then a completion, EFX0')


# ============================================================================================ [6]
def all_allocations(n, m):
    for a in itertools.product(range(n), repeat=m):
        X = [set() for _ in range(n)]
        for g, i in enumerate(a):
            X[i].add(g)
        yield X


def section6():
    out('[6] Limits of the shape')
    trips = [(4, 3, 2), (5, 4, 3), (10, 9, 2), (7, 5, 3)]   # distinct values, strictly balanced
    # (a) agents 0, 1, 2 rank g0 > g1 > p_i; goods g0 = 0, g1 = 1, p_i = 2 + i
    rank = [(0, 1, 2), (0, 1, 3), (0, 1, 4)]
    for t in trips:
        v = vals_from_rank(rank, t)
        efx = [X for X in all_allocations(3, 5) if is_efx0(v, X)]
        small = [X for X in efx if max(len(B) for B in X) <= 2]
        perm_ok = all(is_efx0(v, [B[p] for p in range(3)]) for B in
                      itertools.permutations([{0}, {1}, {2, 3, 4}]))
        check(efx and not small and perm_ok, f'(a) values {t}: {len(efx)} EFX0 allocations, none with all bundles '
                                             f'<= 2 goods; {{g0}}, {{g1}}, {{p0, p1, p2}} is EFX0 in every order')
    # (b) goods g0 = 0, g1 = 1, g2 = 2, p_i = 3 + i
    rank = [(0, 2, 3), (0, 2, 4), (1, 2, 5), (1, 2, 6)]
    for t in trips:
        v = vals_from_rank(rank, t)
        good = [X for X in all_allocations(4, 7) if is_efx0(v, X) and sum(len(B) > 2 for B in X) <= 1]
        shapes = {tuple(sorted(len(B) for B in X)) for X in good}
        Xs = [{0}, {2}, {1}, {3, 4, 5, 6}]
        check(good and shapes == {(1, 1, 1, 4)} and is_efx0(v, Xs),
              f'(b) values {t}: {len(good)} EFX0 allocations with at most one bundle > 2, all of sizes 4,1,1,1; '
              f'the stated one is EFX0')


# ============================================================================================ [7]
def own_small(n, m, cnt):
    for rest in itertools.product(itertools.permutations(range(m), 3), repeat=n - 1):
        rank = [(0, 1, 2)] + list(rest)
        v = vals_from_rank(rank)
        for s in all_states(rank, m):
            st = State(rank, m, s)
            if not st.valid:
                continue
            cnt['valid'] += 1
            free_abs = len(st.U) == st.n or any(st.absorber_bf(o) is not None for o in st.F)
            if not st.completable_bf():
                cnt['not completable'] += 1
            if not free_abs or p2_violators(st):
                r = improve(st)
                if r[0] == 'stop':
                    assert not free_abs is False or True
                    assert st.absorber_bf(r[1]) is not None
                    X = st.completion(r[1], r[2])
                    assert is_efx0(v, X)
                    continue
                o2, kind, ex = r
                assert o2 is not None and State(rank, m, o2).valid and dominates(o2, s)
                cnt[kind] += 1
            for o, H in st.completable_bf():
                assert is_efx0(v, st.completion(o, H))
                cnt['completions checked'] += 1


def section7():
    out('[7] Small rows of the evidence table: hall.py, and this script\'s own code on the same sets')
    sys.path.insert(0, HALL)
    import hall
    want = {(2, None): (590, 90, 40, 10, 40), (3, 4): (2112, 576, 0, 360, 216), (3, 5): (12698, 2060, 444, 872, 744)}
    for (n, mm), w in want.items():
        stats = hall.new_stats()
        stats['raw'] = True
        for m in ([3, 4, 5, 6] if mm is None else [mm]):
            for rank in hall.gen_small(n, m):
                hall.run_profile(rank, m, stats)
        got = (stats['valid'], stats['not completable'], stats['P2-path'], stats['D-cycle'], stats['A-cycle'])
        check(got == w, f'hall.py n={n} m={"3..6" if mm is None else mm}: valid {got[0]}, not completable {got[1]}, '
                        f'P2-path/D-cycle/A-cycle {got[2]}/{got[3]}/{got[4]} (table: {w})')
    for n, ms in ((2, [3, 4, 5, 6]), (3, [4, 5])):
        cnt = Counter()
        for m in ms:
            own_small(n, m, cnt)
        check(cnt['valid'] == (590 if n == 2 else 2112 + 12698),
              f'own code n={n} m={ms}: {cnt["valid"]} valid states, {cnt["not completable"]} not completable; every '
              f'state with no free absorber improved ({cnt["pair chain"]} pair chains, {cnt["need cycle"]} need '
              f'cycles, {cnt["exchange cycle"]} exchange cycles); {cnt["completions checked"]} completions raw EFX0')


# ============================================================================================ [8]
def section8(K_general=20000, K_core=20000):
    out('[8] DE on random instances (evidence, seed 2026)')
    rng = random.Random(2026)
    stats = Counter()
    for _ in range(K_general):
        n = rng.randint(1, 8)
        m = rng.randint(0, 2 * n + 3)
        v = []
        for i in range(n):
            r = min(m, rng.choice([0, 1, 2, 3, 3, 3, 3]))
            v.append({g: rng.randint(1, 6) for g in rng.sample(range(m), r)})
        X = de(v, n, m, stats)
        assert sorted(g for B in X for g in B) == list(range(m))
        assert is_efx0(v, X), (v, X)
        assert sum(len(B) > 2 for B in X) <= 1
        stats['general ok'] += 1
    for _ in range(K_core):
        n = rng.randint(2, 9)
        m = rng.randint(3, 2 * n + 3)
        v = []
        for i in range(n):
            c = rng.randint(1, 9)
            b = rng.randint(c, 9)
            a = rng.randint(b, b + c - 1)
            v.append(dict(zip(rng.sample(range(m), 3), (a, b, c))))
        X = de(v, n, m, stats)
        assert sorted(g for B in X for g in B) == list(range(m))
        assert is_efx0(v, X), (v, X)
        assert sum(len(B) > 2 for B in X) <= 1
        stats['balanced ok'] += 1
    check(stats['general ok'] == K_general and stats['balanced ok'] == K_core,
          f'{K_general} general instances (n <= 8, m <= 2n + 3, 0-3 valued goods, values 1..6) and {K_core} '
          f'instances where every agent values three goods, strictly balanced (n <= 9): every output complete, '
          f'EFX0 (raw) and with at most one bundle of more than two goods')
    out(f'  stats: {stats["cores"]} runs reached a core; {stats["runs with an exchange"]} needed an exchange; at most '
        f'{stats["max exchanges"]} exchanges; pair chains {stats["pair chain"]}, need cycles {stats["need cycle"]}, '
        f'exchange cycles {stats["exchange cycle"]} (by exposure arcs: '
        f'{ {k: v for k, v in stats.items() if k.startswith("exposure arcs")} }); peeled agents {stats["peeled"]}')


def main():
    t0 = time.time()
    section1()
    section2()
    section3()
    section4()
    section5()
    section6()
    section7()
    section8()
    out(f'{len(FAILS)} failure(s); {time.time() - t0:.0f} s')
    with open(os.path.join(HERE, 'check_output.txt'), 'w') as f:
        f.write('\n'.join(LOG[:-1]) + '\n' + f'{len(FAILS)} failure(s)\n')
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
