#!/usr/bin/env python3
"""Referee check of k3-oc1's Lemmas 4-7 (k4/k3_oc1.md §12, branch claude/k4-k3-oc1 at 9719be2) and kgen-n3's Lemma
G5 / Corollary G5' (kgen/n3.md §15.6, branch claude/kgen-n3 at a319483). Own code, written from the texts; nothing
from k4/k3oc1/ or kgen/ is run or imported. Raw EFX0 and one-absorber completion from cert_ref.py.

DE's core case: every agent ranks three goods a > b > c, strictly balanced; values (4, 3, 2) are exact (k3_oc1.md
§1, Lemma L5). Dead goods allowed. DE state notions as in k3_oc1.md §2: U pair holders ({b, c}), T terminals (outside
U, holding a good nobody wants, or nothing), F frozen; E_o for owner o; validity; LB upgrades (a b-holder whose c is
junk and whose b nobody wants takes c; repeated to a fixpoint). Rule E: s(x) = sigma-earliest wanter of x's good,
iterated to a terminal end(x); a valid Rule E rotation is a frozen exposed k (holding a_k) with {b_k, c_k} ⊆
J ∪ {good of end(k)}.

Starts: drafts of random orders on random instances (n = 3..6), kept if perfect (every agent picks); the state
after maximal upgrades. Hard = the draft has no one-absorber completion (brute force).
  G5     : every valid Rule E rotation gives a valid state with an acyclic want graph, also after upgrades.
           Mutation 'anychain': any need chain (any wanter at each step) instead of Rule E.
  G5'    : if |J| <= 2, every valid Rule E rotation gives |J'| <= |T'| (before and after upgrades) and a
           one-absorber completion exists (brute force).
  Lemma 4: after every rotation, no agent sharing a good with k's pair is exposed for any owner o != k.
  Lemma 5: after every rotation (q = 1) and its upgrades (u), |J'| = |J| - q - u, |T'| = |T| - q - u + r and
           omega' = omega - r, with r = nu - nu' counted directly; also for Lemma 7's rings (q >= 2).
  Lemma 6: at every hard state (draft, and draft after upgrades), every terminal has a frozen exposed agent.
  Lemma 7: at hard states with no direct k: f(t) = end(k_t) has no fixed point; its cycles give disjoint Rule E
           segments without other terminals; with distinct junk partners the ring is a §29 official move
           (cert_ref.apply_move) and its result is valid. Also the two named crossed configurations.
"""
import itertools, random, sys, json
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, sd, complete, apply_move

def mkv(ranks, m):
    v = [[0] * m for _ in ranks]
    for i, (a, b, c) in enumerate(ranks):
        v[i][a], v[i][b], v[i][c] = 4, 3, 2
    return v

class St:
    def __init__(self, v, ranks, S):
        self.v, self.ranks, self.S = v, ranks, [frozenset(s) for s in S]
        self.n, self.m = len(S), len(v[0])
        self.J = set(range(self.m)) - set().union(*self.S)
        self.holder = {g: i for i in range(self.n) for g in self.S[i]}
    def wants(self, i, g):
        return g not in self.S[i] and self.v[i][g] > val(self.v, i, self.S[i])
    def wanters(self, i):
        if len(self.S[i]) != 1:
            return []
        (g,) = self.S[i]
        return [w for w in range(self.n) if w != i and self.wants(w, g)]
    def U(self):
        return {i for i in range(self.n) if self.S[i] == frozenset(self.ranks[i][1:])}
    def T(self):
        U = self.U()
        return {i for i in range(self.n) if i not in U and not self.wanters(i)}
    def F(self):
        U = self.U(); T = self.T()
        return {i for i in range(self.n) if i not in U and i not in T}
    def valid(self):
        for i in range(self.n):
            for g in range(self.m):
                if self.wants(i, g):
                    h = self.holder.get(g)
                    if h is None or self.S[h] != frozenset({g}):
                        return False
        return all(len(s) <= 1 or (len(s) == 2 and s == frozenset(self.ranks[i][1:])) for i, s in enumerate(self.S))
    def base(self, o):
        return self.S[o]
    def E(self, o):
        U = self.U(); out = []
        for x in range(self.n):
            a, b, c = self.ranks[x]
            if x != o and x not in U and self.S[x] == frozenset({a}) and {b, c} <= self.J | self.S[o]:
                out.append(x)
        return out
    def nu(self):
        return sum(1 for i in range(self.n) if self.wanters(i))
    def acyclic(self):
        arcs = {i: self.wanters(i) for i in range(self.n)}
        color = {}
        def dfs(u):
            color[u] = 1
            for w in arcs[u]:
                if color.get(w) == 1 or (w not in color and not dfs(w)):
                    return False
            color[u] = 2
            return True
        return all(dfs(u) for u in range(self.n) if u not in color)

def upgrade(st):
    S = list(st.S); u = 0
    while True:
        cur = St(st.v, st.ranks, S); done = True
        for x in range(cur.n):
            a, b, c = cur.ranks[x]
            if cur.S[x] == frozenset({b}) and c in cur.J and not cur.wanters(x):
                S[x] = frozenset({b, c}); u += 1; done = False
                break
        if done:
            return cur, u

def rule_e_chain(st, k, sigma, anyw=False):
    pos = {a: i for i, a in enumerate(sigma)}
    T = st.T()
    def rec(seq):
        x = seq[-1]
        if x in T and len(seq) > 1:
            yield list(seq); return
        ws = [w for w in st.wanters(x) if w not in seq]
        if not ws:
            return
        for w in (ws if anyw else [min(ws, key=lambda a: pos[a])]):
            yield from rec(seq + [w])
    return list(rec([k]))

def rotate(st, seq):
    S = list(st.S); k = seq[0]; a, b, c = st.ranks[k]
    for i in range(1, len(seq)):
        S[seq[i]] = st.S[seq[i - 1]]
    S[k] = frozenset({b, c})
    return St(st.v, st.ranks, S)

def valid_rule_e(st, sigma):
    F = st.F(); out = []
    for k in sorted(F):
        a, b, c = st.ranks[k]
        if st.S[k] != frozenset({a}):
            continue
        for seq in rule_e_chain(st, k, sigma):
            e = seq[-1]
            if {b, c} <= st.J | st.S[e]:
                out.append(seq)
    return out

def check_state(st, sigma, c, ex, hard, tag, mut=None):
    T = st.T(); J = st.J; F = st.F()
    om = len(J) - len(T); nu = st.nu()
    c[tag + "states"] += 1
    if hard:
        c[tag + "hard"] += 1
        for t in T:
            c[tag + "L6_terminals"] += 1
            if not (set(st.E(t)) & F):
                c[tag + "L6_FAIL"] += 1; ex.append(("L6", st.ranks, [sorted(s) for s in st.S], t))
    rots = valid_rule_e(st, sigma)
    if mut == "anychain":
        rots = []
        for k in sorted(F):
            a, b, cc = st.ranks[k]
            if st.S[k] == frozenset({a}):
                rots += [s for s in rule_e_chain(st, k, sigma, anyw=True) if {b, cc} <= J | st.S[s[-1]]]
    for seq in rots:
        k = seq[0]; P = rotate(st, seq)
        c[tag + "rotations"] += 1
        if not P.valid():
            c[tag + "G5_invalid_after_rotation"] += 1
            continue
        P2, u = upgrade(P)
        acyc = P.acyclic() and P2.acyclic()
        c[tag + ("G5_acyclic" if acyc else "G5_CYCLE")] += 1
        if not acyc and mut is None:
            ex.append(("G5", st.ranks, [sorted(s) for s in st.S], seq))
        if mut:
            continue
        # Lemma 4
        kp = set(st.ranks[k][1:])
        for o in range(P.n):
            if o != k and any(set(P.ranks[x][1:]) & kp for x in P.E(o)):
                c[tag + "L4_FAIL"] += 1
        # Lemma 5 (q = 1)
        r = nu - P2.nu()
        ok5 = (len(P2.J) == len(J) - 1 - u and len(P2.T()) == len(T) - 1 - u + r
               and len(P2.J) - len(P2.T()) == om - r)
        c[tag + ("L5_ok" if ok5 else "L5_FAIL")] += 1
        if not ok5:
            ex.append(("L5", st.ranks, [sorted(s) for s in st.S], seq, u, r))
        # G5'
        if len(J) <= 2:
            c[tag + "G5p_tests"] += 1
            okc = len(P.J) <= len(P.T()) and len(P2.J) <= len(P2.T()) and complete(st.v, [set(s) for s in P.S]) is not None
            if not okc:
                c[tag + "G5p_FAIL"] += 1; ex.append(("G5'", st.ranks, [sorted(s) for s in st.S], seq))
    # Lemma 7
    if hard and mut is None and not rots:
        c[tag + "L7_no_direct"] += 1
        lemma7(st, sigma, c, ex, tag)

def lemma7(st, sigma, c, ex, tag):
    T = sorted(st.T()); F = st.F(); pos = {a: i for i, a in enumerate(sigma)}
    kt = {}
    for t in T:
        cand = sorted(set(st.E(t)) & F, key=lambda a: pos[a])
        if not cand:
            c[tag + "L7_no_frozen_exposed (contradicts L6)"] += 1; return
        kt[t] = cand[0]
    seg = {t: rule_e_chain(st, kt[t], sigma)[0] for t in T}
    f = {t: seg[t][-1] for t in T}
    if any(f[t] == t for t in T):
        c[tag + "L7_FAIL_fixed_point"] += 1; return
    t0 = T[0]; seen = []
    while t0 not in seen:
        seen.append(t0); t0 = f[t0]
    cyc = seen[seen.index(t0):]
    segs = [seg[t] for t in cyc]
    agents = [a for s in segs for a in s[:-1]]
    disjoint = len(agents) == len(set(agents)) and all(a not in T for s in segs for a in s[:-1])
    c[tag + ("L7_segments_disjoint" if disjoint else "L7_FAIL_segments")] += 1
    partners = []
    for t in cyc:
        a, b, cc = st.ranks[kt[t]]
        rest = {b, cc} - st.S[t]
        partners.append(next(iter(rest)) if len(rest) == 1 and rest <= st.J else None)
    if None in partners:
        c[tag + "L7_FAIL_pair_not_Yt_plus_junk"] += 1; return
    if len(set(partners)) == len(partners):
        # the ring as one §29 chain: x0 = k_{t1}, ..., t2, k_{t2}, ..., t3, ..., k_{tq}, ..., t1 = x_t;
        # x0 takes {Y_{t1}, j_1} from J + B_{x_t}; each other pair-taker k_{ti} takes Y_{ti} + j_i
        path = []
        for i in range(len(cyc)):
            path += seg[cyc[i]]
        # path = k_{t1} ... t2, k_{t2} ... t3, ..., k_{tq} ... t1 ; H: pair-takers take their junk partner
        Hs = []
        for idx, a in enumerate(path):
            if idx == 0:
                Hs.append(sorted({partners[0], next(iter(st.S[cyc[0]]))}))
            elif a in kt.values():
                i = cyc.index([t for t in cyc if kt[t] == a][0])
                Hs.append([partners[i]])
            else:
                Hs.append([])
        B = [set(s) for s in st.S]
        res = apply_move(st.v, B, dict(kind="chain", path=path, H=Hs))
        okm = res is not None and St(st.v, st.ranks, res).valid()
        c[tag + ("L7_ring_official_and_valid" if okm else "L7_ring_not_official_or_invalid")] += 1
        c[tag + "L7_ring_completes"] += (res is not None and complete(st.v, res) is not None)
    else:
        c[tag + "L7_partners_not_distinct"] += 1

def rand_run(N, seed, mut=None):
    rng = random.Random(seed); c = Counter(); ex = []
    for _ in range(N):
        n = rng.randint(3, 6); m = rng.randint(n + 1, min(2 * n, n + 4)) + rng.choice([0, 0, 1])
        ranks = [tuple(rng.sample(range(m), 3)) for _ in range(n)]
        v = mkv(ranks, m)
        orders = list(itertools.permutations(range(n))); rng.shuffle(orders)
        seen = set()
        for o in orders[:6]:
            Y = sd(v, list(o))
            if None in Y or tuple(Y) in seen:
                continue
            seen.add(tuple(Y))
            if len(set(range(m)) - set(Y)) > 4:
                continue
            st = St(v, ranks, [{y} for y in Y])
            hard = complete(v, [set(s) for s in st.S]) is None
            check_state(st, list(o), c, ex, hard, "draft_", mut)
            st2, u = upgrade(st)
            check_state(st2, list(o), c, ex, hard, "upg_", mut)
    print(json.dumps(dict(source=f"k3 Lemmas 4-7, G5, G5' random N={N} seed={seed} mutation={mut}", **dict(sorted(c.items())))))
    for e in ex[:6]:
        print("EXAMPLE", e)

def named():
    c = Counter(); ex = []
    for name, ranks, m in [("crossed n=6", [(2, 0, 6), (3, 0, 7), (4, 1, 8), (5, 1, 9), (4, 5, 0), (2, 3, 1)], 10),
                           ("crossed n=7", [(0, 7, 5), (1, 8, 5), (3, 9, 6), (4, 6, 10), (1, 0, 6), (3, 4, 2), (2, 5, 6)], 11)]:
        v = mkv(ranks, m); o = list(range(len(ranks))); Y = sd(v, o)
        st = St(v, ranks, [{y} for y in Y])
        hard = complete(v, [set(s) for s in st.S]) is None
        st2, u = upgrade(st)
        c2 = Counter()
        check_state(st2, o, c2, ex, hard, "chk_")
        print(json.dumps(dict(instance=name, picks=Y, hard=hard, T=sorted(st2.T()), valid_rule_e_rotations=len(valid_rule_e(st2, o)),
                              **dict(sorted(c2.items())))))

if __name__ == "__main__":
    if sys.argv[1] == "named":
        named()
    else:
        rand_run(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] if len(sys.argv) > 4 else None)
