"""Shared objects of workstream proof/k4-f2 (k4/f2.md): one strict profile's min-frozen class with deficits, keys and
the moves of R_C = (T1) ∪ (T2) ∪ (T3⁺) ∪ (T4) (k4/dl2.md §3, k4/dl13.md §2.2–2.3, and the coordinator's T3⁺ after DL_RT4
was refuted at n = 5, f = 3 on origin/compute/k4-rt4-n5b and origin/compute/k4-rt4-n5c).

Built on main's k4/suite/model.py (𝒫, the min-frozen class), k4/dl2_classify.py (PA: needs, junk, frozen agents,
slots, Lemma H1's deficit with the owner tables) and k4/dl2_relations.py (the shape of a move, whose (T3) test is
asserted to agree with the T3⁺ test below at W = ∅). Written here from the definitions:
  (T4)  the changed agents are frozen in P and in P', they permute their one-good bases, and NA(P') = NA(P);
  (T3⁺) the frozen-chain role swap: NA(P') = NA(P); among the changed agents exactly one x goes frozen -> free and exactly
        one z goes free -> frozen, z needing its new good in P; W = the changed agents frozen in both; at most one
        changed agent free in both (the helper), and it gives up a good of its base; the bases of W ∪ {z} in P' are
        exactly the bases of W ∪ {x} in P. (T3) is the case W = ∅ (then z takes x's good).
Kinds returned by kind(): 't1', 't2', 't3' (T3⁺ with W = ∅), 't3c' (T3⁺ with W ≠ ∅, a chain), 't4', or None.

Definitions (k4/dl13.md §1, §2.3): the key of a min-frozen P is the map frozen agent -> its good; def*(key) is the least
deficit over the min-frozen P with that key; P is at the *T3 stage* if def(P) > 0, def(P) = def*(key(P)) (no (T1) or
(T2) move lowers it: they are exactly the moves inside a key) and no (T4) move lowers it."""
import itertools, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc, mask
from dl2_classify import PA, INF, best_owners, counted, bigtop
from dl2_relations import shape


def tup(L): return tuple(mask(b) for b in L)
def lst(Bs): return [sorted(bits(B)) for B in Bs]


def t3plus(P, P2):
    """the T3⁺ test (module doc): None, or (x, z, W, h) with W the list of agents frozen in both"""
    if P.NA != P2.NA: return None
    n = P.I.n
    ch = [i for i in range(n) if P.Bs[i] != P2.Bs[i]]
    U = [i for i in ch if P.frozen[i] and not P2.frozen[i]]
    Z = [i for i in ch if not P.frozen[i] and P2.frozen[i]]
    W = [i for i in ch if P.frozen[i] and P2.frozen[i]]
    Y = [i for i in ch if not P.frozen[i] and not P2.frozen[i]]
    if len(U) != 1 or len(Z) != 1 or len(Y) > 1: return None
    if any(not (P.Bs[y] & ~P2.Bs[y]) for y in Y): return None
    x, z = U[0], Z[0]
    if sorted(P2.Bs[i] for i in W + [z]) != sorted(P.Bs[i] for i in W + [x]): return None
    if P2.Bs[z] & ~P.N[z]: return None                   # z needs its new good in P
    return x, z, W, (Y[0] if Y else None)


def kind(P, P2, s=None):
    """the R_C kind of the move P -> P2 (both min-frozen): 't1', 't2', 't3', 't3c', 't4' or None"""
    s = s or shape(P, P2)
    old_t3 = s['swap'] and s['needer'] and not s['nt'] and len(s['Y']) <= 1 and s['gives']
    tp = t3plus(P, P2)
    assert old_t3 == (tp is not None and not tp[2]), ('T3 vs T3+ with W empty', P.Bs, P2.Bs)
    if s['k'] == 1 and not s['nt']: return 't1'
    if s['k'] >= 2 and len(s['Y']) == s['k'] and not s['nt']: return 't2'
    if tp is not None: return 't3' if not tp[2] else 't3c'
    n = P.I.n
    ch = [i for i in range(n) if P.Bs[i] != P2.Bs[i]]
    if len(ch) >= 2 and all(P.frozen[i] and P2.frozen[i] for i in ch) and P.NA == P2.NA \
            and sorted(P.Bs[i] for i in ch) == sorted(P2.Bs[i] for i in ch):
        return 't4'
    return None


def chain_shape(P, P2, x, z, W):
    """the frozen goods' route in a T3⁺ move: (path, cycles): path = [z, a_1, ..., a_k, x] where z takes a_1's old good,
    a_i takes a_{i+1}'s (a_k takes x's); the other agents of W form cycles; also whether every agent of the path takes a
    good it needs in P (a need path)"""
    holder = {P.Bs[i]: i for i in W + [x]}
    src = {i: holder[P2.Bs[i]] for i in W + [z]}          # i takes the old good of src[i]
    path = [z]; cur = z
    while cur != x:
        cur = src[cur]; path.append(cur)
    rest = [w for w in W if w not in path]
    needp = all(P2.Bs[a] & P.N[a] for a in path[:-1])
    return path, len(rest), needp


class Prof:
    """the min-frozen class of one strict profile (needs f >= 1 and omega >= 1 to be useful)"""

    def __init__(self, d, fmin=1):
        I = M.Inst(d['sets'], d['vals'], d.get('m'))
        I.preallocs()
        self.I, self.d = I, d
        self.ok = I.omega >= 1 and I.f >= fmin
        if not self.ok: return
        self.mp = [Bs for Bs, NA in I.minP]
        self.PA = {Bs: PA(I, Bs) for Bs in self.mp}
        self.D, self.OWN = {}, {}
        for Bs in self.mp:
            self.D[Bs], self.OWN[Bs] = self.PA[Bs].deficit()
        self.key = {Bs: tuple(Bs[i] if self.PA[Bs].frozen[i] else 0 for i in range(I.n)) for Bs in self.mp}
        self.dstar = {}
        for Bs in self.mp:
            k = self.key[Bs]
            self.dstar[k] = min(self.dstar.get(k, INF), self.D[Bs])
        self.bykey = {}
        for Bs in self.mp: self.bykey.setdefault(self.key[Bs], []).append(Bs)

    def improving(self, Bs):
        """[(B2, kind)] for every min-frozen B2 with def(B2) < def(Bs); kind as in kind()"""
        P = self.PA[Bs]; out = []
        for B2 in self.mp:
            if self.D[B2] >= self.D[Bs]: continue
            k = kind(P, self.PA[B2])
            same = self.key[B2] == self.key[Bs]
            assert same == (k in ('t1', 't2')), ('key vs (T1)/(T2)', Bs, B2, k)
            out.append((B2, k))
        return out

    def t3_stage(self, Bs):
        """def > 0, least deficit of its key, no improving (T4) move"""
        if self.D[Bs] <= 0 or self.D[Bs] != self.dstar[self.key[Bs]]: return False
        return not any(k == 't4' for _, k in self.improving(Bs))

    def best(self, Bs): return best_owners(self.OWN[Bs])

    def V(self, Bs):
        b = self.best(Bs)
        return self.OWN[Bs][b[0]][0] if b else None

    # ---------------------------------------------------------------- blockers, needers
    def blockers(self, Bs, o, Z, hold=None):
        """agents w != o that Z threatens, w holding its base (or hold[w])"""
        I = self.I; hold = hold or {}
        return [w for w in range(I.n) if w != o and I.threat(w, Z, I.val(w, hold.get(w, Bs[w])))]

    def needers(self, Bs, x):
        P = self.PA[Bs]
        return [i for i in range(self.I.n) if P.N[i] & Bs[x]]

    def free_needers(self, Bs, x):
        P = self.PA[Bs]
        return [i for i in self.needers(Bs, x) if not P.frozen[i]]

    def single_blocks(self, Bs):
        """(o, X, c, w): o a best owner, X optimal, c ∈ J \\ X, and w the only agent other than o threatened by
        X ∪ {c}"""
        P = self.PA[Bs]; out = []
        for o in self.best(Bs):
            for X in self.OWN[Bs][o][1]:
                for c in bits(P.J & ~X):
                    ws = self.blockers(Bs, o, X | (1 << c))
                    if len(ws) == 1: out.append((o, X, c, ws[0]))
        return out

    def t3_moves(self, Bs, chains=True):
        """the improving (T3⁺) moves: (B2, x, z, W, h); with chains=False only those with W = ∅ (plain (T3))"""
        P = self.PA[Bs]; out = []
        for B2, k in self.improving(Bs):
            if k == 't3' or (chains and k == 't3c'):
                x, z, W, h = t3plus(P, self.PA[B2])
                out.append((B2, x, z, W, h))
        return out

    def t4_optimal(self, Bs):
        """the need digraph on the frozen agents (x -> y iff x needs B_y) is acyclic"""
        P = self.PA[Bs]; F = [i for i in range(self.I.n) if P.frozen[i]]
        succ = {x: [y for y in F if y != x and P.N[x] & Bs[y]] for x in F}
        state = {}

        def cyc(u):
            state[u] = 1
            for w in succ[u]:
                if state.get(w) == 1 or (w not in state and cyc(w)): return True
            state[u] = 2
            return False
        return not any(x not in state and cyc(x) for x in F)


def profile_items(d):
    """normalize a record with sets/vals/m (or core.sets/core.m)"""
    if 'sets' in d: return {'sets': d['sets'], 'vals': d['vals'], 'm': d.get('m') or 1 + max(g for S in d['sets'] for g in S)}
    c = d['core']
    return {'sets': c['sets'], 'vals': d['vals'], 'm': c['m']}
