#!/usr/bin/env python3
"""Replay of attempts/k4-oneneeder-escape-t1.md (workstream proof/k4-oneneeder) with two implementations.

Implementation 1: k4/oneneeder_check.py (on k4/suite/model.py; deficit by Lemma H1).
Implementation 2: written here from the definitions only (k4/c4x.md section 1): the pre-allocations are enumerated as
base maps (every good to nobody or to one agent that values it, at most two goods per agent), validity is (V1), (V2)
literally, and the deficit is the removal-only deficit itself (the least |C| - S_o(C) over free owners o and C inside
J with B_o + (J minus C) threatening nobody, slots recomputed with o's needs taken from that bundle), not Lemma H1.

For each instance and state the script checks, with both implementations: f = 1 and omega; P is min-frozen with the
stated deficit; whether P is T1-stuck (no re-base of one free agent inside its base and the junk, keeping the needed
set, lowers the deficit) and whether it is at the T3 stage (its deficit is the least of its key); x is big-top and z is
the only needer; the set of x-alone triples (o, X, c) (o a best owner, X optimal, X + c threatening x and nobody else
but o; implementation 2 takes o and X from the owners and bundles at which the removal-only deficit is attained), and
that the listed triple is one; o has no escape (k4/oneneeder.md Proposition D) at the triples with owner o != z as the
claim says. For the state-level claims (instances 2 and 3) also: no swap of Corollary 8.2's form with at most one helper
lowers the deficit (implementation 1: k4/oneneeder_check.c3; implementation 2: every min-frozen state in which z holds
{g}, x a base inside L, and at most one other agent h changes, to a base inside (J + B_z + B_h) minus L that gives up a
good of B_h and does not need g, has deficit >= def(P)); for instance 3 also no move of x, z and one more agent at all."""
import itertools, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'k4')); sys.path.insert(0, os.path.join(HERE, '..', 'k4', 'suite'))
import oneneeder_check as C1
from model import bits, pc, mask

INSTANCES = [
    {'id': 'oneneeder-escape-t1-n4', 'sets': [[0, 2, 6, 10], [1, 5, 9, 10], [3, 6, 7, 8], [4, 7, 8, 9]],
     'vals': [[4, 3, 2, 8], [4, 3, 2, 8], [6, 1, 8, 4], [4, 8, 3, 6]], 'm': 11,
     'P': [[10], [1], [3, 7], [4, 9]], 'def': 1, 't1stuck': True, 't3stage': False, 'x': 0, 'z': 1,
     'triple': (3, [0, 2, 4, 8, 9], 6), 'claim': 'per-triple'},
    {'id': 'oneneeder-escape-n3', 'sets': [[0, 1, 2, 3], [2, 4, 5, 6], [3, 4, 5, 6]],
     'vals': [[3, 2, 4, 8], [4, 6, 3, 8], [8, 2, 4, 3]], 'm': 7,
     'P': [[0, 1], [2, 4], [3]], 'def': 1, 't1stuck': False, 't3stage': False, 'x': 2, 'z': 0,
     'triple': (1, [2, 4, 5], 6), 'claim': 'state'},
    {'id': 'oneneeder-onehelper-t1-n4', 'sets': [[0, 1, 2, 7], [2, 4, 5, 8], [3, 4, 5, 6], [3, 6, 7, 8]],
     'vals': [[2, 3, 6, 10], [7, 4, 8, 2], [6, 5, 3, 7], [3, 2, 8, 4]], 'm': 9,
     'P': [[7], [2, 8], [4, 5], [3, 6]], 'def': 1, 't1stuck': True, 't3stage': False, 'x': 0, 'z': 3,
     'triple': (1, [0, 2, 8], 1), 'claim': 'one-helper'},
]


# ---------------------------------------------------------------- implementation 2
class Two:
    def __init__(self, d):
        self.n, self.m = len(d['sets']), d['m']
        self.R = [set(S) for S in d['sets']]
        self.v = [dict(zip(S, V)) for S, V in zip(d['sets'], d['vals'])]
        self.P = []
        choices = [[None] + [i for i in range(self.n) if g in self.R[i]] for g in range(self.m)]
        for bm in itertools.product(*choices):
            B = tuple(frozenset(g for g in range(self.m) if bm[g] == i) for i in range(self.n))
            if any(len(b) > 2 for b in B): continue
            N = [self.needs(i, B[i]) for i in range(self.n)]
            NA = frozenset().union(*N)
            J = frozenset(g for g in range(self.m) if bm[g] is None)
            if J & NA or any(len(B[i]) == 2 and B[i] & NA for i in range(self.n)): continue
            self.P.append(B)
        fr = {B: self.frozen(B) for B in self.P}
        self.f = min(len(F) for F in fr.values())
        self.omega = self.f - (2 * self.n - self.m)
        self.minP = [B for B in self.P if len(fr[B]) == self.f]
        self.D = {B: self.deficit(B) for B in self.minP}

    def val(self, i, S): return sum(self.v[i].get(g, 0) for g in S)

    def needs(self, i, B): return frozenset(g for g in self.R[i] - B if self.v[i][g] > self.val(i, B))

    def threat(self, i, Z, B):
        return bool(Z) and max(self.val(i, Z - {h}) for h in Z) > self.val(i, B)

    def frozen(self, B):
        NA = frozenset().union(*[self.needs(i, B[i]) for i in range(self.n)])
        return [i for i in range(self.n) if len(B[i]) == 1 and B[i] <= NA]

    def junk(self, B): return frozenset(range(self.m)) - frozenset().union(*B)

    def deficit(self, B):
        n = self.n; N = [self.needs(i, B[i]) for i in range(n)]; F = self.frozen(B); J = self.junk(B)
        S = sum(2 - len(B[i]) for i in range(n) if i not in F)
        if len(J) <= S: return len(J) - S
        best = None
        for o in range(n):
            if o in F: continue
            for k in range(len(J) + 1):
                for Cl in itertools.combinations(sorted(J), k):
                    X = B[o] | (J - set(Cl))
                    if any(self.threat(w, X, B[w]) for w in range(n) if w != o): continue
                    NA2 = frozenset().union(*[N[j] for j in range(n) if j != o]) | self.needs(o, X)
                    sl = sum(0 if (len(B[j]) == 1 and B[j] <= NA2) else 2 - len(B[j]) for j in range(n) if j != o)
                    d = k - sl
                    if best is None or d < best: best = d
        return best

    def best_bundles(self, B):
        """the pairs (o, X) of a free owner o and a bundle X = B_o + (J minus C) at which the removal-only deficit is
        attained (the best owners and their optimal bundles, from the definition)"""
        n = self.n; N = [self.needs(i, B[i]) for i in range(n)]; F = self.frozen(B); J = self.junk(B)
        out = []
        for o in range(n):
            if o in F: continue
            for k in range(len(J) + 1):
                for Cl in itertools.combinations(sorted(J), k):
                    X = B[o] | (J - set(Cl))
                    if any(self.threat(w, X, B[w]) for w in range(n) if w != o): continue
                    NA2 = frozenset().union(*[N[j] for j in range(n) if j != o]) | self.needs(o, X)
                    sl = sum(0 if (len(B[j]) == 1 and B[j] <= NA2) else 2 - len(B[j]) for j in range(n) if j != o)
                    out.append((k - sl, o, X))
        best = min(d for d, _, _ in out)
        return [(o, X) for d, o, X in out if d == best]

    def triples(self, B, x):
        """the x-alone triples (o, X, c): o, X from best_bundles, c a junk good outside X such that X + c threatens x
        holding B_x and no agent other than o and x holding its base"""
        J = self.junk(B); out = set()
        for o, X in self.best_bundles(B):
            for c in J - X:
                Y = X | {c}
                if self.threat(x, Y, B[x]) and not any(self.threat(w, Y, B[w]) for w in range(self.n) if w not in (o, x)):
                    out.add((o, X, c))
        return out

    def cor82_family(self, B, x, z, g, L):
        """deficits of every min-frozen state of a swap of Corollary 8.2's form: z takes {g}, x takes a base inside L,
        and at most one other agent h changes, to a base inside (J + B_z + B_h) minus L that gives up a good of B_h and
        does not need g"""
        J = self.junk(B); out = []
        for B2 in self.minP:
            if B2[z] != frozenset([g]) or not B2[x] <= L: continue
            ch = [i for i in range(self.n) if i not in (x, z) and B2[i] != B[i]]
            if len(ch) > 1: continue
            if ch:
                h = ch[0]
                if not B2[h] <= (J | B[z] | B[h]) - L or B[h] <= B2[h] or g in self.needs(h, B2[h]): continue
            out.append(self.D[B2])
        return out

    def key(self, B):
        F = self.frozen(B); return tuple((x, B[x]) for x in F)

    def facts(self, d):
        B = tuple(frozenset(b) for b in d['P'])
        assert B in self.D, 'not min-frozen'
        D = self.D[B]; J = self.junk(B); F = self.frozen(B)
        stuck = True
        for y in range(self.n):
            if y in F: continue
            pool = sorted((B[y] | J) & self.R[y])
            for k in (1, 2):
                for S in itertools.combinations(pool, k):
                    S = frozenset(S)
                    if S == B[y] or self.needs(y, S) - frozenset().union(*[self.needs(i, B[i]) for i in range(self.n)]): continue
                    B2 = list(B); B2[y] = S; B2 = tuple(B2)
                    if B2 in self.D and self.D[B2] < D: stuck = False
        keymin = min(self.D[B2] for B2 in self.minP if self.key(B2) == self.key(B))
        x = F[0]; g = next(iter(B[x])); z = [i for i in range(self.n) if g in self.needs(i, B[i])]
        vs = sorted(self.v[x].values(), reverse=True)
        bt = len(vs) == 4 and self.v[x][g] == vs[0] and vs[0] > vs[1] + vs[2]
        return {'f': self.f, 'omega': self.omega, 'def': D, 't1stuck': stuck, 't3stage': D == keymin, 'x': x,
                'needers': z, 'bigtop': bt}


# ---------------------------------------------------------------- the escape test, on either implementation's numbers
def escapes(val, needs_free, threat, Bs, J, L, z, o, Y, g, R_o):
    Rest = (J - Y) | Bs[z]
    reg = sorted(((Y | Rest) - L) & R_o - {g})
    out = []
    for k in (1, 2):
        for S in itertools.combinations(reg, k):
            S = frozenset(S)
            if len(S & Y) > 1 or not needs_free(S): continue
            helper = bool(Bs[o] - S)
            if not helper and not (S == Bs[o] and not (L & Bs[o]) and len(S) == 1): continue
            if threat(Y - S, S): continue
            out.append(S)
    return out


def main():
    ok = True
    for d in INSTANCES:
        print('==', d['id'])
        # implementation 1
        pr = C1.Prof(d, check=True)
        Bs = tuple(mask(b) for b in d['P']); s = pr.st[Bs]; I = pr.I
        x = s['x']; gm = Bs[x]; g = next(bits(gm))
        one = {'f': I.f, 'omega': I.omega, 'def': s['def'], 'x': x,
               'needers': [i for i in range(I.n) if s['N'][i] & gm], 'bigtop': C1.bigtop_on(I, x, g),
               't3stage': s['def'] == pr.keymin[(x, gm)]}
        stuck = True
        for y in range(I.n):
            if s['F'][y]: continue
            for k in (1, 2):
                for S in itertools.combinations(list(bits((Bs[y] | s['J']) & I.R[y])), k):
                    S = mask(S)
                    if S == Bs[y] or I.needs(y, S) & ~s['NA']: continue
                    b2 = list(Bs); b2[y] = S; b2 = tuple(b2)
                    if pr.st[b2]['def'] < s['def']: stuck = False
        one['t1stuck'] = stuck
        T = Two(d); two = T.facts(d)
        for k in ('f', 'omega', 'def', 't1stuck', 't3stage', 'x', 'bigtop'):
            good = one[k] == two[k] == d.get(k, one[k])
            ok &= good
            print('  %-9s impl1 %-6s impl2 %-6s expected %-6s %s' % (k, one[k], two[k], d.get(k, '-'), 'ok' if good else 'MISMATCH'))
        good = one['needers'] == two['needers'] == [d['z']]
        ok &= good
        print('  needers  impl1 %s impl2 %s %s' % (one['needers'], two['needers'], 'ok' if good else 'MISMATCH'))
        # the listed triple, and no escape at any x-alone triple with o != z (implementation 1's owner tables)
        L = frozenset(bits(I.R[x] & ~gm))
        o0, X0, c0 = d['triple']; z = d['z']
        trip_all = []
        for o, (val_, arg) in s['own'].items():
            if val_ != s['V']: continue
            for X, u in arg:
                for c in bits(s['J'] & ~X):
                    Y = X | (1 << c)
                    if I.threat(x, Y, s['hv'][x]) and not any(I.threat(w, Y, s['hv'][w]) for w in range(I.n) if w not in (o, x)):
                        trip_all.append((o, X, c))
        trip = [t for t in trip_all if t[0] != z]
        B0 = tuple(frozenset(b) for b in d['P'])
        t2 = T.triples(B0, x)
        t1 = set((o, frozenset(bits(X)), c) for o, X, c in trip_all)
        good = t1 == t2
        ok &= good
        print('  x-alone triples: impl1 %d, impl2 %d, %s (owner z: %d)' % (len(t1), len(t2), 'same' if good else 'MISMATCH',
                                                                      sum(1 for t in t1 if t[0] == z)))
        listed = (o0, frozenset(X0), c0) in t1 and (o0, frozenset(X0), c0) in t2
        ok &= listed
        print('  listed x-alone triple %s: %s' % (d['triple'], 'ok (both implementations)' if listed else 'NOT FOUND'))
        J = frozenset(bits(s['J'])); BsF = [frozenset(bits(B)) for B in Bs]
        n_esc = {}
        for o, X, c in trip:
            Y = frozenset(bits(X | (1 << c)))
            e1 = escapes(None, lambda S: not I.needs(o, mask(S)), lambda Z, S: I.threat(o, mask(Z), I.val(o, mask(S))),
                         BsF, J, L, z, o, Y, g, frozenset(bits(I.R[o])))
            e2 = escapes(None, lambda S: not T.needs(o, S), lambda Z, S: T.threat(o, Z, S),
                         BsF, J, L, z, o, Y, g, T.R[o])
            assert sorted(map(sorted, e1)) == sorted(map(sorted, e2)), ('escape mismatch', e1, e2)
            n_esc[(o, X, c)] = len(e1)
        if d['claim'] == 'one-helper':
            # implementation 1: no swap of Corollary 8.2 with at most one helper, no construction of Proposition C or D,
            # no deficit-lowering move of x, z and at most one other agent; implementation 2: the last, from its own states
            c3 = C1.c3(pr, Bs, x, z, g, mask(L))
            trip4 = [(o, X, 0, c) for o, X, c in trip_all]
            r = C1.rules(pr, Bs, x, z, g, mask(L), trip4)
            t3 = C1.t3move(pr, Bs)
            D0 = T.D[B0]
            fam = T.cor82_family(B0, x, z, g, L)
            moves2 = [B2 for B2 in T.minP if T.D[B2] < D0 and B2[z] == frozenset([g]) and x not in T.frozen(B2)
                      and sum(1 for i in range(T.n) if i not in (x, z) and B2[i] != B0[i]) <= 1]
            two_helpers = sum(1 for B2 in T.minP if T.D[B2] < D0 and B2[z] == frozenset([g]) and x not in T.frozen(B2))
            good = (sum(n_esc.values()) == 0 and not c3 and not r and not t3 and not moves2 and two_helpers > 0
                    and all(dd >= D0 for dd in fam))
            print('  x-alone triples with o != z: %d (owners %s), escapes: %d (both implementations); Corollary 8.2 with at '
                  'most one helper: impl1 %s, impl2 %d swaps of its form, least deficit %s >= %d; Proposition C or D: %s; '
                  'a deficit-lowering move of x, z and at most one other agent: impl1 %s, impl2 %d; states of smaller '
                  'deficit with z on g (all need two other agents to move): %d' % (
                      len(trip), sorted(set(o for o, _, _ in trip)), sum(n_esc.values()), sorted(c3) or 'none',
                      len(fam), min(fam) if fam else '-', D0, bool(r), t3, len(moves2), two_helpers))
        elif d['claim'] == 'per-triple':
            good = n_esc[(o0, mask(X0), c0)] == 0
            print('  the listed triple has no escape (both implementations): %s; escapes at the other %d triples: %d' % (
                good, len(trip) - 1, sum(n_esc.values())))
        else:
            good = sum(n_esc.values()) == 0
            c3 = C1.c3(pr, Bs, x, z, g, mask(L))
            D0 = T.D[B0]; fam = T.cor82_family(B0, x, z, g, L)
            good &= not c3 and all(dd >= D0 for dd in fam) and not any(t[0] == z for t in t1)
            print('  x-alone triples with o != z: %d, none with an escape (both implementations): %s; Corollary 8.2 '
                  'with at most one helper: impl1 %s, impl2 %d swaps of its form, least deficit %s >= %d' % (
                      len(trip), sum(n_esc.values()) == 0, sorted(c3) or 'none', len(fam), min(fam) if fam else '-', D0))
        ok &= good
    print('ALL OK' if ok else 'SOMETHING FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
