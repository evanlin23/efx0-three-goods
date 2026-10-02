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
the only needer; the listed x-alone triple (o, X, c) is one (o a best owner, X optimal, X + c threatening x and nobody
else but o); o has no escape (k4/oneneeder.md Proposition D) at any x-alone triple with owner o != z."""
import itertools, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'k4')); sys.path.insert(0, os.path.join(HERE, '..', 'k4', 'suite'))
import oneneeder_check as C1
from model import bits, pc, mask

INSTANCES = [
    {'id': 'oneneeder-escape-t1-n4', 'sets': [[0, 2, 6, 10], [1, 5, 9, 10], [3, 6, 7, 8], [4, 7, 8, 9]],
     'vals': [[4, 3, 2, 8], [4, 3, 2, 8], [6, 1, 8, 4], [4, 8, 3, 6]], 'm': 11,
     'P': [[10], [1], [3, 7], [4, 9]], 'def': 1, 't1stuck': True, 't3stage': False, 'x': 0, 'z': 1,
     'triple': (3, [0, 2, 4, 8, 9], 6)},
    {'id': 'oneneeder-escape-n3', 'sets': [[0, 1, 2, 3], [2, 4, 5, 6], [3, 4, 5, 6]],
     'vals': [[3, 2, 4, 8], [4, 6, 3, 8], [8, 2, 4, 3]], 'm': 7,
     'P': [[0, 1], [2, 4], [3]], 'def': 1, 't1stuck': False, 't3stage': False, 'x': 2, 'z': 0,
     'triple': (1, [2, 4, 5], 6)},
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
        trip = []
        for o, (val_, arg) in s['own'].items():
            if val_ != s['V'] or o == z: continue
            for X, u in arg:
                for c in bits(s['J'] & ~X):
                    Y = X | (1 << c)
                    if I.threat(x, Y, s['hv'][x]) and not any(I.threat(w, Y, s['hv'][w]) for w in range(I.n) if w not in (o, x)):
                        trip.append((o, X, c))
        listed = (o0, mask(X0), c0) in trip
        ok &= listed
        print('  listed x-alone triple %s: %s' % (d['triple'], 'ok' if listed else 'NOT FOUND'))
        J = frozenset(bits(s['J'])); BsF = [frozenset(bits(B)) for B in Bs]
        n_esc = 0
        for o, X, c in trip:
            Y = frozenset(bits(X | (1 << c)))
            e1 = escapes(None, lambda S: not I.needs(o, mask(S)), lambda Z, S: I.threat(o, mask(Z), I.val(o, mask(S))),
                         BsF, J, L, z, o, Y, g, frozenset(bits(I.R[o])))
            e2 = escapes(None, lambda S: not T.needs(o, S), lambda Z, S: T.threat(o, Z, S),
                         BsF, J, L, z, o, Y, g, T.R[o])
            assert sorted(map(sorted, e1)) == sorted(map(sorted, e2)), ('escape mismatch', e1, e2)
            n_esc += len(e1)
        ok &= n_esc == 0
        print('  x-alone triples with o != z: %d; escapes found (both implementations): %d %s' % (len(trip), n_esc, 'ok' if n_esc == 0 else 'UNEXPECTED'))
    print('ALL OK' if ok else 'SOMETHING FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
