"""Independent checker of the LIFT-SHAPE+ certificate at n = 4 (k4/matching.md §6).  Self-contained: it imports no code
of k4/matching or k4/sdc.  Raw definitions only.

Input: results/k4_matching/data/two_move_starts_n4.json.gz (every n = 4 start with no one-move repair, exported by
compute/k4-oc1max-cert) and results/k4_matching/lift_n4_witnesses.json.gz (one witness per start, written by
n4_exhaustive.py).  For every start it checks, from scratch:
  1. the picks are the serial-dictatorship picks of the first stored order, every agent picks, and exactly one agent
     z is a holder (nobody else wants its pick);
  2. the first chain P1 = (x0, ..., xt): official (each x_i, i >= 1, takes its predecessor's pick alone and gains;
     x0 takes H01, a subset of the junk and of z's pick, worth more than its pick), ends at z, |H01| = 2, H01 is also
     worth more than its pick to a second agent that is frozen and values a junk good (a dangerous agent), x0 is
     dangerous, and z is a holder after P1;
  3. the second chain P2 at the state after P1: official and canonical (each agent after the head takes its
     predecessor's bundle alone and gains; the head h takes H02 from the junk and z's bundle, gaining), ends at z,
     z's new bundle is a single good t that z values most, h is not x0;
  4. the stated case: (L3) every agent other than h and z values at most one good of X = H02 + junk; case a: z is a
     holder after P2 and v_z(H02 restricted to R_z) <= v_z(t) + v_z(g), g z's best junk good; case b:
     v_z(X restricted to R_z) <= v_z(t);
  5. the stored allocation is the one Lemma LIFT-1 prescribes (case a: h gets X minus g, z gets {t, g}; case b: h gets
     X), keeps every base of the state after P2, is a partition of all goods, and is EFX0 (raw definition).

    python3 k4/matching/check_lift_n4.py"""
import os, gzip, json, collections, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


class Inst:
    def __init__(self, sets, vals):
        self.n = len(sets); self.m = 1 + max(max(s) for s in sets)
        self.v = [dict(zip(s, x)) for s, x in zip(sets, vals)]

    def V(self, i, S): return sum(self.v[i].get(g, 0) for g in S)

    def efx0(self, X):
        for i in range(self.n):
            own = self.V(i, X[i])
            for j in range(self.n):
                if j == i: continue
                for g in X[j]:
                    if self.V(i, [h for h in X[j] if h != g]) > own: return False
        return True

    def sd(self, order):
        taken = set(); Y = [None] * self.n
        for i in order:
            av = [g for g in self.v[i] if g not in taken]
            if av:
                g = max(av, key=lambda h: (self.v[i][h], -h)); Y[i] = g; taken.add(g)
        return Y

    def junk(self, B):
        used = set(g for b in B for g in b); return [g for g in range(self.m) if g not in used]

    def wants(self, i, g, B): return g not in B[i] and self.v[i].get(g, 0) > self.V(i, B[i])

    def frozen(self, j, B):
        return len(B[j]) == 1 and any(i != j and self.wants(i, B[j][0], B) for i in range(self.n))

    def holder(self, j, B): return len(B[j]) <= 1 and not self.frozen(j, B)


def chain(I, B, P, H0, canonical_only=True):
    """Apply P (x_i takes B_{x_{i-1}}, i >= 1; x0 takes H0) after checking the official rule; returns the new state or
    raises AssertionError."""
    J = set(I.junk(B)); x0, xt = P[0], P[-1]
    assert len(set(P)) == len(P) >= 2
    assert set(H0) <= J | set(B[xt]) and H0 and I.V(x0, H0) > I.V(x0, B[x0])
    nb = [list(b) for b in B]; nb[x0] = list(H0)
    for i in range(1, len(P)):
        assert B[P[i - 1]], 'hands on an empty base'
        assert I.V(P[i], B[P[i - 1]]) > I.V(P[i], B[P[i]]), 'chain agent does not gain'
        nb[P[i]] = list(B[P[i - 1]])
    return nb


def check(sets, st, w):
    I = Inst(sets, st['vals']); Y = st['picks']; n = I.n
    assert I.sd(st['orders'][0]) == Y and all(y is not None for y in Y), '1: picks'
    base = [[g] for g in Y]; J = I.junk(base)
    hold = [j for j in range(n) if I.holder(j, base)]
    assert len(hold) == 1, '1: one holder'
    z = hold[0]
    dangerous = [x for x in range(n) if I.frozen(x, base) and any(g in I.v[x] for g in J)]
    P1, H01, P2, H02, h = w['P1'], w['H01'], w['P2'], w['H02'], w['owner']
    B1 = chain(I, base, P1, H01)
    assert P1[0] in dangerous and P1[-1] == z and len(H01) == 2 and set(H01) <= set(J) | {Y[z]}, '2: P1 shape'
    assert any(q != P1[0] and I.V(q, H01) > I.V(q, base[q]) for q in dangerous), '2: shared'
    assert I.holder(z, B1), '2: z holder after P1'
    B2 = chain(I, B1, P2, H02)
    assert P2[0] == h and h != P1[0] and P2[-1] == z and len(B2[z]) == 1, '3: P2 shape'
    t = B2[z][0]; assert I.v[z][t] == max(I.v[z].values()), '3: favourite'
    J2 = I.junk(B2); X = list(B2[h]) + J2
    assert all(len(set(X) & set(I.v[i])) <= 1 for i in range(n) if i not in (h, z)), '4: L3'
    G = [g for g in J2 if g in I.v[z]]
    if w['case'] == 'a':
        assert I.holder(z, B2), '4: L1'
        gb = max([I.v[z][g] for g in G] + [0])
        assert I.V(z, [g for g in B2[h] if g in I.v[z]]) <= I.v[z][t] + gb, "4: L2'"
        A = [list(b) for b in B2]
        if G:
            g = max(G, key=lambda x: I.v[z][x]); A[h] = [x for x in X if x != g]; A[z] = [t, g]
        else:
            A[h] = X
    else:
        assert I.V(z, [g for g in X if g in I.v[z]]) <= I.v[z][t], '4: Lb'
        A = [list(b) for b in B2]; A[h] = X
    assert sorted(map(sorted, A)) == sorted(map(sorted, w['alloc'])), '5: allocation as prescribed'
    assert all(set(B2[i]) <= set(A[i]) for i in range(n)), '5: bases kept'
    assert sorted(g for b in A for g in b) == list(range(I.m)), '5: partition'
    assert I.efx0(A), '5: EFX0'
    return w['case']


if __name__ == '__main__':
    t0 = time.time()
    d = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_matching', 'data', 'two_move_starts_n4.json.gz'), 'rt'))
    W = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_matching', 'lift_n4_witnesses.json.gz'), 'rt'))['witnesses']
    starts = [(hg['sets'], s) for hg in d['hypergraphs'] for s in hg['starts']]
    print('$ python3 k4/matching/check_lift_n4.py |', len(starts), 'starts,', len(W), 'witnesses', flush=True)
    byk = {w['k']: w for w in W}; C = collections.Counter()
    for k, (sets, st) in enumerate(starts):
        if k not in byk: C['no witness'] += 1; continue
        try:
            C['verified, case %s' % check(sets, st, byk[k])] += 1
        except AssertionError as e:
            C['FAILED: %s' % e] += 1
    for x in sorted(C): print(x, C[x])
    print('all starts certified:', C['no witness'] == 0 and not any(x.startswith('FAILED') for x in C))
    print('time %.0f s' % (time.time() - t0))
