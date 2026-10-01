#!/usr/bin/env python3
"""Second implementation of k4/oneneeder.c's tests (workstream proof/k4-oneneeder; k4/oneneeder.md §6). EVIDENCE only.

Written on k4/suite/model.py (the space 𝒫, needs, threats; independent of k4/oneneeder.c) with its own deficit by
Lemma H1 (asserted equal to model.Inst.deficit, the direct removal-only deficit, with --check). For every profile in the
input with f = 1 and omega >= 1 it computes every min-frozen state, the least deficit of every key, and at every
one-needer T3-stage state (def > 0, least deficit of its key, exactly one needer z of x's good g) the same tests as
k4/oneneeder.c: x big-top on g; def = 1; an x-alone triple (o, X, c) (o a best owner, X optimal, c in J minus X, X + c
threatening x holding {g} and no other agent but o); u = 1 at some optimal bundle of a best owner; Corollary 8.2 with at
most one helper (its conclusion asserted against the exact deficit of the swapped state); Proposition C and the escape
of Proposition D (k4/oneneeder.md §4), each construction's swap checked; some improving (T3) move; R_z = R_x.

usage: python3 k4/oneneeder_check.py catalog FILE [--every=E] [--max=N] [--check]
       python3 k4/oneneeder_check.py dump FILE.jsonl.gz [--check]      (the profiles of k4/oneneeder.c's dumps)
       python3 k4/oneneeder_check.py inst FILE.json [--check]          (a JSON list of {"sets", "vals", "m"})
Prints the counters (same names as k4/oneneeder.c) in total, and per profile with --per."""
import collections, gzip, itertools, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc, mask


class Prof:
    def __init__(self, d, check=False):
        I = M.Inst(d['sets'], d['vals'], d.get('m'))
        I.preallocs()
        self.I = I; self.ok = I.f == 1 and I.omega >= 1
        if not self.ok: return
        self.om = I.omega
        self.st = {}
        for Bs, NA in I.minP:
            s = self.state(Bs)
            if check:
                ref = I.deficit(Bs)
                assert ref == s['def'], ('deficit mismatch', Bs, ref, s['def'])
            self.st[Bs] = s
        self.keymin = {}
        for Bs, s in self.st.items():
            k = (s['x'], Bs[s['x']])
            self.keymin[k] = min(self.keymin.get(k, 10 ** 9), s['def'])

    def state(self, Bs):
        I = self.I; n = I.n
        N = [I.needs(i, Bs[i]) for i in range(n)]
        NA = 0
        for q in N: NA |= q
        used = 0
        for B in Bs: used |= B
        J = I.ALL & ~used
        F = [pc(Bs[i]) == 1 and bool(Bs[i] & NA) for i in range(n)]
        x = F.index(True)
        hv = [I.val(i, Bs[i]) for i in range(n)]
        own = {}
        for o in range(n):
            if F[o]: continue
            others = 0
            for j in range(n):
                if j != o: others |= N[j]
            best, arg = -1, []
            Jl = list(bits(J))
            for k in range(len(Jl) + 1):
                for K in itertools.combinations(Jl, k):
                    X = Bs[o] | mask(K)
                    if any(I.threat(w, X, hv[w]) for w in range(n) if w != o): continue
                    NA2 = others | I.needs(o, X)
                    u = sum(1 for j in range(n) if j != o and F[j] and not (Bs[j] & NA2))
                    val = pc(X) + u
                    if val > best: best, arg = val, [(X, u)]
                    elif val == best: arg.append((X, u))
            own[o] = (best, arg)
        V = max(v for v, _ in own.values())
        return {'N': N, 'NA': NA, 'J': J, 'F': F, 'x': x, 'hv': hv, 'own': own, 'V': V, 'def': self.om + 2 - V}


def bigtop_on(I, x, g):
    vs = sorted(I.v[x].values(), reverse=True)
    return len(vs) == 4 and I.v[x][g] == vs[0] and vs[0] > vs[1] + vs[2]


def analyse(pr, Bs, cnt):
    I = pr.I; s = pr.st[Bs]; n = I.n; om = pr.om
    x = s['x']; gm = Bs[x]; g = next(bits(gm))
    needers = [i for i in range(n) if s['N'][i] & gm]
    cnt['t3stage'] += 1
    t3 = t3move(pr, Bs)
    if not t3: cnt['no_t3move_any_t3stage'] += 1
    if len(needers) != 1: cnt['t3stage_more_needers'] += 1; return
    z = needers[0]
    cnt['t3stage_1needer'] += 1
    bt = bigtop_on(I, x, g)
    cnt['bt' if bt else 'not_bt'] += 1
    cnt['def1' if s['def'] == 1 else 'def_ge2'] += 1
    hv = s['hv']; J = s['J']
    L = I.R[x] & ~gm
    trip = []
    for o, (val, arg) in s['own'].items():
        if val != s['V']: continue
        for X, u in arg:
            if u: cnt['_u'] += 1
            for c in bits(J & ~X):
                Y = X | (1 << c)
                if I.threat(x, Y, hv[x]) and not any(I.threat(w, Y, hv[w]) for w in range(n) if w not in (o, x)):
                    trip.append((o, X, u, c))
    if any(u for o, (val, arg) in s['own'].items() if val == s['V'] for X, u in arg): cnt['u_at_best'] += 1
    if trip: cnt['sx1'] += 1
    else: cnt['no_sx1'] += 1
    if any(o != z for o, _, _, _ in trip): cnt['sx1_o_not_z'] += 1
    if any(o == z for o, _, _, _ in trip): cnt['sx1_o_is_z'] += 1
    kinds = c3(pr, Bs, x, z, g, L) if bt else set()
    cnt['c3' if kinds else 'no_c3'] += 1
    if 'none' in kinds: cnt['c3_nohelper'] += 1
    if 'best' in kinds: cnt['c3_helper_best'] += 1
    if 'other' in kinds: cnt['c3_helper_other'] += 1
    cnt['t3move' if t3 else 'no_t3move_1needer'] += 1
    if I.R[z] == I.R[x]: cnt['twin'] += 1
    if bigtop_on(I, z, g): cnt['z_bigtop'] += 1
    r = rules(pr, Bs, x, z, g, L, trip) if bt else 0
    if r & 1: cnt['propC'] += 1
    if r & 2: cnt['escape'] += 1
    cnt['propC_or_escape' if r else 'no_rule'] += 1


def swap(pr, Bs, x, z, g, A, h=None, Bh=None):
    b = list(Bs); b[z] = 1 << g; b[x] = A
    if h is not None: b[h] = Bh
    b = tuple(b)
    assert b in pr.st, ('Lemma 6: swap not min-frozen', Bs, b)
    return b


def safe_after(pr, Bs, x, z, g, Z, h=None, Bh=None):
    I = pr.I; hold = list(pr.st[Bs]['hv']); hold[z] = I.v[z][g]
    if h is not None: hold[h] = I.val(h, Bh)
    return not any(I.threat(w, Z, hold[w]) for w in range(I.n) if w != x)


def c3(pr, Bs, x, z, g, L):
    I = pr.I; s = pr.st[Bs]; out = set()
    A = mask(sorted(bits(L), key=lambda q: -I.v[x][q])[:2])
    for h in [None] + [h for h in range(I.n) if h not in (x, z) and not s['F'][h]]:
        G = s['J'] | Bs[z] | (Bs[h] if h is not None else 0)
        if L & ~G: continue
        cands = [None] if h is None else []
        if h is not None:
            reg = list(bits((G & ~L) & I.R[h]))
            for k in (1, 2):
                for S in itertools.combinations(reg, k):
                    S = mask(S)
                    if (Bs[h] & ~S) and not I.needs(h, S): cands.append(S)
        for Bh in cands:
            W = G & ~(Bh or 0); rest = list(bits(W & ~L)); best = -1
            for k in range(len(rest), -1, -1):
                for K in itertools.combinations(rest, k):
                    if safe_after(pr, Bs, x, z, g, L | mask(K), h, Bh): best = pc(L) + k; break
                if best >= 0: break
            if best < 0 or best + 1 <= s['V']: continue
            b2 = swap(pr, Bs, x, z, g, A, h, Bh)
            assert pr.st[b2]['def'] <= pr.om + 1 - best and pr.st[b2]['def'] < s['def'], ('Corollary 8.2 violated', Bs, b2)
            out.add('none' if h is None else ('best' if s['own'][h][0] == s['V'] else 'other'))
    return out


def rules(pr, Bs, x, z, g, L, trip):
    I = pr.I; s = pr.st[Bs]; J = s['J']; om = pr.om; res = 0
    A = mask(sorted(bits(L), key=lambda q: -I.v[x][q])[:2])
    def check(Z, h=None, Bh=None):
        assert safe_after(pr, Bs, x, z, g, Z, h, Bh), ('construction unsafe', Bs, Z)
        b2 = swap(pr, Bs, x, z, g, A, h, Bh)
        assert pr.st[b2]['def'] <= om + 1 - pc(Z) and pr.st[b2]['def'] <= 0, ('construction: deficit', Bs, b2)
    for o, X, u, c in trip:
        Y = X | (1 << c)
        if o == z:
            if u: continue
            if safe_after(pr, Bs, x, z, g, Y): check(Y); res |= 1; continue
            assert bigtop_on(I, z, g) and not (I.R[z] & ~(1 << g) & ~Y), ('Corollary B2', Bs)
            Lz = I.R[z] & ~(1 << g)
            if Lz != L: check(Y & ~(1 << next(bits(Lz & ~L)))); res |= 1
            elif om == 2: check(L); res |= 1
        else:
            Rest = (J & ~Y) | Bs[z]
            reg = list(bits((Y | Rest) & ~L & I.R[o] & ~(1 << g)))
            for k in (1, 2):
                for S in itertools.combinations(reg, k):
                    S = mask(S)
                    if pc(S & Y) > 1 or I.needs(o, S): continue
                    helper = bool(Bs[o] & ~S)
                    if not helper and not (S == Bs[o] and not (L & Bs[o]) and pc(S) == 1): continue
                    if I.threat(o, Y & ~S, I.val(o, S)): continue
                    check(Y & ~S, o if helper else None, S if helper else None); res |= 2
    return res


def t3move(pr, Bs):
    I = pr.I; s = pr.st[Bs]; x = s['x']; gm = Bs[x]
    for b2, s2 in pr.st.items():
        if s2['def'] >= s['def'] or s2['F'][x]: continue
        z = s2['x']
        if s['F'][z] or b2[z] != gm or not (s['N'][z] & gm): continue
        ch = [i for i in range(I.n) if b2[i] != Bs[i] and i not in (x, z)]
        if len(ch) > 1: continue
        if ch and not (Bs[ch[0]] & ~b2[ch[0]]): continue
        return True
    return False


def profiles(argv, opt):
    if argv[0] == 'catalog':
        recs = json.load(gzip.open(argv[1], 'rt'))['records'][::int(opt.get('every', 1))]
        if 'max' in opt: recs = recs[:int(opt['max'])]
        for r in recs: yield {'sets': r['core']['sets'], 'vals': r['vals'], 'm': r['core']['m']}
    elif argv[0] == 'dump':
        seen = set()
        for l in gzip.open(argv[1], 'rt'):
            d = json.loads(l); key = json.dumps([d['core']['sets'], d['vals']])
            if key in seen: continue
            seen.add(key); yield {'sets': d['core']['sets'], 'vals': d['vals'], 'm': d['core']['m']}
    else:
        for d in json.load(open(argv[1])): yield d


def main(argv):
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    args = [a for a in argv if not a.startswith('--')]
    print('# command: python3 k4/oneneeder_check.py ' + ' '.join(argv), flush=True)
    tot = collections.Counter()
    for d in profiles(args, opt):
        tot['prof'] += 1
        pr = Prof(d, 'check' in opt)
        if not pr.ok: continue
        tot['f1om1'] += 1
        cnt = collections.Counter()
        for Bs, s in pr.st.items():
            if s['def'] <= 0: continue
            cnt['states'] += 1
            if s['def'] != pr.keymin[(s['x'], Bs[s['x']])]: continue
            analyse(pr, Bs, cnt)
        if 'per' in opt: print('P', json.dumps(d), dict(cnt), flush=True)
        tot.update(cnt)
    tot.pop('_u', None)
    print('total: ' + ', '.join(f'{k} {v}' for k, v in sorted(tot.items())), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
