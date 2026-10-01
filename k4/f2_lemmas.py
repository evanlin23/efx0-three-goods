#!/usr/bin/env python3
"""The chain lemmas of k4/f2.md §3, checked and measured (workstream proof/k4-f2). EVIDENCE tooling for written proofs.

Objects (k4/f2.md §3): a *need path* to a frozen x is z = a_{k+1}, a_k, ..., a_1, a_0 = x (k >= 0), distinct agents,
a_1..a_k frozen, z free, each a_{i+1} needing the good of a_i. The *chain swap* along it with helper h (or none): z takes
the good of a_k, each a_i (1 <= i <= k) the good of a_{i-1}, x takes A, h takes B'_h, with A, B'_h ⊆ G = J ∪ B_z ∪ B_h.
Every conclusion is asserted against the exact deficits and owner tables (k4/f2_lib.py: main's model.py and
dl2_classify.py):
  P    Lemma P: every frozen agent has a need path from a free agent, or the agents with a need walk to it are all
       frozen and contain a cycle of the frozen need digraph (so: always, at a T4-optimal P).
  L6+  Lemma 6+: every chain swap with admissible A, B'_h (N(.) ⊆ 𝒩) is min-frozen with NA(P') = NA(P),
       F(P') = F - x + z, and is a (T3+) move (k4/f2_lib.t3plus) when the helper gives up a good.
  L8+  Lemma 8+: Val_{P'}(x) = max over A ⊆ Z ⊆ G minus B'_h, Z safe for the P' bases, of |Z| + #{q ∈ 𝒩 : q ∉ N_x(Z) ∪ 𝒩'},
       𝒩' = N_z({g_k}) ∪ ⋃ N_{a_i}({g_{i-1}}) ∪ N_h(B'_h) ∪ the needs of the unmoved agents; all from P's data.
  C1+  Corollary 9.1+ (the S1 repair through a need path): o a best owner, X optimal, c ∈ J \\ X, X ∪ {c} threatens
       only a frozen x, o the free end of a need path to x, theta_o(X ∪ {c}) <= v_o(g_k): for every admissible
       A ⊆ X ∪ {c}, def(P') <= def(P) - 1 - iota (iota = 1 if nobody but o needs g_k).
  C2+  Corollary 11.1+ (the blocker swap through a need path): X ∪ {c} threatens only a free z, z the free end of a
       need path to a frozen x, theta_z(X ∪ {c}) <= v_z(g_k), A ⊆ (J ∪ B_z) minus (X ∪ {c}) admissible with
       theta_x(X ∪ {c}) <= v_x(A) and no good counted in u_o(X) in N_x(A): def(P') <= def(P) - 1.
  C3+  Corollary 8.2+ (the Lemma 7 swap through a need path): x big-top on its top g, a_1 the only needer of g, a need
       path through a_1, L_x ⊆ G, B'_h ⊆ G minus L_x admissible with g ∉ N_h(B'_h), Z ⊇ L_x a safe bundle of x in P':
       def(P') <= omega + 1 - |Z|; certified when |Z| + 1 > Val*(P).
usage: python3 k4/f2_lemmas.py DUMP.jsonl.gz ...            (T3-stage dumps of k4/f2_shapes.py: coverage, all checks)
       python3 k4/f2_lemmas.py --random N [--seed=S] [--nmax=5] [--mmax=12]   (random strict instances, not cores,
                                   biased to f >= 2; every check at every def > 0 state with f >= 1)"""
import collections, gzip, itertools, json, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from f2_lib import Prof, bits, pc, mask, tup, lst, counted, bigtop, kind, t3plus, INF
import model as M


class Ctx:
    def __init__(self, pr, Bs):
        self.pr, self.Bs, self.I = pr, Bs, pr.I
        self.P = pr.PA[Bs]; self.D = pr.D[Bs]
        self.best = pr.best(Bs); self.V = pr.V(Bs)
        self.omega = pc(self.P.J) - self.P.S
        self.F = [i for i in range(self.I.n) if self.P.frozen[i]]

    def thr(self, w, Z, hold): return self.I.threat(w, Z, self.I.val(w, hold))

    def adm(self, i, pool, kmax=2):
        I, P = self.I, self.P
        return [mask(A) for k in range(1, kmax + 1) for A in itertools.combinations(list(bits(pool & I.R[i])), k)
                if not (I.needs(i, mask(A)) & ~P.NA)]

    # ------------------------------------------------------------ need paths
    def paths_to(self, x):
        """every need path [z, a_k, ..., a_1, x] (lists) to the frozen x"""
        P, I = self.P, self.I
        out = []

        def rec(path):
            head = path[0]
            for i in range(I.n):
                if i in path or not (P.N[i] & self.Bs[head]): continue
                if P.frozen[i]: rec([i] + path)
                else: out.append([i] + path)
        rec([x])
        return out

    def lemmaP(self):
        """every frozen x: a need path from a free agent, or a need cycle among the agents with a need walk to x"""
        P, I = self.P, self.I
        for x in self.F:
            if self.paths_to(x): continue
            S, stack = {x}, [x]
            while stack:
                y = stack.pop()
                for i in range(I.n):
                    if P.N[i] & self.Bs[y] and i not in S: S.add(i); stack.append(i)
            assert all(P.frozen[i] for i in S), ('Lemma P: a free agent reaches x without a path', self.Bs, x)
            assert not self.pr.t4_optimal(self.Bs), ('Lemma P: T4-optimal but no path', self.Bs, x)
            return 1
        return 0

    def swap(self, path, A, h=None, Bh=None):
        b = list(self.Bs)
        for j in range(len(path) - 1): b[path[j]] = self.Bs[path[j + 1]]
        b[path[-1]] = A
        if h is not None: b[h] = Bh
        return tuple(b)

    def hold(self, path, h=None, Bh=None):
        """the P' bases of the moved agents other than x"""
        hd = {path[j]: self.Bs[path[j + 1]] for j in range(len(path) - 1)}
        if h is not None: hd[h] = Bh
        return hd

    def Nprime(self, path, h=None, Bh=None, skip=()):
        """𝒩' of Lemma 8+ (the needs in P' of every agent other than x and the agents in skip)"""
        I, P = self.I, self.P
        hd = self.hold(path, h, Bh); x = path[-1]
        out = 0
        for i in range(I.n):
            if i == x or i in skip: continue
            out |= I.needs(i, hd[i]) if i in hd else P.N[i]
        return out

    # ------------------------------------------------------------ Lemma 6+ and Lemma 8+
    def moves(self, kmax_paths=None):
        """every chain swap allowed by Lemma 6+: (path, A, h, Bh)"""
        I, P, Bs = self.I, self.P, self.Bs
        for x in self.F:
            for path in self.paths_to(x):
                z = path[0]
                for h in [None] + [h for h in P.free if h != z]:
                    G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
                    for A in self.adm(x, G):
                        if h is None: yield path, A, None, None; continue
                        for k in range(3):
                            for Bh in itertools.combinations(list(bits((G & ~A) & I.R[h])), k):
                                Bh = mask(Bh)
                                if I.needs(h, Bh) & ~P.NA: continue
                                yield path, A, h, Bh

    def check_6_8(self):
        pr, I, P, Bs = self.pr, self.I, self.P, self.Bs
        n6 = n8 = 0
        for path, A, h, Bh in self.moves():
            x, z = path[-1], path[0]
            b2 = self.swap(path, A, h, Bh)
            assert b2 in pr.D, ('Lemma 6+: not min-frozen', Bs, b2)
            P2 = pr.PA[b2]
            assert P2.NA == P.NA and [i for i in range(I.n) if P2.frozen[i]] == sorted(set(self.F) - {x} | {z}), \
                ('Lemma 6+: needed or frozen set', Bs, b2)
            gives = h is None or bool(Bs[h] & ~Bh)
            if gives:
                k = kind(P, P2)
                assert k == ('t3' if len(path) == 2 else 't3c'), ('Lemma 6+: not a T3+ move', Bs, b2, k)
            n6 += 1
            # Lemma 8+
            G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
            W = G & ~(Bh or 0)
            hd = self.hold(path, h, Bh)
            Np = self.Nprime(path, h, Bh)
            rest = list(bits(W & ~A)); best = -1
            for k in range(len(rest) + 1):
                for K in itertools.combinations(rest, k):
                    Z = A | mask(K)
                    if any(self.thr(w, Z, hd.get(w, Bs[w])) for w in range(I.n) if w != x): continue
                    u = sum(1 for q in bits(P.NA) if not ((1 << q) & (I.needs(x, Z) | Np)))
                    best = max(best, pc(Z) + u)
            assert best == pr.OWN[b2][x][0], ('Lemma 8+', Bs, b2, best, pr.OWN[b2][x][0])
            n8 += 1
        return n6, n8

    # ------------------------------------------------------------ the corollaries
    def single_blocks(self):
        return self.pr.single_blocks(self.Bs)

    def C1p(self, sb):
        """Corollary 9.1+; returns the (o, x, c, k) certified"""
        I, P, Bs, pr = self.I, self.P, self.Bs, self.pr
        out = []
        for o, X, c, x in sb:
            if not P.frozen[x]: continue
            Y = X | (1 << c)
            for path in self.paths_to(x):
                if path[0] != o: continue
                gk = Bs[path[1]]
                if self.thr(o, Y, gk): continue
                As = self.adm(x, Y)
                assert As, ('Corollary 9.1+: no admissible A', Bs)
                iota = 0 if any(P.N[i] & gk for i in range(I.n) if i != o) else 1
                for A in As:
                    b2 = self.swap(path, A)
                    assert b2 in pr.D and pr.D[b2] <= self.D - 1 - iota, ('Corollary 9.1+', Bs, b2)
                out.append((o, x, c, len(path) - 2))
        return out

    def C2p(self, sb):
        """Corollary 11.1+; returns the (o, z, x, c, k) certified"""
        I, P, Bs, pr = self.I, self.P, self.Bs, self.pr
        out = []
        for o, X, c, z in sb:
            if P.frozen[z]: continue
            cnt = counted(P, o, X); Y = X | (1 << c)
            for x in self.F:
                for path in self.paths_to(x):
                    if path[0] != z: continue
                    gk = Bs[path[1]]
                    if self.thr(z, Y, gk): continue
                    for A in self.adm(x, (P.J | Bs[z]) & ~Y):
                        if self.thr(x, Y, A): continue
                        if any(Bs[w] & I.needs(x, A) for w in cnt): continue
                        b2 = self.swap(path, A)
                        assert b2 in pr.D and pr.D[b2] <= self.D - 1, ('Corollary 11.1+', Bs, b2)
                        out.append((o, z, x, c, len(path) - 2))
        return out

    def C3p(self):
        """Corollary 8.2+; returns the (x, path, h) certified (first found)"""
        I, P, Bs, pr = self.I, self.P, self.Bs, self.pr
        for x in self.F:
            if not bigtop(I, x): continue
            g = Bs[x]
            if max(I.sets[x], key=lambda q: I.v[x][q]) != next(bits(g)): continue
            nd = [i for i in range(I.n) if P.N[i] & g]
            if len(nd) != 1: continue
            L = I.R[x] & ~g
            for path in self.paths_to(x):
                z = path[0]
                for h in [None] + [h for h in P.free if h != z]:
                    G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
                    if L & ~G: continue
                    hs = [None]
                    if h is not None:
                        hs = [mask(B) for k in range(3) for B in itertools.combinations(list(bits((G & ~L) & I.R[h])), k)
                              if (Bs[h] & ~mask(B)) and not (I.needs(h, mask(B)) & ~P.NA)
                              and not (I.needs(h, mask(B)) & g)]
                    for Bh in hs:
                        hd = self.hold(path, h, Bh)
                        W = G & ~(Bh or 0)
                        safe = lambda Z: not any(self.thr(w, Z, hd.get(w, Bs[w])) for w in range(I.n) if w != x)
                        if not safe(L): continue
                        rest = list(bits(W & ~L)); bestZ = None
                        for k in range(len(rest), -1, -1):
                            for K in itertools.combinations(rest, k):
                                if safe(L | mask(K)): bestZ = L | mask(K); break
                            if bestZ is not None: break
                        for A in self.adm(x, L):
                            b2 = self.swap(path, A, h, Bh)
                            assert b2 in pr.D and pr.D[b2] <= self.omega + 1 - pc(bestZ), ('Corollary 8.2+', Bs, b2)
                        if pc(bestZ) + 1 <= self.V: continue
                        return [(x, path, h)]
        return []


# ------------------------------------------------------------------ drivers
def coverage(files):
    cnt = collections.Counter(); ex = {}; cache = {}
    for fn in files:
        for r in (json.loads(l) for l in gzip.open(fn, 'rt')):
            key = json.dumps([r['sets'], r['vals']])
            if key not in cache:
                cache.clear(); cache[key] = Prof({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']}, fmin=1)
            pr = cache[key]; Bs = tup(r['Bs']); ctx = Ctx(pr, Bs)
            assert pr.t3_stage(Bs)
            cnt['states'] += 1
            cnt['Lemma P: a frozen agent without a need path (not T4-optimal)'] += ctx.lemmaP()
            n6, n8 = ctx.check_6_8(); cnt['Lemma 6+ chain swaps checked'] += n6; cnt['Lemma 8+ values checked'] += n8
            sb = ctx.single_blocks()
            c1 = ctx.C1p(sb); c2 = ctx.C2p(sb); c3 = ctx.C3p()
            plain = any(t[-1] == 0 for t in c1) or any(t[-1] == 0 for t in c2) or any(len(t[1]) == 2 for t in c3)
            first = ('C1+' if c1 else ('C2+' if c2 else ('C3+' if c3 else 'none')))
            chain_only = not any(rp['k'] == 0 for rp in r['reps'])
            row = (r['case'], 'chain-only' if chain_only else 'plain T3 exists')
            cnt[row + (first,)] += 1
            cnt[row + ('certified by a plain (k = 0) corollary' if plain else 'only by a chain corollary (k >= 1)'
                       if first != 'none' else 'not certified',)] += 1
            if first == 'none':
                cur = ex.get(r['case'])
                cand = (len(r['sets']), r['m'], r['src'], r['sets'], r['vals'], r['Bs'])
                if cur is None or cand[:2] < cur[:2]: ex[r['case']] = cand
    for k in sorted(cnt, key=str): print('  %-100s %d' % (' | '.join(k) if isinstance(k, tuple) else k, cnt[k]))
    for k in sorted(ex):
        print('  smallest uncertified, case %s: n=%d m=%d %s sets=%s vals=%s P=%s' % ((k,) + ex[k]))


def rand_inst(rng, nmax, mmax):
    """strict, strictly balanced 3- and 4-good agents, every good valued; a few 'hot' goods are many agents' tops"""
    while True:
        n = rng.randint(3, nmax)
        m = rng.randint(n + 2, min(mmax, 3 * n))
        goods = list(range(m)); hot = rng.sample(goods, rng.randint(2, 3))
        sets, vals = [], []
        for _ in range(n):
            k = rng.choice((3, 4))
            top = rng.choice(hot)
            S = [top] + rng.sample([g for g in goods if g != top], k - 1)
            while True:
                vs = [rng.randint(1, 12) for _ in S]
                vs[0] = max(vs)
                sums = [sum(c) for r in range(1, k + 1) for c in itertools.combinations(vs, r)]
                if len(set(sums)) == len(sums) and all(2 * v < sum(vs) for v in vs): break
            sets.append(S); vals.append(vs)
        if set(g for S in sets for g in S) == set(goods):
            return {'sets': sets, 'vals': vals, 'm': m}


def random_run(N, seed, nmax, mmax):
    rng = random.Random(seed); cnt = collections.Counter()
    for _ in range(N):
        d = rand_inst(rng, nmax, mmax)
        pr = Prof(d, fmin=1)
        cnt['instances'] += 1
        if not pr.ok: continue
        cnt['instances f>=1, omega>=1'] += 1; cnt['instances f=%d' % pr.I.f] += 1
        for Bs in pr.mp:
            ctx = Ctx(pr, Bs)
            cnt['Lemma P: frozen agent without a need path (not T4-optimal)'] += ctx.lemmaP()
            if pr.D[Bs] <= 0: continue
            cnt['def>0 states'] += 1; cnt['def>0 states f=%d' % pr.I.f] += 1
            n6, n8 = ctx.check_6_8(); cnt['Lemma 6+ chain swaps'] += n6; cnt['Lemma 8+ values'] += n8
            cnt['Lemma 6+ chain swaps with k >= 1 checked at f >= 2'] += 0
            sb = ctx.single_blocks()
            c1 = ctx.C1p(sb); c2 = ctx.C2p(sb); c3 = ctx.C3p()
            cnt['C1+ applies'] += bool(c1); cnt['C1+ applies with k >= 1'] += any(t[-1] >= 1 for t in c1)
            cnt['C2+ applies'] += bool(c2); cnt['C2+ applies with k >= 1'] += any(t[-1] >= 1 for t in c2)
            cnt['C3+ applies'] += bool(c3); cnt['C3+ applies with k >= 1'] += any(len(t[1]) > 2 for t in c3)
    for k in sorted(cnt): print('  %-70s %d' % (k, cnt[k]))


def main(argv):
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in argv if a.startswith('--'))
    rest = [a for a in argv if not a.startswith('--')]
    print('# command: python3 k4/f2_lemmas.py ' + ' '.join(argv), flush=True)
    if 'random' in opt:
        random_run(int(rest[0]), int(opt.get('seed', 1)), int(opt.get('nmax', 5)), int(opt.get('mmax', 12)))
    else:
        coverage(rest)
    print('# no assertion failed')


if __name__ == '__main__':
    main(sys.argv[1:])
