#!/usr/bin/env python3
"""DL on the key graph (workstream proof/k4-sx; k4/sx.md). EVIDENCE tooling.

Setting (k4/dl13.md §2.3 Remark, on branch proof/k4-dl13): a strict profile of a k = 4 core with fewest frozen agents
f >= 1 and omega >= 1. The *key* of a min-frozen P in the space 𝒫 of k4/c4x.md §1 is its frozen agents with their goods
(phi: F -> 𝒩). def*(κ) is the least removal-only deficit of a min-frozen P with key κ. κ' is a *neighbour* of κ for an
edge set E if some state P of κ has a move of E to a min-frozen P' with key κ'. DL on the key graph (DLK_E): every key κ
with def*(κ) > 0 has a neighbour κ' with def*(κ') < def*(κ). Edge sets:
  T3   a role swap with a needer and at most one helper (k4/dl2.md (T3)): NA' = NA; exactly one changed agent x frozen in
       P and free in P'; exactly one z free in P and frozen in P', with B'_z = B_x and B_x ⊆ N_z(B_z); no changed agent
       frozen in both; at most one other changed agent h (free in both) and it gives up a good (B_h \\ B'_h nonempty);
  T3+  the frozen-chain role swap (the coordinator's (T3⁺)): as T3, but W = the changed agents frozen in both may be
       nonempty, and the bases of W ∪ {z} in P' are the bases of W ∪ {x} in P (z takes a good it needs in P); T3 is
       the case W = ∅;
  T4   only frozen agents change, all stay frozen, NA' = NA (a permutation of the frozen goods among the frozen agents).
At f = 1, T3+ = T3 and T4 is empty. Also tested: SKG_E, "every key with def* > 0 has a neighbour with def* <= 0".

The moves are generated from each state (x, z, W, the bijection, helper h and its new base, x's new base A inside
J ∪ B_z ∪ B_h minus B'_h) and looked up among the min-frozen states; the deficit of every min-frozen state is Lemma H1's
(k4/dl2_classify.PA.deficit; --check asserts it against k4/suite/model.py's direct removal-only deficit).

usage: python3 k4/sx_keygraph.py catalog FILE [--every=E] [--start=S] [--max=N] [--fmin=F] [--fmax=F] [--dump=OUT.jsonl.gz] [--check]
       python3 k4/sx_keygraph.py certs FILE --rand=K [--seed=S] [...]     (random strict profiles per core)
       python3 k4/sx_keygraph.py certs FILE [...]                         (every strict profile of every core)
       python3 k4/sx_keygraph.py suite [...]
       python3 k4/sx_keygraph.py one '{"sets": ..., "vals": ..., "m": ...}'
       python3 k4/sx_keygraph.py inst LIST.json [...]                      (a JSON list of {id, sets, vals, m})
--dump writes one JSON line per profile that has a key with def* > 0 (the profile, every key with def* and its
neighbours per edge set). Prints counters and every failure."""
import collections, gzip, itertools, json, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc, mask
from dl2_classify import PA, INF

EDGESETS = ('T3', 'T3+', 'T3T4', 'T3+T4')


def keyof(P):
    return tuple(next(bits(P.Bs[i])) if P.frozen[i] else None for i in range(P.I.n))


class KeyProfile:
    """the min-frozen states of one strict profile, grouped by key, with deficits and key-level neighbours"""

    def __init__(self, d, check=False):
        I = M.Inst(d['sets'], d['vals'], d.get('m'))
        I.preallocs()
        self.I, self.d = I, d
        self.ok = I.omega >= 1 and I.f >= 1
        if not self.ok: return
        self.mp = [Bs for Bs, NA in I.minP]
        self.S = set(self.mp)
        self.PA = {Bs: PA(I, Bs) for Bs in self.mp}
        self.D = {}
        for Bs in self.mp:
            dv = self.PA[Bs].deficit()[0]
            if check:
                ref = I.deficit(Bs)
                assert dv == (INF if ref is None else ref), ('deficit mismatch', Bs)
            self.D[Bs] = dv
        self.K = collections.defaultdict(list)
        for Bs in self.mp: self.K[keyof(self.PA[Bs])].append(Bs)
        self.dstar = {k: min(self.D[b] for b in v) for k, v in self.K.items()}

    # ------------------------------------------------------------------ moves
    def _close(self, P, Bs, b2, x):
        """b2 (tuple) is a min-frozen state with the same needed set, x free in it: return it, else None"""
        if b2 not in self.S: return None
        P2 = self.PA[b2]
        if P2.NA != P.NA or P2.frozen[x]: return None
        return b2

    def t3plus_moves(self, Bs):
        """every (T3+) move from Bs: list of (B2, x, z, W, h); W = () is (T3)"""
        I, P = self.I, self.PA[Bs]
        F = [i for i in range(I.n) if P.frozen[i]]
        out = []
        for x in F:
            for z in P.free:
                for r in range(len(F)):
                    for W in itertools.combinations([w for w in F if w != x], r):
                        src = [x] + list(W)              # the goods B_x, B_w (w in W)
                        tgt = [z] + list(W)
                        for perm in itertools.permutations(src):
                            # tgt[i] takes the good of perm[i]
                            if not (P.N[z] & Bs[perm[0]]): continue
                            if any(perm[j + 1] == W[j] for j in range(len(W))): continue   # every w in W changes
                            for h in [None] + [w for w in P.free if w != z]:
                                G = P.J | Bs[z] | (Bs[h] if h is not None else 0)
                                hopts = [None] if h is None else [
                                    mask(c) for k in range(3) for c in itertools.combinations(list(bits(G & I.R[h])), k)
                                    if Bs[h] & ~mask(c)]
                                for Bh in hopts:
                                    G2 = G & ~(Bh or 0)
                                    for k in range(3):
                                        for c in itertools.combinations(list(bits(G2 & I.R[x])), k):
                                            b2 = list(Bs)
                                            for i, s in zip(tgt, perm): b2[i] = Bs[s]
                                            b2[x] = mask(c)
                                            if h is not None: b2[h] = Bh
                                            b2 = self._close(P, Bs, tuple(b2), x)
                                            if b2 is None: continue
                                            if not all(self.PA[b2].frozen[i] for i in tgt): continue
                                            out.append((b2, x, z, tuple(W), h))
        return out

    def t4_moves(self, Bs):
        I, P = self.I, self.PA[Bs]
        F = [i for i in range(I.n) if P.frozen[i]]
        goods = [Bs[i] for i in F]
        out = []
        for perm in itertools.permutations(goods):
            if list(perm) == goods: continue
            b2 = list(Bs)
            for i, gg in zip(F, perm): b2[i] = gg
            b2 = tuple(b2)
            if b2 in self.S and self.PA[b2].NA == P.NA and all(self.PA[b2].frozen[i] for i in F):
                out.append(b2)
        return out

    def neighbours(self):
        """{edge set: {key: set of neighbour keys}}"""
        nb = {e: collections.defaultdict(set) for e in EDGESETS}
        for Bs in self.mp:
            k0 = keyof(self.PA[Bs])
            for b2, x, z, W, h in self.t3plus_moves(Bs):
                k2 = keyof(self.PA[b2])
                nb['T3+'][k0].add(k2); nb['T3+T4'][k0].add(k2)
                if not W:
                    nb['T3'][k0].add(k2); nb['T3T4'][k0].add(k2)
            if self.I.f >= 2:
                for b2 in self.t4_moves(Bs):
                    k2 = keyof(self.PA[b2])
                    nb['T3T4'][k0].add(k2); nb['T3+T4'][k0].add(k2)
        return nb


def ks(k): return ','.join('-' if g is None else str(g) for g in k)


def run_one(d, check=False):
    kp = KeyProfile(d, check)
    if not kp.ok: return None
    nb = kp.neighbours()
    keys = []
    for k in kp.K:
        rec = {'key': ks(k), 'f': kp.I.f, 'def*': kp.dstar[k], 'states': len(kp.K[k])}
        if kp.dstar[k] > 0:
            for e in EDGESETS:
                rec['nb_' + e] = sorted((ks(k2), kp.dstar[k2]) for k2 in nb[e][k])
                rec['DLK_' + e] = any(kp.dstar[k2] < kp.dstar[k] for k2 in nb[e][k])
                rec['SKG_' + e] = any(kp.dstar[k2] <= 0 for k2 in nb[e][k])
        keys.append(rec)
    return kp, keys


def items(mode, rest, opt):
    if mode == 'one':
        d = json.loads(rest[0]); d.setdefault('m', 1 + max(g for S in d['sets'] for g in S))
        return [(d, 'one')]
    if mode == 'inst':                        # a JSON list of {id, sets, vals, m}
        return [({'sets': d['sets'], 'vals': d['vals'], 'm': d['m']}, d.get('id', 'inst%d' % i))
                for i, d in enumerate(json.load(gzip.open(rest[0], 'rt') if rest[0].endswith('.gz') else open(rest[0])))]
    if mode == 'catalog':
        recs = json.load(gzip.open(rest[0], 'rt'))['records']
        fmin = int(opt.get('fmin', 1)); fmax = int(opt.get('fmax', 99))
        recs = [r for r in recs if fmin <= r.get('f', 1) <= fmax][::int(opt.get('every', 1))]
        recs = recs[int(opt.get('start', 0)):]
        if 'max' in opt: recs = recs[:int(opt['max'])]
        base = os.path.basename(rest[0]).replace('.json.gz', '')
        return [({'sets': r['core']['sets'], 'vals': r['vals'], 'm': r['core']['m']},
                 '%s:%s[m=%d,idx=%d]:%s' % (base, r['core']['file'], r['core']['m'], r['core']['idx'],
                                            ','.join(map(str, r['prof'])))) for r in recs]
    from dl2_relations import items_of
    return items_of(mode, rest, opt)


def main(argv):
    if not argv: print(__doc__); return
    mode = argv[0]; rest = [a for a in argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in argv[1:] if a.startswith('--') and '=' in a)
    check = '--check' in argv
    print('# command: python3 k4/sx_keygraph.py ' + ' '.join(argv), flush=True)
    its = items(mode, rest, opt)
    fo = gzip.open(opt['dump'], 'wt') if 'dump' in opt else None
    cnt = collections.Counter(); t0 = time.time(); fails = collections.defaultdict(list)
    for d, src in its:
        res = run_one(d, check)
        cnt['profiles'] += 1
        if res is None: continue
        kp, keys = res
        f = kp.I.f
        cnt['profiles f>=1, omega>=1'] += 1; cnt['profiles f=%d' % f] += 1
        bad = [r for r in keys if r['def*'] > 0]
        for r in keys:
            cnt['keys f=%d' % f] += 1
            cnt['keys f=%d def*=%s' % (f, r['def*'] if r['def*'] < INF else 'inf')] += 1
        for r in bad:
            cnt['keys def*>0 f=%d' % f] += 1
            for e in EDGESETS:
                if not r['DLK_' + e]:
                    cnt['DLK_%s FAIL f=%d' % (e, f)] += 1
                    fails['DLK_' + e].append((src, d, r))
                if not r['SKG_' + e]:
                    cnt['SKG_%s fail f=%d' % (e, f)] += 1
                    if len(fails['SKG_' + e]) < 20: fails['SKG_' + e].append((src, d, r))
        if bad:
            cnt['profiles with a key def*>0 f=%d' % f] += 1
            if fo:
                fo.write(json.dumps({'src': src, 'sets': d['sets'], 'vals': d['vals'], 'm': d['m'], 'f': f,
                                     'omega': kp.I.omega, 'keys': keys}, separators=(',', ':')) + '\n')
    if fo: fo.close()
    for k in sorted(cnt): print('%-45s %d' % (k, cnt[k]))
    for e in EDGESETS:
        print('DLK_%s failures: %d' % (e, len(fails['DLK_' + e])))
        for src, d, r in fails['DLK_' + e][:50]:
            print('  FAIL %s %s key %s def* %s nb %s' % (e, src, r['key'], r['def*'], r['nb_' + e]))
            print('       sets=%s vals=%s m=%d' % (d['sets'], d['vals'], d['m']))
    for e in ('T3', 'T3+T4'):
        for src, d, r in fails['SKG_' + e][:5]:
            print('  SKG-fail %s %s key %s def* %s nb %s' % (e, src, r['key'], r['def*'], r['nb_' + e]))
    print('# time %.1f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
