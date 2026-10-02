"""The (T3+) repairs at the (r', Λ')-maxima of the f >= 2 keys with def* > 0 where neither Lemma A+ nor Lemma B+ of
k4/sx.md §6 applies (workstream proof/k4-sx; k4/sx.md §6, "What f >= 2 still needs"). EVIDENCE tooling.

Written by the f >= 2 referee in the PR #80 review (scratch file classify.py) and committed here with only this
docstring, the path setup, and the "# command" / "# time" lines changed. It uses this workstream's model
(k4/suite/model.py through k4/sx_keygraph.py and k4/sx_f2.py), so it is not an independent implementation.

For every such maximum it records the improving (T3+) moves from its state P_Q: |W|, whether a helper takes part,
the role of z, and who the best owners of the image are (x, the helper, a leaf, another agent), with the size of the
owner's bundle relative to omega and its slack u. Counters:
  "Lemma C shape": a move with W = ∅ and no helper whose image is owned by a leaf with a bundle of omega + 2 goods;
  "iota shape" (k4/dl13.md Lemma 9's ι, the mechanism of Lemma C′): W = ∅, no helper, owned by x with a bundle of
  omega + 1 goods and u >= 1;
  and a widened A+ (the leaf's bundle may threaten frozen agents of the chain, each safe at its new good).

usage: python3 k4/sx_f2_classify.py INST.json | DUMP.jsonl.gz ...   (the f >= 2 profiles of each input)"""
import sys, os, collections, itertools, gzip, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, 'suite'))
import model as M
from model import bits, pc, mask
from sx_keygraph import KeyProfile, keyof, ks
from dl2_classify import PA
import sx_f2


def covered_AB(kp, k, c):
    cnt = collections.Counter(); ex = collections.defaultdict(list)
    return None


def analyse(kp, k, tot, small):
    I = kp.I
    F = [i for i in range(I.n) if k[i] is not None]
    Nm = mask(k[i] for i in F)
    free = [i for i in range(I.n) if k[i] is None]
    U = {y: I.R[y] & ~Nm for y in range(I.n)}
    cs = I.configs([k])
    lev = lambda c: sum(I.level(y, c.Q[y] & I.R[y]) for y in free)
    rob = lambda c: sum(1 for y in free if c.robust(y))
    best = max((rob(c), lev(c)) for c in cs)
    mx = [c for c in cs if (rob(c), lev(c)) == best]
    ds = kp.dstar[k]
    # A+/B+ coverage per maximum: reuse sx_f2 on a one-maximum basis by re-running analyse_key and comparing totals
    cnt = collections.Counter(); ex = collections.defaultdict(list)
    sx_f2.analyse_key(kp, k, cnt, ex, 10 ** 6)
    unc = set(e[2] for e in ex['noAplus'])
    keyunc = cnt['keys: Lemma A+ or B+ at some Zmax=False'] == 1
    tot['keys'] += 1
    if not keyunc: return
    tot['uncovered keys'] += 1
    small.append((I.n, I.m, I.f, ks(k), kp.d))
    keyflags = collections.Counter()
    for c in mx:
        if repr(c) not in unc: continue
        tot['uncovered maxima'] += 1
        Bs = tuple((1 << k[i]) if k[i] is not None else (c.Q[i] & U[i]) for i in range(I.n))
        P = kp.PA[Bs]
        X = {o: c.Q[o] | c.L for o in free}
        V = [o for o in free if not any(I.threat(y, X[o], c.hv(y)) for y in free if y != o)]
        out = {o: [y for y in free if y != o and I.threat(y, X[o], c.hv(y))] for o in free}
        par = {y: o2 for o2 in free for y in out[o2]}
        succ = {w: [v for v in F if v != w and P.N[v] & Bs[w]] for w in F}
        # widened A+: leaf o, chain x = w0..wj, o needs phi(wj), the frozen agents X_o threatens are inside {x} ∪ W,
        # each threatened w_i (i >= 1) safe holding phi(w_{i-1}); theta_o(X_o) <= v_o(phi(wj))
        widened = False
        for o in V:
            thr = set(x for x in F if I.threat(x, X[o], c.hv(x)))
            for x in thr:
                chains = []
                def walk(path):
                    w = path[-1]
                    if P.N[o] & Bs[w]: chains.append(list(path))
                    for v in succ[w]:
                        if v not in path: walk(path + [v])
                walk([x])
                for ch in chains:
                    if not thr <= set(ch): continue
                    if any(I.threat(ch[i], X[o], I.val(ch[i], Bs[ch[i - 1]])) for i in range(1, len(ch)) if ch[i] in thr):
                        continue
                    if I.threat(o, X[o], I.val(o, Bs[ch[-1]])): continue
                    # build and check
                    b2 = list(Bs)
                    for i in range(1, len(ch)): b2[ch[i]] = Bs[ch[i - 1]]
                    b2[o] = Bs[ch[-1]]
                    pair = next((mask(pr) for pr in itertools.combinations(list(bits(X[o])), 2)
                                 if mask(pr) & U[x] and I.admissible(x, mask(pr) & U[x], U[x])), None)
                    if pair is None: continue
                    b2[x] = pair & U[x]
                    b2 = tuple(b2)
                    ok = b2 in kp.S and kp.D[b2] <= 0
                    tot['widened A+ candidate, verified def<=0=%s, j=%d' % (ok, len(ch) - 1)] += 1
                    if ok: widened = True
        tot['uncovered maxima: widened A+ applies=%s' % widened] += 1
        if widened: keyflags['widened'] += 1
        # the improving T3+ moves from P_Q
        shapes = set()
        for (b2, x, z, Wt, h) in kp.t3plus_moves(Bs):
            if kp.D[b2] >= ds: continue
            d2, res = kp.PA[b2].deficit()
            mxv = max(b for b, _ in res.values())
            owners = [o for o, (b, _) in res.items() if b == mxv]
            roles = set()
            om = I.omega
            for o in owners:
                r0 = 'x' if o == x else ('helper' if o == h else ('leaf' if o in V else 'nonleaf'))
                sz = max(pc(Xb) for Xb in res[o][1])
                roles.add('%s|X|=w+%d,u=%d' % (r0, sz - om, mxv - sz))
            if h is None and len(Wt) == 0: tot['    W=0, no helper: owner ' + ','.join(sorted(roles))] += 1
            zr = 'z leaf' if z in V else ('z root' if z not in par else 'z inner')
            shapes.add((len(Wt), h is not None, zr, tuple(sorted(roles)), d2 <= 0))
        if not shapes: tot['uncovered maxima: NO improving T3+ move from P_Q'] += 1
        for s in shapes: tot['  repair shape |W|=%d helper=%s %s owners=%s def<=0=%s' % s] += 1
        tot['uncovered maxima: some repair with |W|=0'] += any(s[0] == 0 for s in shapes)
        tot['uncovered maxima: some repair, no helper, owner a leaf != x'] += any(
            not s[1] and any(r.startswith('leaf') for r in s[3]) for s in shapes)
        tot['uncovered maxima: some repair, owner x'] += any(any(r.startswith('x') for r in s[3]) for s in shapes)
        tot['uncovered maxima: some W=0 no-helper repair, owner x with |X|=w+1 and u>=1 (Lemma 9 iota shape)'] += any(
            s[0] == 0 and not s[1] and any(r.startswith('x|X|=w+1') and not r.endswith('u=0') for r in s[3]) for s in shapes)
        sC = any(s[0] == 0 and not s[1] and any(r.startswith('leaf|X|=w+2') for r in s[3]) for s in shapes)
        s9 = any(s[0] == 0 and not s[1] and any(r.startswith('x|X|=w+1') and not r.endswith('u=0') for r in s[3])
                 for s in shapes)
        sL1 = any(s[0] == 0 and not s[1] and any(r.startswith('leaf|X|=w+1') and not r.endswith('u=0') for r in s[3])
                  for s in shapes)
        tot['uncovered maxima: some W=0 no-helper repair, owner a leaf with |X|=w+2 (Lemma C shape)'] += sC
        tot['uncovered maxima: C shape or iota shape'] += sC or s9
        tot['uncovered maxima: C shape or iota shape (owner x or a leaf, |X|=w+1, u>=1)'] += sC or s9 or sL1
        tot['uncovered maxima: some repair with def<=0'] += any(s[4] for s in shapes)
    tot['uncovered keys: widened A+ at some max=%s' % bool(keyflags['widened'])] += 1


def main(argv):
    print('# command: python3 k4/sx_f2_classify.py ' + ' '.join(argv), flush=True)
    t0 = time.time()
    profs = []
    for fn in argv:
        if fn.endswith('.json'):
            profs += [{'sets': d['sets'], 'vals': d['vals'], 'm': d['m']} for d in json.load(open(fn))]
        else:
            for line in gzip.open(fn, 'rt'):
                r = json.loads(line)
                if r['f'] >= 2: profs.append({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']})
    tot = collections.Counter(); small = []
    for d in profs:
        kp = KeyProfile(d)
        if not kp.ok or kp.I.f < 2: continue
        for k in kp.K:
            if kp.dstar[k] > 0: analyse(kp, k, tot, small)
    for k in sorted(tot): print('%-100s %d' % (k, tot[k]))
    small.sort(key=lambda t: (t[0], t[1], t[2]))
    for s in small[:3]: print('SMALL', s)
    print('# time %.1f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
