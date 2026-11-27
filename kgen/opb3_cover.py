"""Conjecture OPB3 (kgen/n3.md §13.2) checked exhaustively on the 51 n = 3 cores of k = 4
(results/k4_certs_3.json.gz), for every strict balanced type profile and every SD order.

OPB3: if every agent has a pick, some EFX0 allocation with exactly one pick per bundle is an OC1(t >= 0) completion
of the picks.  In a core, values are positive exactly on R_i, so this reads:
  - agent i holds y_{sigma(i)} for a permutation sigma (identity, a swap = a t = 1 chain, a 3-cycle = a ring);
  - every moved agent gains, v_i(X_i) > v_i(y_i) (Lemma R's chain and ring gains, since X_i minus its non-relevant
    goods is exactly i's new base);
  - at most one agent holds two or more goods outside its base.  A moved agent's base is its held pick plus its
    relevant unpicked goods.  A fixed agent's base is its pick, except that with sigma = identity one fixed agent may
    add its relevant unpicked goods (a t = 0 move).
  - X is EFX0 (raw, over every good).

Method (as in the coverage check of k4/oc1cert/brute.py on branch compute/k4-oc1max-cert, written independently):
  - Types: own enumeration of [1, 16]^d by the signs of v(A) - v(B) over disjoint nonempty A, B. Strict means no sign
    is zero; balanced means 2 max < sum; an agent with two private goods p, q also needs v(p) + v(q) < v(rest)
    (core condition C4).  The counts must equal the list's 'domains'.
  - For every maximum matching Y with three picks, every OPB allocation X of the right shape gives a box of type
    profiles (EFX0 and the gains are per-agent conditions).  For every order, the SD region of Y is a box too.  Each
    region box must lie inside the union of the witness boxes, computed densely.
  - Two variants: "OPB3" (with the absorber condition) and "OPB, gains only" (no absorber condition).
  - Spot check: for random profiles, the box answer equals a direct brute force over all allocations from integer
    values.

With RESUME=file.jsonl, finished cores are recorded there and skipped on a rerun.

    [RESUME=F.jsonl] python3 kgen/opb3_cover.py [SPOTS]"""
import sys, os, gzip, json, itertools, collections, time, random, multiprocessing as mp
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def own_types(d):
    grid = np.array(list(itertools.product(range(1, 17), repeat=d)), dtype=np.int64)
    masks = list(range(1, 1 << d))
    sums = np.stack([grid[:, [p for p in range(d) if M >> p & 1]].sum(1) for M in masks], 1)
    pairs = [(A, B) for A in masks for B in masks if A < B and not A & B]
    sig = np.stack([np.sign(sums[:, A - 1] - sums[:, B - 1]) for A, B in pairs], 1)
    ok = (sig != 0).all(1) & (2 * grid.max(1) < grid.sum(1))
    reps = {}
    for v, s in zip(grid[ok], sig[ok]): reps.setdefault(s.tobytes(), tuple(int(a) for a in v))
    return list(reps.values())


TYPES = {d: own_types(d) for d in (3, 4)}


class Core:
    def __init__(self, sets):
        self.sets = [list(S) for S in sets]; self.n = len(sets); self.m = 1 + max(g for S in sets for g in S)
        self.R = [set(S) for S in sets]; deg = collections.Counter(g for S in sets for g in S)
        self.V = []
        for S in self.sets:
            priv = [p for p, g in enumerate(S) if deg[g] == 1]; T = TYPES[len(S)]
            if len(priv) == 2: T = [v for v in T if v[priv[0]] + v[priv[1]] < sum(v) - v[priv[0]] - v[priv[1]]]
            self.V.append(np.array([[dict(zip(S, v)).get(g, 0) for g in range(self.m)] for v in T], dtype=np.int64))

    def matchings(self):
        out = []
        def rec(i, used, cur):
            if i == self.n: out.append(tuple(cur)); return
            rec(i + 1, used, cur + [None])
            for g in self.sets[i]:
                if g not in used: rec(i + 1, used | {g}, cur + [g])
        rec(0, frozenset(), [])
        nu = max(sum(y is not None for y in Y) for Y in out)
        return nu, [Y for Y in out if sum(y is not None for y in Y) == nu]

    def val(self, i, S):
        S = list(S); return self.V[i][:, S].sum(1) if S else np.zeros(len(self.V[i]), dtype=np.int64)

    def efx0_mask(self, B, i):
        own = self.val(i, B[i]); ok = np.ones(len(self.V[i]), dtype=bool)
        for j in range(self.n):
            if j != i and B[j]:
                tot = self.val(i, B[j])
                for h in B[j]: ok &= own >= tot - self.V[i][:, h]
        return ok

    def shape(self, Y, sig, B):
        J = set(range(self.m)) - set(Y); moved = [sig[i] != i for i in range(self.n)]
        out = []
        for i in range(self.n):
            if moved[i]: out.append(len([g for g in B[i] if g in J and g not in self.R[i]]))
            else: out.append(len(B[i]) - 1)
        best = sum(c >= 2 for c in out)
        if not any(moved):
            for f in range(self.n):
                o2 = list(out); o2[f] = len([g for g in B[f] if g in J and g not in self.R[f]])
                best = min(best, sum(c >= 2 for c in o2))
        return best <= 1

    def witness_boxes(self, Y):
        J = sorted(set(range(self.m)) - set(Y)); boxes = {'OPB3': [], 'gains only': []}
        for sig in itertools.permutations(range(self.n)):
            for q in itertools.product(range(self.n), repeat=len(J)):
                B = [[Y[sig[i]]] for i in range(self.n)]
                for g, a in zip(J, q): B[a].append(g)
                masks = []
                for i in range(self.n):
                    mk = self.efx0_mask(B, i)
                    if sig[i] != i: mk &= self.val(i, B[i]) > self.V[i][:, Y[i]]
                    masks.append(mk)
                if not all(mk.any() for mk in masks): continue
                boxes['gains only'].append(masks)
                if self.shape(Y, sig, B): boxes['OPB3'].append(masks)
        return boxes

    def region(self, Y, order):
        taken = set(); out = [None] * self.n
        for i in order:
            S = [g for g in self.sets[i] if g not in taken]
            if S: picks = np.array(S)[np.argmax(self.V[i][:, S], axis=1)]; out[i] = picks == Y[i]
            else: out[i] = np.full(len(self.V[i]), Y[i] is None)
            if Y[i] is not None: taken.add(Y[i])
        return out


def cover(C, boxes):
    sizes = [len(V) for V in C.V]; cov = np.zeros(sizes, dtype=bool)
    if not boxes: return cov
    M = [np.array([b[i] for b in boxes], dtype=np.float32) for i in range(3)]
    for t in range(sizes[0]):
        sel = M[0][:, t] > 0
        if sel.any(): cov[t] = (M[1][sel].T @ M[2][sel]) > 0
    return cov


def job(arg):
    pos, rec = arg
    t0 = time.time(); C = Core(rec['sets']); out = collections.Counter(); bad = {}
    out['types match the list'] = int([len(V) for V in C.V] == rec['domains'])
    nu, Ys = C.matchings(); out['nu = %d' % nu] += 1
    if nu < 3: return pos, out, bad, time.time() - t0
    for Y in Ys:
        boxes = C.witness_boxes(Y)
        covs = {k: cover(C, b) for k, b in boxes.items()}
        for order in itertools.permutations(range(3)):
            A = C.region(Y, order)
            if not all(a.any() for a in A): continue
            idx = np.ix_(*[np.flatnonzero(a) for a in A]); out['profile x order pairs'] += int(np.prod([a.sum() for a in A]))
            for k, cov in covs.items():
                sub = cov[idx]; miss = int((~sub).sum()); out['%s: uncovered profile x order pairs' % k] += miss
                if miss and k not in bad:
                    b = np.argwhere(~sub)[0]; prof = [int(np.flatnonzero(a)[j]) for a, j in zip(A, b)]
                    bad[k] = {'picks': Y, 'order': order, 'values': [[int(C.V[i][prof[i]][g]) for g in C.sets[i]] for i in range(3)]}
    return pos, out, bad, time.time() - t0


def brute_opb(sets, vals, order, absorber):
    """direct check from integer values: does an OPB OC1 completion (or OPB with gains) exist for this order?"""
    m = 1 + max(g for S in sets for g in S); v = [[0] * m for _ in range(3)]
    for i in range(3):
        for g, x in zip(sets[i], vals[i]): v[i][g] = x
    left = set(range(m)); y = [None] * 3
    for i in order:
        av = [g for g in left if v[i][g] > 0]
        if av: y[i] = max(av, key=lambda g: v[i][g]); left.discard(y[i])
    if any(g is None for g in y): return None
    C = Core(sets)
    for q in itertools.product(range(3), repeat=m):
        B = [[g for g in range(m) if q[g] == i] for i in range(3)]
        if not all(sum(1 for g in b if g in y) == 1 for b in B): continue
        sig = [y.index(next(g for g in B[i] if g in y)) for i in range(3)]
        if any(sig[i] != i and sum(v[i][g] for g in B[i]) <= v[i][y[i]] for i in range(3)): continue
        ok = True
        for i in range(3):
            own = sum(v[i][g] for g in B[i])
            for j in range(3):
                if j != i and B[j] and any(own < sum(v[i][g] for g in B[j]) - v[i][h] for h in B[j]): ok = False
        if ok and (not absorber or C.shape(y, sig, B)): return True
    return False


if __name__ == '__main__':
    spots = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    print('$ python3 kgen/opb3_cover.py', *sys.argv[1:], flush=True)
    print('types: %d for 3 goods, %d for 4 goods' % (len(TYPES[3]), len(TYPES[4])), flush=True)
    recs = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_certs_3.json.gz')))['cores']
    T = collections.Counter(); allbad = {}
    resume = os.environ.get('RESUME')            # a .jsonl of finished cores (list position, counts); appended to
    done = {}
    if resume and os.path.exists(resume):
        for line in open(resume): r = json.loads(line); done[r['pos']] = r
    todo = [(p, r) for p, r in enumerate(recs) if p not in done]
    for p, r in sorted(done.items()):
        T.update(r['out']); T['cores'] += 1
        for k, b in r['bad'].items(): T['%s: cores with an uncovered profile' % k] += 1; allbad.setdefault(k, (p, b))
    print('resumed %d cores, %d to do' % (len(done), len(todo)), flush=True)
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for pos, out, bad, dt in pool.imap_unordered(job, todo):
            T.update(out); T['cores'] += 1
            for k, b in bad.items():
                T['%s: cores with an uncovered profile' % k] += 1; allbad.setdefault(k, (pos, b))
            if resume:
                with open(resume, 'a') as f: f.write(json.dumps({'pos': pos, 'out': dict(out), 'bad': bad}) + '\n')
            print('core at list position %2d (idx %d, m = %d): %s%s (%.0f s)' % (pos, recs[pos]['idx'], recs[pos]['m'], ', '.join('%s %d' % kv for kv in sorted(out.items()) if 'uncovered' in kv[0] and kv[1]) or 'all covered',
                  '' if out['types match the list'] else ' TYPE COUNT MISMATCH', dt), flush=True)
    for k in sorted(T): print(T[k], k)
    for k, (idx, b) in allbad.items(): print('first uncovered (%s): core at list position %d' % (k, idx), json.dumps(b))
    # spot check: box answers versus a direct brute force on concrete integer profiles
    rng = random.Random(1); agree = collections.Counter()
    small = [r for r in recs if 1 + max(g for S in r['sets'] for g in S) <= 7]
    for _ in range(spots):
        rec = rng.choice(small); C = Core(rec['sets'])
        prof = [rng.randrange(len(V)) for V in C.V]; vals = [[int(C.V[i][prof[i]][g]) for g in C.sets[i]] for i in range(3)]
        order = rng.choice(list(itertools.permutations(range(3))))
        taken = set(); Y = [None] * 3
        for i in order:
            S = [g for g in C.sets[i] if g not in taken]
            if S: Y[i] = max(S, key=lambda g: C.V[i][prof[i]][g]); taken.add(Y[i])
        if any(g is None for g in Y): agree['spot checks skipped (a pickless agent)'] += 1; continue
        boxes = C.witness_boxes(tuple(Y))
        for absorber, k in ((True, 'OPB3'), (False, 'gains only')):
            boxans = any(all(b[i][prof[i]] for i in range(3)) for b in boxes[k])
            d = brute_opb(rec['sets'], vals, order, absorber)
            agree['%s: spot checks' % k] += 1; agree['%s: box answer = direct brute force' % k] += (boxans == d)
            agree['%s: direct brute force finds one' % k] += d
    for k in sorted(agree): print(agree[k], k)
