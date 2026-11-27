"""Independent checker of OC2-REC witnesses (proof/k4-oc1max-multi's Sub-lemma OC2-REC with Lemma LIFT,
k4/oc1max_multi.md §8; written by n5_census.py with REC_WIT).  Self-contained: it imports no code of k4/matching or
k4/sdc.  Raw definitions only.

For every start (sets, vals, picks, orders) of the input and its witness it checks, from scratch:
  1. the picks are the serial-dictatorship picks of the first stored order, and every agent picks;
  2. the first chain P1 = (k = x0, ..., xt) is canonical:
     - each x_i, i >= 1, takes its predecessor's pick alone and gains;
     - k is dangerous at the picks (frozen, and values a junk good) and takes T = B1[k], with #T = 2,
       T inside J + {y_xt}, worth more to k than its pick;
     - T is worth more than its pick to a second dangerous agent;
     - B1 is the resulting state;
  3. Lemma LIFT's hypothesis: every agent i != k values each good of T below v_i(B1_i);
  4. the reduced instance I- (k and T deleted): B1 restricted to it is a perfect start, the SD outcome of the stored
     reduced order;
  5. the reduced part of B2 is the reduced part of B1, or an official move of I- from it (k4/sdc.md §29 as implemented
     by k4/sdc/oc1_mc2_rand.Inst.moves):
     - a junk grab (an agent adds relevant junk);
     - a chain from any agent: x_i takes x_{i-1}'s bundle plus relevant junk and gains, and x_0 takes relevant
       junk plus relevant goods of x_t's bundle and gains;
     - a ring;
     All three are enumerated here by brute force. B2[k] = T;
  6. the allocation keeps every bundle of B2, gives k nothing more, gives one owner o != k any junk and every other
     agent at most one junk good, partitions the goods, and is EFX0 in I (raw).

    python3 k4/matching/check_rec.py STARTS WITNESSES
      STARTS: the n = 4 export (results/k4_matching/data/two_move_starts_n4.json.gz) or a JSONL of {sets, vals,
      picks, orders} (or a single `order`); WITNESSES: the REC_WIT file of n5_census.py, written on the same input in the same order."""
import sys, os, gzip, json, itertools, collections, time


class Inst:
    def __init__(self, sets, vals):
        self.n = len(sets); self.sets = sets
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

    def sd(self, order, banned=()):
        taken = set(banned); Y = {}
        for i in order:
            av = [g for g in self.v[i] if g not in taken]
            if av:
                g = max(av, key=lambda h: (self.v[i][h], -h)); Y[i] = g; taken.add(g)
        return Y


def junk(B, goods): used = set(g for b in B.values() for g in b); return [g for g in goods if g not in used]


def sub(xs): return itertools.chain.from_iterable(itertools.combinations(xs, r) for r in range(len(xs) + 1))


def moves(I, B, goods):
    """Every official move of the instance restricted to the agents of B (a dict) and the goods `goods`."""
    ag = sorted(B); J = junk(B, goods); out = set()
    key = lambda nb: tuple((a, tuple(sorted(nb[a]))) for a in ag)
    R = {a: set(g for g in I.v[a] if g in goods) for a in ag}
    for x in ag:
        for H in sub([g for g in J if g in R[x]]):
            if H: nb = {a: list(B[a]) for a in ag}; nb[x] = list(B[x]) + list(H); out.add(key(nb))

    def ext(path, used, asg):
        xt = path[-1]
        if len(path) >= 2:
            pool = [g for g in J if g not in used and g in R[path[0]]] + [g for g in B[xt] if g in R[path[0]]]
            for H0 in sub(pool):
                if H0 and I.V(path[0], H0) > I.V(path[0], B[path[0]]):
                    nb = {a: list(B[a]) for a in ag}; nb[path[0]] = list(H0)
                    for i in range(1, len(path)): nb[path[i]] = list(B[path[i - 1]]) + list(asg[i])
                    out.add(key(nb))
        if len(path) >= len(ag) or not B[xt]: return
        for y in ag:
            if y in path: continue
            for H in sub([g for g in J if g not in used and g in R[y]]):
                if I.V(y, list(B[xt]) + list(H)) > I.V(y, B[y]): ext(path + [y], used | set(H), {**asg, len(path): H})
    for x in ag: ext([x], frozenset(), {})
    for r in range(2, len(ag) + 1):
        for cyc in itertools.permutations(ag, r):
            if cyc[0] != min(cyc): continue

            def ring(i, used, asg):
                if i == r:
                    nb = {a: list(B[a]) for a in ag}
                    for t in range(r): nb[cyc[t]] = list(B[cyc[t - 1]]) + list(asg[t])
                    out.add(key(nb)); return
                w, pred = cyc[i], cyc[i - 1]
                if not B[pred]: return
                for H in sub([g for g in J if g not in used and g in R[w]]):
                    if I.V(w, list(B[pred]) + list(H)) > I.V(w, B[w]): ring(i + 1, used | set(H), {**asg, i: H})
            ring(0, frozenset(), {})
    return out, key


def check(sets, st, w):
    I = Inst(sets, st['vals']); n = I.n; m = 1 + max(max(s) for s in sets); allg = list(range(m))
    Y = I.sd(st['orders'][0] if 'orders' in st else st['order'])
    assert [Y.get(i) for i in range(n)] == list(st['picks']) and len(Y) == n, '1: picks'
    base = {i: [Y[i]] for i in range(n)}; J = junk(base, allg)
    wants = lambda i, g, B: g not in B[i] and I.v[i].get(g, 0) > I.V(i, B[i])
    frozen = lambda j, B: len(B[j]) == 1 and any(i != j and wants(i, B[j][0], B) for i in range(n))
    dang = [x for x in range(n) if frozen(x, base) and any(g in I.v[x] for g in J)]
    P1, T, B1 = w['P1'], sorted(w['T']), {i: list(b) for i, b in enumerate(w['B1'])}
    k, xt = P1[0], P1[-1]
    assert len(set(P1)) == len(P1) >= 2 and k in dang, '2: head'
    assert sorted(B1[k]) == T and len(T) == 2 and set(T) <= set(J) | {Y[xt]}, '2: T'
    assert I.V(k, T) > I.V(k, base[k]), '2: k gains'
    for i in range(1, len(P1)):
        assert B1[P1[i]] == [Y[P1[i - 1]]] and I.V(P1[i], B1[P1[i]]) > I.V(P1[i], base[P1[i]]), '2: canonical'
    assert all(B1[i] == base[i] for i in range(n) if i not in P1), '2: others keep'
    assert any(q != k and I.V(q, T) > I.V(q, base[q]) for q in dang), '2: shared'
    assert all(I.v[i].get(g, 0) < I.V(i, B1[i]) for i in range(n) if i != k for g in T), '3: LIFT hypothesis'
    red = [i for i in range(n) if i != k]; goods = [g for g in allg if g not in T]
    order = w['reduced order']
    assert sorted(order) == red and all(len(B1[i]) == 1 for i in red), '4: perfect'
    Ym = I.sd(order, banned=T)
    assert len(Ym) == len(red) and all(B1[i] == [Ym[i]] for i in red), '4: SD outcome of the reduced instance'
    B2 = {i: list(b) for i, b in enumerate(w['B2'])}
    assert sorted(B2[k]) == T, '5: k keeps T'
    B1m = {i: B1[i] for i in red}; B2m = {i: B2[i] for i in red}
    mv, key = moves(I, B1m, goods)
    at_once = key(B2m) == key(B1m)
    assert at_once or key(B2m) in mv, '5: official move of the reduced instance'
    A = {i: list(b) for i, b in enumerate(w['alloc'])}; o = w['owner']
    assert o != k and sorted(A[k]) == T, '6: owner, k'
    assert all(set(B2[i]) <= set(A[i]) for i in range(n)), '6: bases kept'
    assert sorted(g for b in A.values() for g in b) == allg, '6: partition'
    assert all(len(A[i]) - len(B2[i]) <= 1 for i in range(n) if i != o), '6: one absorber'
    assert I.efx0([A[i] for i in range(n)]), '6: EFX0'
    return 'B1- completes at once' if at_once else 'after one move of I-'


def load(path):
    if path.endswith('.json.gz') and 'two_move_starts' in path:
        d = json.load(gzip.open(path, 'rt'))
        return [(hg['sets'], s) for hg in d['hypergraphs'] for s in hg['starts']]
    op = gzip.open if path.endswith('.gz') else open
    return [(r['sets'], r) for r in (json.loads(l) for l in op(path, 'rt') if l.strip())]


if __name__ == '__main__':
    t0 = time.time()
    rows = load(sys.argv[1]); W = json.load(gzip.open(sys.argv[2], 'rt'))['witnesses']
    seen = set(); R = []          # distinct rows, in input order (as n5_census.py indexes them)
    for sets, st in rows:
        kk = json.dumps([sets, st['vals'], list(st['picks'])])
        if kk not in seen: seen.add(kk); R.append((sets, st))
    print('$ python3 k4/matching/check_rec.py', *sys.argv[1:], '|', len(R), 'distinct starts,', len(W), 'witnesses', flush=True)
    byk = {w['k']: w for w in W}; C = collections.Counter()
    for t, (sets, st) in enumerate(R):
        if t not in byk: C['no witness'] += 1; continue
        try:
            C['verified, %s' % check(sets, st, byk[t])] += 1
        except AssertionError as e:
            C['FAILED: %s' % e] += 1
    for x in sorted(C): print(x, C[x])
    print('all starts certified:', C['no witness'] == 0 and not any(x.startswith('FAILED') for x in C))
    print('time %.0f s' % (time.time() - t0))
