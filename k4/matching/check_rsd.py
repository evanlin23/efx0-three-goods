"""Independent checker of RSD witnesses (iterated reduction, k4/matching.md §6; written by rsd.py with RSD_WIT).
Self-contained: it imports no code of k4/matching or k4/sdc.  Raw definitions only.

For every start (sets, vals, picks, orders) and its witness, from scratch:
  0. the picks are the SD picks of the first stored order (or of some order, if none is stored), and every agent picks;
  then for each reduction step, at the current instance (the present agents, the present goods):
  1. k is present and dangerous there: its single good is wanted by another present agent, and it values a junk good
     of the current instance;
  2. P = (k, x_1, ..., x_t) is canonical: distinct present agents, each x_i wants x_{i-1}'s single good and takes it;
     k takes T, inside (junk + B_{x_t}) and k's relevant goods, worth more to k than its good; nobody else changes; the
     stored state is the result;
  3. (L*): T threatens no other present agent at its value in the new state;
  4. after deleting k and T, every present bundle is a single good and the state is the SD outcome of some order of
     the smaller instance;
  witnesses of round_rsd.py instead list rounds: each settlement is checked as in 1-2 at the round's start, the
  chains and sets are disjoint, the state is all of them applied at once, (L*) holds at the round's end (skipped with
  DEFER=1), and 4 holds after deleting all of them;
  finally:
  5. the allocation keeps every bundle of the last state; deleted agents hold exactly their T; one present owner
     takes any number of the remaining goods and every other present agent at most one; it partitions the goods and
     is EFX0 in the original instance (raw).

    python3 k4/matching/check_rsd.py STARTS WITNESSES      (STARTS as for check_rec.py)"""
import sys, gzip, json, itertools, collections, time


class Inst:
    def __init__(self, sets, vals):
        self.n = len(sets); self.v = [dict(zip(s, x)) for s, x in zip(sets, vals)]

    def V(self, i, S): return sum(self.v[i].get(g, 0) for g in S)

    def threat(self, i, S, t):
        return bool(S) and self.V(i, S) - min(self.v[i].get(g, 0) for g in S) > t

    def efx0(self, X):
        return not any(self.threat(i, X[j], self.V(i, X[i])) for i in range(self.n) for j in range(self.n) if j != i)

    def sd(self, order, goods):
        taken = set(); Y = {}
        for i in order:
            av = [g for g in self.v[i] if g in goods and g not in taken]
            if av:
                g = max(av, key=lambda h: (self.v[i][h], -h)); Y[i] = g; taken.add(g)
        return Y


DEFER = bool(__import__('os').environ.get('DEFER'))   # ROUND witnesses written with LSTAR=defer


def check(sets, st, w):
    w0 = w
    I = Inst(sets, st['vals']); n = I.n; m = 1 + max(max(s) for s in sets); allg = set(range(m))
    picks = list(st['picks'])
    orders = st.get('orders') or ([st['order']] if 'order' in st else None)
    if orders:
        Y = I.sd(orders[0], allg)
    else:
        Y = next((y for y in (I.sd(o, allg) for o in itertools.permutations(range(n))) if [y.get(i) for i in range(n)] == picks), {})
    assert [Y.get(i) for i in range(n)] == picks and len(Y) == n, '0: picks'
    B = [[g] for g in picks]; alive = list(range(n)); goods = set(allg); dead = {}
    if 'rounds' in w:
        for rd in w['rounds']:
            J = [g for g in goods if all(g not in B[i] for i in alive)]
            wants = lambda i, g: g not in B[i] and I.v[i].get(g, 0) > I.V(i, B[i])
            exp = [list(b) for b in B]; used_agents = []; used_T = []
            for s in rd['settled']:
                k, T, P = s['k'], sorted(s['T']), s['P']
                assert k in alive and len(B[k]) == 1, 'R1: k present'
                assert any(i != k and wants(i, B[k][0]) for i in alive), 'R1: k frozen'
                assert any(g in I.v[k] for g in J), 'R1: k values a junk good'
                assert P[0] == k and len(set(P)) == len(P) >= 2 and all(x in alive for x in P), 'R2: chain agents'
                for a in range(1, len(P)):
                    assert len(B[P[a]]) == 1 and wants(P[a], B[P[a - 1]][0]), 'R2: canonical'
                assert set(T) <= (set(J) | set(B[P[-1]])) and all(g in I.v[k] for g in T), 'R2: T in the pool'
                assert I.V(k, T) > I.V(k, B[k]), 'R2: k gains'
                used_agents += P; used_T += T
                exp[k] = list(T)
                for a in range(1, len(P)): exp[P[a]] = list(B[P[a - 1]])
            assert len(used_agents) == len(set(used_agents)) and len(used_T) == len(set(used_T)), 'R3: disjoint'
            new = [list(b) for b in rd['state']]
            assert [sorted(b) for b in exp] == [sorted(b) for b in new], 'R3: state'
            if not DEFER:
                assert not any(I.threat(i, sorted(s['T']), I.V(i, new[i])) for s in rd['settled'] for i in alive
                               if i != s['k']), "R4: (L*) at the round's end"
            K = [s['k'] for s in rd['settled']]
            for s in rd['settled']: dead[s['k']] = sorted(s['T']); goods -= set(s['T'])
            alive = [a for a in alive if a not in K]; B = new
            assert all(len(B[i]) == 1 for i in alive), 'R5: perfect'
            target = {i: B[i][0] for i in alive}
            assert not alive or any(I.sd(o, goods) == target for o in itertools.permutations(alive)), 'R5: SD outcome'
        w = dict(w, steps=[])
    for t, s in enumerate(w['steps']):
        k, T, P, new = s['k'], sorted(s['T']), s['P'], [list(b) for b in s['state']]
        J = [g for g in goods if all(g not in B[i] for i in alive)]
        wants = lambda i, g: g not in B[i] and I.v[i].get(g, 0) > I.V(i, B[i])
        assert k in alive and len(B[k]) == 1, '1: k present'
        assert any(i != k and wants(i, B[k][0]) for i in alive), '1: k frozen'
        assert any(g in I.v[k] for g in J), '1: k values a junk good'
        assert P[0] == k and len(set(P)) == len(P) >= 2 and all(x in alive for x in P), '2: chain agents'
        for a in range(1, len(P)):
            assert len(B[P[a]]) == 1 and wants(P[a], B[P[a - 1]][0]), '2: canonical'
        assert set(T) <= (set(J) | set(B[P[-1]])) and all(g in I.v[k] for g in T), '2: T in the pool'
        assert I.V(k, T) > I.V(k, B[k]), '2: k gains'
        exp = [list(b) for b in B]; exp[k] = list(T)
        for a in range(1, len(P)): exp[P[a]] = list(B[P[a - 1]])
        assert [sorted(b) for b in exp] == [sorted(b) for b in new], '2: state'
        assert not any(I.threat(i, T, I.V(i, new[i])) for i in alive if i != k), '3: (L*)'
        alive = [a for a in alive if a != k]; goods -= set(T); dead[k] = T; B = new
        assert all(len(B[i]) == 1 for i in alive), '4: perfect'
        target = {i: B[i][0] for i in alive}
        assert any(I.sd(o, goods) == target for o in itertools.permutations(alive)), '4: SD outcome'
    A = [list(b) for b in w['alloc']]
    assert all(set(B[i]) <= set(A[i]) for i in range(n)), '5: bases kept'
    assert all(sorted(A[k]) == T for k, T in dead.items()), '5: deleted agents hold T'
    extra = {i: len(A[i]) - len(B[i]) for i in alive}
    assert sum(1 for i in alive if extra[i] > 1) <= 1, '5: one absorber'
    assert sorted(g for b in A for g in b) == sorted(allg), '5: partition'
    assert I.efx0(A), '5: EFX0'
    if 'rounds' in w0:
        return 'rounds %d, sizes %s' % (len(w0['rounds']), [[len(s['T']) for s in rd['settled']] for rd in w0['rounds']])
    return 'steps %d, sizes of T %s' % (len(w['steps']), [len(s['T']) for s in w['steps']])


def load(path):
    if path.endswith('.json.gz'):
        d = json.load(gzip.open(path, 'rt'))
        return [(hg['sets'], s) for hg in d['hypergraphs'] for s in hg['starts']]
    op = gzip.open if path.endswith('.gz') else open
    return [(r['sets'], r) for r in (json.loads(l) for l in op(path, 'rt') if l.strip())]


if __name__ == '__main__':
    t0 = time.time(); rows = []
    W = json.load(gzip.open(sys.argv[-1], 'rt'))['witnesses']
    for p in sys.argv[1:-1]: rows += load(p)
    seen = set(); R = []
    for sets, st in rows:
        kk = json.dumps([sets, st['vals'], list(st['picks'])])
        if kk not in seen: seen.add(kk); R.append((sets, st))
    print('$ python3 k4/matching/check_rsd.py', *sys.argv[1:], '|', len(R), 'distinct starts,', len(W), 'witnesses', flush=True)
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
