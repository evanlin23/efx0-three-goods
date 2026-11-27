"""RD² at n = 3 by settling one agent (kgen/rounds.md §6.2): at hard n = 3 starts (no one-round completion), does the
REC-S-type repair exist?
  move 1: the earliest-wanter chain E(k) of a dangerous agent k (k4/oc1max_multi.md §12), k taking an improving set T
          of goods it values inside J + {Y_z} (|T| = 1, 2 or 3);
  move 2: one chain or addition among the two other agents only (k's bundle untouched): the two-agent instance
          I- = I - k - T, where kgen-n3's Theorem 2 gives an EFX0 completion of OC1(t >= 0) shape;
  then a one-absorber completion that is EFX0 in I.  (Two moves, hence two rounds.)
Reported per hard start: whether some (order, k, T, move 2) works, and why not otherwise: no dangerous agent, no
improving T, or no lifted completion.  Raw definitions (verify_k4zero: one_round, completion, efx0).
Input: hard starts from a JSONL file (fields vals | sets+vals, picks) or the 13 k = 5 one-chain failures of ksens
(results/k4_ksens/kcegar_k5_n3_D1.log, FAIL lines).
    python3 kgen/rounds/rd2_n3_recs.py FILE"""
import sys, os, json, itertools, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import verify_k4zero as VZ


def dense(sets, vals):
    m = 1 + max(max(s) for s in sets); V = [[0] * m for _ in sets]
    for i, (s, vv) in enumerate(zip(sets, vals)):
        for g, x in zip(s, vv): V[i][g] = x
    return V


def hard(V, y):
    b0 = [frozenset([g]) for g in y]
    return not any(VZ.completion(V, list(s), 1) is not None for s in VZ.one_round(V, b0, False))


def earliest_chain(V, y, k, order):
    n = len(V); p = [V[a][y[a]] for a in range(n)]; pos = {a: t for t, a in enumerate(order)}; P = [k]
    while True:
        ws = [i for i in range(n) if i != P[-1] and i not in P and V[i][y[P[-1]]] > p[i]]
        if not ws: return P
        P.append(min(ws, key=lambda i: pos[i]))


def th2_route(V, y):
    """the explicit form: move 1 = E(k) with k taking T (|T| = 2 inside J + {Y_z}, improving, (L)); move 2 = kgen-n3's
    Theorem 2 construction in the two-agent instance I- = I - k - T from the order without k; X = its completion plus
    X_k = T.  Returns ('ok', witness) or a reason; also checks Lemma SD-E (the reduced start is the SD outcome)."""
    sys.path.insert(0, os.path.join(os.path.dirname(HERE)))
    import theorem2 as T2
    n, m = len(V), len(V[0]); p = [V[a][y[a]] for a in range(n)]; J = [g for g in range(m) if g not in y]
    orders = [o for o in itertools.permutations(range(n)) if tuple(VZ.sd(V, o)) == tuple(y)]
    D = [k for k in range(n) if any(V[i][y[k]] > p[i] for i in range(n) if i != k) and any(V[k][g] > 0 for g in J)]
    if not D: return 'no dangerous agent', None
    why = 'no improving pool pair'
    for o in orders:
        for k in D:
            P = earliest_chain(V, y, k, o); z = P[-1]
            pool = [g for g in J + [y[z]] if V[k][g] > 0]
            for T in itertools.combinations(pool, 2):
                if sum(V[k][g] for g in T) <= p[k]: continue
                B1 = [{y[a]} for a in range(n)]; B1[k] = set(T)
                for l in range(1, len(P)): B1[P[l]] = {y[P[l - 1]]}
                val = [sum(V[a][g] for g in B1[a]) for a in range(n)]
                if any(val[a] <= p[a] for a in P): continue
                if any(a != k and any(V[a][g] >= val[a] for g in T) for a in range(n)): why = '(L) fails'; continue
                rest = [a for a in o if a != k]; G = [g for g in range(m) if g not in T]
                v2 = [[V[a][g] for g in G] for a in rest]
                y2 = VZ.sd(v2, (0, 1))
                if [G[g] if g is not None else None for g in y2] != [next(iter(B1[a])) for a in rest]:
                    return 'SD-E VIOLATION', {'order': o, 'k': k}
                X2 = T2.theorem2(v2, (0, 1))
                X = [None] * n; X[k] = sorted(T)
                for j, a in enumerate(rest): X[a] = sorted(G[g] for g in X2[j])
                if VZ.efx0(V, X):
                    return 'ok', {'order': list(o), 'k': k, 'E(k)': P, 'T': list(T), 'X': X}
                why = '(K) or (L) fails after Theorem 2'
    return why, None


def route(V, y):
    n, m = len(V), len(V[0]); p = [V[a][y[a]] for a in range(n)]; J = [g for g in range(m) if g not in y]
    orders = [o for o in itertools.permutations(range(n)) if tuple(VZ.sd(V, o)) == tuple(y)]
    D = [k for k in range(n) if any(V[i][y[k]] > p[i] for i in range(n) if i != k) and any(V[k][g] > 0 for g in J)]
    if not D: return 'no dangerous agent', None
    anyT = False
    for o in orders:
        for k in D:
            P = earliest_chain(V, y, k, o); z = P[-1]
            pool = [g for g in J + [y[z]] if V[k][g] > 0]
            for r in (1, 2, 3):
                for T in itertools.combinations(pool, r):
                    if sum(V[k][g] for g in T) <= p[k]: continue
                    anyT = True
                    B1 = [{y[a]} for a in range(n)]; B1[k] = set(T)
                    for l in range(1, len(P)): B1[P[l]] = {y[P[l - 1]]}
                    if any(sum(V[a][g] for g in B1[a]) <= p[a] for a in P): continue        # move 1 must improve
                    for s in VZ.one_round(V, [frozenset(b) for b in B1], True):
                        if set(s[k]) != set(B1[k]): continue                               # move 2 leaves k alone
                        X = VZ.completion(V, [set(b) for b in s], 1)
                        if X is not None:
                            return 'ok', {'order': list(o), 'k': k, 'E(k)': P, 'T': list(T), 'state2': [sorted(b) for b in s], 'X': X}
    return ('no lifted completion' if anyT else 'no improving T'), None


if __name__ == '__main__':
    fn = sys.argv[1]; rows = []
    for l in open(fn):
        l = l.strip()
        if not l: continue
        if l.startswith('{') and '"result": "FAIL"' in l:
            x = json.loads(l); rows.append((x['name'], dense(x['sets'], x['recheck']['vals']), tuple(x['recheck']['picks'])))
        elif l.startswith('{') and '"picks"' in l and '"result"' not in l:
            x = json.loads(l); V = x['vals'] if 'sets' not in x else dense(x['sets'], x['vals']); rows.append((x.get('name', ''), V, tuple(x['picks'])))
    print('$ python3 kgen/rounds/rd2_n3_recs.py', fn, '| starts', len(rows), flush=True)
    C = collections.Counter(); t0 = time.time()
    for name, V, y in rows:
        if not hard(V, y): C['not hard (one round suffices)'] += 1; continue
        C['hard starts'] += 1
        why, w = route(V, y); C[('any second move', why)] += 1
        if w:   # the structure of the repair found
            o = w['order']; k = w['k']; pos = o.index(k)
            C[('repair: k is the', ['first', 'second', 'third'][pos] + ' picker')] += 1
            C[('repair: |T|', len(w['T']))] += 1
            C[('repair: k absorbs junk beyond T', len(w['X'][k]) > len(w['T']))] += 1
            s2 = w['state2']; moved2 = [a for a in range(3) if a != k and sorted(s2[a]) != [y[a]] and not (len(w['E(k)']) > 1 and a in w['E(k)'][1:] and sorted(s2[a]) == [y[w['E(k)'][w['E(k)'].index(a) - 1]]])]
            C[('repair: agents changed by move 2', len(moved2))] += 1
            C[('repair: E(k) length', len(w['E(k)']))] += 1
        why2, w2 = th2_route(V, y); C[('Theorem 2 as the second move', why2)] += 1
        print(name, json.dumps(V), 'picks', y, '->', why, '| Theorem 2 route:', why2, json.dumps(w2) if w2 else '', flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
