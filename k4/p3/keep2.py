"""p <= 2 structure of perfect starts (k4/p3.md section 6, Lemmas UNF2, KEEP2, CR2), checked on hard starts.
Independent code (k4/p3/p3lib.py, k4/p3/oc1max.py); shares nothing with k4/oc1max_multi/.

For a perfect start (every agent holds its pick; records as written by proof/k4-oc1max-multi's collect.py: 'inst' is
the reduced instance, 'picks' its picks) in which every good has at most two valuers:
  - w(i): the unique agent that wants Y_i (asserted unique); P(k) = (k, w(k), w(w(k)), ...) up to the first agent
    nobody wants (the unique canonical chain from k);
  - UNF2: after P(k) with any improving H0 (subset of J + {Y_z}), every agent of P other than k is unfrozen (asserted);
  - KEEP2: k in D_T, H0 a subset of J inside R_k with v_k(H0) > p_k, every other truly dangerous agent unfrozen after
    P(k) ("P(k) covers D_T"), and no holder other than the head crowded by H0 (|H0 & R_u| >= 2 and
    v_u(H0 & R_u) > v_u(B'_u)); then B' has a
    one-absorber completion (checked by SAT, k4/p3/oc1max.Checker.complete, models re-checked by the raw definition);
  - for the starts without a KEEP2 chain: whether some canonical chain P(k), k in D, with some improving H0 has a
    one-absorber completion (any owner), and whether such k can be truly dangerous;
  - CR2: for k in D_T and H0 inside J, every crowded holder other than the head is in D_T, in E_J, or H0 = J is a junk
    triple inside R_u (case (iii)); anything else is counted as a CR2 VIOLATION.
    python3 k4/p3/keep2.py FILE.jsonl[.gz]       (records of collect.py, or of k4/p3/t1_p2.py)
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from p3lib import Inst
from oc1max import Checker


def threatened(I, i, S, t):
    S = list(S)
    if len(S) == 0: return False
    vs = [I.v[i].get(g, 0) for g in S]
    return sum(vs) - min(vs) > t


def analyse(I, Y):
    n = I.n; V = I.val
    J = [g for g in range(I.m) if g not in Y]
    p = [I.v[i][Y[i]] for i in range(n)]
    wanters = {i: [j for j in range(n) if j != i and I.v[j].get(Y[i], 0) > p[j]] for i in range(n)}
    assert all(len(w) <= 1 for w in wanters.values()), 'two wanters at p <= 2?'
    w = {i: (ws[0] if ws else None) for i, ws in wanters.items()}
    F = {i for i in range(n) if w[i] is not None}
    D = {i for i in F if any(g in I.R[i] for g in J)}
    DT = {d for d in D if threatened(I, d, J, p[d])}
    EJ = {u for u in range(n) if u not in F and threatened(I, u, J, p[u])}
    return J, p, w, F, D, DT, EJ


def chain(w, k):
    P = [k]
    while w[P[-1]] is not None:
        P.append(w[P[-1]]); assert len(P) <= len(w)
    return P


def state(I, Y, P, H0):
    B = [frozenset([Y[i]]) for i in range(I.n)]
    B[P[0]] = frozenset(H0)
    for i in range(1, len(P)): B[P[i]] = frozenset([Y[P[i - 1]]])
    return B


def frozen_at(I, B, i):
    return any(j != i and I.val(j, B[i]) > I.val(j, B[j]) for j in range(I.n) if len(B[i]) == 1)


if __name__ == '__main__':
    cnt = collections.Counter(); ex = {}
    import gzip
    src = gzip.open(sys.argv[1], 'rt') if sys.argv[1].endswith('.gz') else open(sys.argv[1])
    for line in src:
        d = json.loads(line); r = d.get('inst', d); I = Inst(r['sets'], r['vals'], r['m']); Y = d['picks']
        d.setdefault('name', str(cnt['starts']))
        assert I.p() <= 2 and all(y is not None for y in Y)
        J, p, w, F, D, DT, EJ = analyse(I, Y)
        cnt['starts'] += 1; cnt[f'|D_T| = {min(len(DT), 2)}{"+" if len(DT) >= 2 else ""}'] += 1
        K = Checker(I); keep2 = False
        for k in sorted(D):
            P = chain(w, k); z = P[-1]
            pool = [g for g in J if g in I.R[k]] + ([Y[z]] if Y[z] in I.R[k] else [])
            for r in range(1, len(pool) + 1):
                for H0 in itertools.combinations(pool, r):
                    if I.val(k, H0) <= p[k]: continue
                    B = state(I, Y, P, H0)
                    for x in P[1:]:                                    # UNF2
                        cnt['UNF2 tests'] += 1
                        assert not frozen_at(I, B, x), ('UNF2 violated', d['name'], P, H0, x)
                    if k not in DT or Y[z] in H0: continue
                    covered = all(not frozen_at(I, B, e) for e in DT - {k})
                    holders = [u for u in range(I.n) if u != k and not frozen_at(I, B, u)]
                    crowd = [u for u in holders if len(set(H0) & I.R[u]) >= 2 and I.val(u, set(H0) & I.R[u]) > I.val(u, B[u])]
                    for u in crowd:
                        kind = ('head z' if u == z else 'in D_T (frozen at the picks)' if u in DT
                                else 'in E_J (unfrozen at the picks)' if u in EJ
                                else 'case (iii): H0 = J, three junk goods inside R_u' if set(H0) == set(J) and len(J) == 3 and set(J) <= I.R[u]
                                else 'OTHER: CR2 VIOLATION')
                        cnt['CR2 crowded holder: ' + kind] += 1
                        ex.setdefault('CR2 ' + kind, (d['name'], Y, P, H0, u))
                    crowd = [u for u in crowd if u != z]               # the head is compensated by its old pick
                    if covered and not crowd:
                        cnt['KEEP2 (chain, H0) cases'] += 1
                        own = K.complete(tuple(B))
                        if own is None:
                            cnt['KEEP2 VIOLATION'] += 1; print('VIOLATION', d['name'], Y, P, H0); continue
                        keep2 = True
                    elif not covered: cnt['P(k) does not cover D_T (k in D_T, H0 in J)'] += 1
        if keep2: cnt['starts with a KEEP2 chain'] += 1
        else:
            cnt[f'starts without a KEEP2 chain, |D_T| = {len(DT)}'] += 1; ex.setdefault(f'no KEEP2, |D_T| = {len(DT)}', (d['name'], I.n, I.m, Y))
            # does some canonical chain P(k), k in D, with some improving H0 in (J + {Y_z}) & R_k, repair (owner anyone)?
            hit = set()
            for k in sorted(D):
                P = chain(w, k); z = P[-1]
                pool = [g for g in J if g in I.R[k]] + ([Y[z]] if Y[z] in I.R[k] else [])
                if any(I.val(k, H0) > p[k] and K.complete(tuple(state(I, Y, P, H0))) is not None
                       for r in range(1, len(pool) + 1) for H0 in itertools.combinations(pool, r)):
                    hit.add('D_T' if k in DT else 'D-D_T')
            tag = ('some P(k), k in D_T, repairs' if 'D_T' in hit else 'only P(k) with k pick-dangerous repairs' if hit
                   else 'no canonical chain repairs')
            cnt['no KEEP2: ' + tag] += 1
            key = 'no KEEP2: ' + tag
            if key not in ex or (I.n, I.m) < ex[key][1:3]: ex[key] = (d['name'], I.n, I.m, Y, json.dumps({'sets': I.sets, 'vals': [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)]}))
        K.close()
    print('$ python3 k4/p3/keep2.py ' + ' '.join(sys.argv[1:]))
    for k in sorted(cnt): print(f'{k}: {cnt[k]}')
    for k in sorted(ex): print('example', k, ex[k])
