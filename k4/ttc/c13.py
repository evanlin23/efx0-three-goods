"""The RF class (|U'|, |D_T'|) = (1, 3) at n = 5 (k4/ttc.md §14.8): structure of girth's repair (C) on all 7,733 starts.

Input: girth's list results/k4_girth_rf_n5_class13.jsonl.gz (branch claude/k4-girth): sets, vals, the RF picks Y2, the
receiver u of the failing start and the RF path (u, w, d).  At Y' = Y2 the receiver is d.  Girth's form: the chain
"w takes an improving junk pair H, d takes Y'_w" (w is truly dangerous), then a completion giving all remaining junk to
w and d.  For every start this script records:
  - |J'|, the roles of u, w, d, and which agents are truly dangerous;
  - whether d wants Y'_w (the chain's second step), and the improving junk pairs H of w;
  - after the chain, the remaining junk R = (J' - H) + {Y'_d}, and every split of R between w and d that is EFX0 (raw),
    with nothing to the others; whether d's share always contains Y'_d;
  - for the split that works: who values each good of R, and which agent each excluded split fails against.

    python3 k4/ttc/c13.py FILE.jsonl.gz          (structure)
    python3 k4/ttc/c13.py FILE.jsonl.gz lemma    (Lemma C13's hypotheses and allocation at every start)"""
import sys, os, gzip, json, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ttclib as T
import oc1max_hard as H


def roles(E, b):
    F = T.frozen_set(E, b); D = T.dangerous_set(E, b); J = [g for g in range(E.m) if b[g] < 0]

    def thr(i):
        vs = [E.v[i].get(g, 0) for g in J]
        return len(J) >= 2 and sum(vs) - min(vs) > E.v[i][[g for g in range(E.m) if b[g] == i][0]]
    DT = [k for k in sorted(D) if thr(k)]
    U = [i for i in range(E.n) if i not in F]
    return F, D, DT, U, J


if __name__ == '__main__' and not (len(sys.argv) > 2 and sys.argv[2] == 'lemma'):
    print('$ python3 k4/ttc/c13.py', *sys.argv[1:], flush=True)
    rows = [json.loads(l) for l in gzip.open(sys.argv[1])]
    C = collections.Counter(); ex = []
    for r in rows:
        sets, vals, Y2, path = r['sets'], r['vals'], tuple(r['Y2']), r['path']
        m = 1 + max(max(s) for s in sets); E = T.Enc(sets, vals, m); b = T.base_of(E, Y2)
        F, D, DT, U, J = roles(E, b)
        u, w, d = path[0], path[1], path[-1]
        C['path length %d' % (len(path) - 1)] += 1
        C['|J\'| = %d' % len(J)] += 1
        C['receiver is d' if U == [d] else 'receiver is NOT d'] += 1
        C['w truly dangerous' if w in DT else 'w NOT truly dangerous'] += 1
        C['u truly dangerous' if u in DT else 'u not truly dangerous'] += 1
        C['d values junk: %d goods' % sum(1 for g in J if E.v[d].get(g, 0) > 0)] += 1
        C['d wants Y\'_w' if E.v[d].get(Y2[w], 0) > E.v[d][Y2[d]] else 'd does NOT want Y\'_w'] += 1
        pw = E.v[w][Y2[w]]
        pairs = [Hp for Hp in itertools.combinations([g for g in J if E.v[w].get(g, 0) > 0], 2) if T.val(E, w, Hp) > pw]
        C['w has %d improving junk pairs' % len(pairs)] += 1
        works = []
        for Hp in pairs:
            Rr = [g for g in J if g not in Hp] + [Y2[d]]
            Bw = list(Hp); Bd = [Y2[w]]
            for mask in itertools.product([0, 1], repeat=len(Rr)):
                X = [[Y2[i]] for i in range(E.n)]
                X[w] = Bw + [g for g, s in zip(Rr, mask) if s == 0]
                X[d] = Bd + [g for g, s in zip(Rr, mask) if s == 1]
                if H.efx0(E.v, X):
                    works.append((Hp, tuple(sorted(X[w])), tuple(sorted(X[d])), Y2[d] in X[d],
                                  sum(1 for g in Rr if g in X[w] and g != Y2[d])))
        C['some pair and split works' if works else 'NO PAIR AND SPLIT WORKS'] += 1
        if works:
            C['  some working split gives Y\'_d to d' if any(x[3] for x in works) else '  no working split gives Y\'_d to d'] += 1
            C['  splits with w taking %s junk goods of R' % sorted(set(x[4] for x in works))] += 1
            C['  every improving pair H works' if len(set(x[0] for x in works)) == len(pairs) else
              '  only some improving pairs H work'] += 1
        if len(ex) < 3 and works:
            ex.append({'sets': sets, 'vals': vals, 'Y2': list(Y2), 'path': path, 'J': J, 'DT': DT, 'works': works[:4]})
    for k in sorted(C):
        print(k, C[k])
    for e in ex:
        print('example', json.dumps(e))


def lemma_c13(E, Y2, w, d, J):
    """Lemma C13's hypotheses: an improving pair H of w, d wants Y'_w and is its only wanter, and a split {x, y} of
    J' - H such that no agent other than w values two goods of H + {x}, and no agent other than d values two goods of
    {Y'_w, Y'_d, y}.  Returns the witnesses (H, x, y) that satisfy them."""
    n = E.n; pw = E.v[w][Y2[w]]; out = []
    if not E.v[d].get(Y2[w], 0) > E.v[d][Y2[d]]:
        return out
    if any(i not in (w, d) and E.v[i].get(Y2[w], 0) > E.v[i][Y2[i]] for i in range(n)):
        return out
    for Hp in itertools.combinations([g for g in J if E.v[w].get(g, 0) > 0], 2):
        if T.val(E, w, Hp) <= pw:
            continue
        rest = [g for g in J if g not in Hp]
        if len(rest) != 2:
            continue
        for x, y in (rest, rest[::-1]):
            Bw = list(Hp) + [x]; Bd = [Y2[w], Y2[d], y]
            if all(sum(1 for g in Bw if E.v[i].get(g, 0) > 0) <= 1 for i in range(n) if i != w) and \
               all(sum(1 for g in Bd if E.v[i].get(g, 0) > 0) <= 1 for i in range(n) if i != d):
                out.append((Hp, x, y))
    return out


def lemma_c13_value(E, Y2, w, d, J):
    """Lemma C13 with (3) in its value form: every i != w has v_i(X_w - g) <= p_i for every g in X_w"""
    n = E.n; pw = E.v[w][Y2[w]]; out = []
    if not E.v[d].get(Y2[w], 0) > E.v[d][Y2[d]]:
        return out
    if any(i not in (w, d) and E.v[i].get(Y2[w], 0) > E.v[i][Y2[i]] for i in range(n)):
        return out
    for Hp in itertools.combinations([g for g in J if E.v[w].get(g, 0) > 0], 2):
        if T.val(E, w, Hp) <= pw:
            continue
        rest = [g for g in J if g not in Hp]
        if len(rest) != 2:
            continue
        for x, y in (rest, rest[::-1]):
            Bw = list(Hp) + [x]; Bd = [Y2[w], Y2[d], y]

            def thr_ok(i, Bn):
                vs = [E.v[i].get(g, 0) for g in Bn]
                return sum(vs) - min(vs) <= E.v[i][Y2[i]]
            if all(thr_ok(i, Bw) for i in range(n) if i != w) and \
               all(sum(1 for g in Bd if E.v[i].get(g, 0) > 0) <= 1 for i in range(n) if i != d):
                out.append((Hp, x, y))
    return out


def run_c13(rows):
    C = collections.Counter()
    for r in rows:
        sets, vals, Y2, path = r['sets'], r['vals'], tuple(r['Y2']), r['path']
        m = 1 + max(max(s) for s in sets); E = T.Enc(sets, vals, m); b = T.base_of(E, Y2)
        J = [g for g in range(m) if b[g] < 0]; w, d = path[1], path[-1]
        wv = lemma_c13_value(E, Y2, w, d, J)
        C['Lemma C13 with (3) in value form: hypotheses hold' if wv else 'Lemma C13 with (3) in value form: FAIL'] += 1
        if wv:
            Hp, x, y = wv[0]
            X = [[Y2[i]] for i in range(E.n)]; X[w] = list(Hp) + [x]; X[d] = [Y2[w], Y2[d], y]
            C['  value form: allocation EFX0 (raw)' if H.efx0(E.v, X) else '  value form: ALLOCATION NOT EFX0'] += 1
        wit = lemma_c13(E, Y2, w, d, J)
        C['Lemma C13 hypotheses hold' if wit else 'Lemma C13 hypotheses FAIL'] += 1
        if wit:
            Hp, x, y = wit[0]
            X = [[Y2[i]] for i in range(E.n)]; X[w] = list(Hp) + [x]; X[d] = [Y2[w], Y2[d], y]
            C['  and its allocation is EFX0 (raw)' if H.efx0(E.v, X) else '  ITS ALLOCATION IS NOT EFX0'] += 1
            vx = sorted(i for i in range(E.n) if E.v[i].get(x, 0) > 0 or E.v[i].get(y, 0) > 0)
            DT = roles(E, b)[2]
            C['  {x, y} valued exactly by the other two truly dangerous agents' if vx == sorted(set(DT) - {w}) else
              '  {x, y} valued by %s' % ('a superset' if set(DT) - {w} <= set(vx) else 'others')] += 1
    return C


if __name__ == '__main__' and len(sys.argv) > 2 and sys.argv[2] == 'lemma':
    rows = [json.loads(l) for l in gzip.open(sys.argv[1])]
    for k, v in sorted(run_c13(rows).items()):
        print(k, v)
