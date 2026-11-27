"""Lemma RF-13 (k4/k3_oc1.md §13) checked on the RF class (1, 3): its hypotheses and its conclusion, separately.
Setting: RF start Y' with RF path u -> w -> d (d takes a junk good g of Y, so Y'_w = Y_d and Y'_d = g), H a subset of
J' improving for w, and J' - H split as A (to d) and B (to w), |B| <= 1.  X: u keeps {Y_w}; w takes H + B; d takes
{Y_d, g} + A; everyone else keeps its pick.  Hypotheses:
  (F1) every agent other than w values at most one good of H + B;
  (F2) every agent other than d values at most one good of {Y_d, g} + A;
  (F3) no agent other than d and w values Y_d above its pick at Y'.
Conclusion: X is EFX0 (raw check), and it is one official chain ('w takes H, d takes Y'_w') plus a one-absorber
completion (d absorbs g and A, w takes B).
    python3 k4/k3oc1/rf/rf13_lemma.py RESIDUE.jsonl.gz"""
import sys, gzip, json, itertools, collections
from rf13_facts import efx0
C = collections.Counter()
for line in gzip.open(sys.argv[1], 'rt'):
    r = json.loads(line)
    if r['cls'] != '(1, 3)': continue
    sets, vals, Y, Y2, path = r['sets'], r['vals'], r['Y'], r['Y2'], r['path']
    n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    allg = set(g for s in sets for g in s); J2 = sorted(allg - set(Y2)); p2 = [v[i][Y2[i]] for i in range(n)]
    u, w, d = path[0], path[1], path[-1]
    assert len(path) == 3 and Y2[w] == Y[d] and Y2[d] not in Y and Y2[u] == Y[w]
    Yd, g = Y[d], Y2[d]
    some_hyp = False; some_ok = False
    for H in itertools.combinations(J2, 2):
        if sum(v[w].get(h, 0) for h in H) <= p2[w]: continue
        rest = [h for h in J2 if h not in H]
        for B in ([], *[[b] for b in rest]):
            A = [h for h in rest if h not in B]
            Wb = list(H) + B; Zb = [Yd, g] + A
            F1 = all(sum(1 for h in Wb if h in v[i]) <= 1 for i in range(n) if i != w)
            F2 = all(sum(1 for h in Zb if h in v[i]) <= 1 for i in range(n) if i != d)
            F3 = all(v[i].get(Yd, 0) <= p2[i] for i in range(n) if i not in (d, w))
            X = [[Y2[i]] for i in range(n)]; X[w] = Wb; X[d] = Zb
            ok = efx0(v, X)
            hyp = F1 and F2 and F3
            C['|B| = %d: hypotheses %s, X EFX0 %s' % (len(B), hyp, ok)] += 1
            if hyp and not ok: print('LEMMA VIOLATED', r, H, A, B, flush=True)
            some_hyp |= hyp; some_ok |= ok
    C['start: some (H, A, B) meets (F1)-(F3): %s' % some_hyp] += 1
    C['start: some X is EFX0: %s' % some_ok] += 1
for k in sorted(C): print(C[k], k)
