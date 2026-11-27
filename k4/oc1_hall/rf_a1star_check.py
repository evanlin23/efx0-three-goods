"""Referee check of k3-oc1's Lemma RF-A1* (k4/k3_oc1.md §13.5 on claude/k4-k3-oc1; Hall's RF-A1, k4/oc1_hall.md §24.6,
with (A1-iv) weakened to (A1-iv*)), written here independently from the statement (k4/oc1_hall.md §24.13).

At every DEMOTE-0 RF start of the n = 5 exports (one receiver d, no truly dangerous agent) whose RF path is u -> w -> d
with d taking a junk good g of Y: h = d's favourite good of J' (if d values one), W = {Y_d} + (J' - {h}), and
  (A1-i)   J ∩ R_d = {g, h}, v_d(g) + v_d(h) > v_d(Y_d), J' ∩ R_d = {h}
  (A1-ii)  W ∩ R_u = {Y_d, Y_u}, v_u(Y_d) + v_u(Y_u) < v_u(Y_w)
  (A1-iii) some k2 != d values g and h and has v_k2(Y_d) <= p'_k2
  (A1-iv*) every frozen q of Y' outside {w, u, k2} (for SOME k2 of (A1-iii)) valuing Y_d has v_q(W) - min_W v_q <= p'_q
  (A1-iv)  (Hall's) no frozen q of Y' outside {w, u, k2} values Y_d
are tested, and the allocation X (w takes W, d takes {g, h}, the rest keep their picks) with two EFX0 checkers (ohlib and
the raw checker k4/sdc/oc1_mc2_rand.Inst.efx0).  The lemma says: hypotheses => X EFX0; a violation is printed.

    python3 k4/oc1_hall/rf_a1star_check.py N5_EXPORT [N5_EXPORT ...]
"""
import sys, os, json, gzip, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, threatened, efx0
import _paths
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst as RawInst


def job(task):
    sets, starts = task
    m = 1 + max(max(s) for s in sets); C = collections.Counter(); seen = set(); bad = []
    for st in starts:
        vals = st['vals']; I = Inst(sets, vals, m); Y = tuple(st['picks']); u = st['receivers'][0]
        J = [g for g in range(m) if g not in Y]
        for o in st['orders']:
            Y2 = picks(I, [u] + [x for x in o if x != u])
            if None in Y2 or (json.dumps(vals), Y2) in seen: continue
            seen.add((json.dumps(vals), Y2)); P = Picks(I, Y2)
            U2 = [i for i in range(I.n) if i not in P.F]
            if len(U2) != 1 or any(threatened(I, k, P.pv[k], P.J) for k in P.D): continue
            d = U2[0]
            ch = [i for i in range(I.n) if Y2[i] != Y[i]]
            if len(ch) != 3: continue
            w = [i for i in range(I.n) if Y[i] == Y2[u]]
            if not w or w[0] == d or Y2[w[0]] != Y[d] or Y2[d] not in J: continue
            w = w[0]; g = Y2[d]; Jp = P.J
            C['DEMOTE-0 starts with path u -> w -> d, d taking junk'] += 1
            dj = [x for x in Jp if x in I.R[d]]
            if not dj: C['  d values no good of J\''] += 1; continue
            h = max(dj, key=lambda x: I.key[d][x])
            W = [Y[d]] + [x for x in Jp if x != h]
            pv = P.pv
            vz = lambda i, T: sum(I.v[i].get(x, 0) for x in T) - min(I.v[i].get(x, 0) for x in T)
            a1 = (set(x for x in J if x in I.R[d]) == {g, h} and I.v[d][g] + I.v[d][h] > I.v[d].get(Y[d], 0) and dj == [h])
            a2 = (set(x for x in W if x in I.R[u]) == {Y[d], Y[u]} and I.v[u][Y[d]] + I.v[u][Y[u]] < I.v[u][Y[w]])
            k2s = [k for k in range(I.n) if k != d and g in I.R[k] and h in I.R[k] and I.v[k].get(Y[d], 0) <= pv[k]]
            a3 = bool(k2s)
            frozen = [q for q in range(I.n) if q in P.F]
            a4s = any(all(vz(q, W) <= pv[q] for q in frozen if q not in (w, u, k2) and Y[d] in I.R[q]) for k2 in k2s)
            a4 = any(all(Y[d] not in I.R[q] for q in frozen if q not in (w, u, k2)) for k2 in k2s)
            X = [[y] for y in Y2]; X[w] = list(W); X[d] = [g, h]
            ok = efx0(I, X); ok2 = RawInst(sets, vals).efx0(X)
            hyp = a1 and a2 and a3 and a4s
            C['  (A1-i) %s, (A1-ii) %s, (A1-iii) %s, (A1-iv*) %s, (A1-iv) %s' % (a1, a2, a3, a4s, a4)] += 1
            C['  hypotheses of RF-A1* hold: %s; X EFX0 (ohlib %s, raw %s)' % (hyp, ok, ok2)] += 1
            if hyp and not (ok and ok2) and len(bad) < 3:
                bad.append({'sets': sets, 'vals': vals, 'Y': list(Y), "Y'": list(Y2), 'u': u, 'w': w, 'd': d, 'h': h})
    return C, bad


def tasks_of(path):
    d = json.load(gzip.open(path))
    for hg in d['hypergraphs']:
        groups = collections.defaultdict(list)
        for st in hg['starts']: groups[json.dumps(st['vals'])].append(st)
        chunk = []
        for g in groups.values():
            chunk += g
            if len(chunk) >= 2000: yield (hg['sets'], chunk); chunk = []
        if chunk: yield (hg['sets'], chunk)


if __name__ == '__main__':
    print('$ python3 k4/oc1_hall/rf_a1star_check.py', *[os.path.basename(p) for p in sys.argv[1:]], flush=True)
    T = collections.Counter(); shown = 0
    with mp.Pool() as pool:
        for C, bad in pool.imap_unordered(job, [t for p in sys.argv[1:] for t in tasks_of(p)]):
            T.update(C)
            for b in bad:
                if shown < 5: shown += 1; print('LEMMA VIOLATED:', json.dumps(b), flush=True)
    for k in sorted(T): print(k, T[k])
