"""Residue A1 of Conjecture RF (k4/oc1_hall.md §24.6): RF starts Y' with one receiver d, no truly dangerous agent, and
the RF path u -> w -> d of length 2 with d taking a junk good g.  With owner w, d is the only holder, so Lemma 2* asks
for one good h of J' (= J - g + Y_u) such that (a) d, which wants its old pick Y_d = Y'_w, is compensated by h, and (b)
no frozen agent other than w is threatened by W_w - h, where W_w = {Y_d} + J'.  For each A1 start this script records
which goods h work, whether h = Y_u works, whether h = d's best good of J' works, and which frozen agents a wrong h
leaves threatened; and checks the raw S* completion with owner w (ohlib.shaped_completion) against the count.

    python3 k4/oc1_hall/rf_a1.py
"""
import sys, os, json, gzip, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, shaped_completion, threatened, bundles_of, frozen_set
import _paths

if __name__ == '__main__':
    d = json.load(gzip.open(os.path.join(_paths.ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz')))
    C = collections.Counter(); shown = 0
    print('$ python3 k4/oc1_hall/rf_a1.py', flush=True)
    for hg in d['hypergraphs']:
        sets = hg['sets']; m = 1 + max(max(s) for s in sets); seen = set()
        for st in hg['starts']:
            vals = st['vals']; I = Inst(sets, vals, m); Y = tuple(st['picks']); u = st['receivers'][0]; P0 = Picks(I, Y)
            for o in st['orders']:
                rf = [u] + [x for x in o if x != u]; Y2 = picks(I, rf)
                if (json.dumps(vals), Y2) in seen: continue
                seen.add((json.dumps(vals), Y2))
                P = Picks(I, Y2); base = base_of_picks(I, Y2)
                U2 = [i for i in range(I.n) if i not in P.F and Y2[i] is not None]
                DT = [k for k in P.D if threatened(I, k, P.pv[k], P.J)]
                if len(U2) != 1 or DT: continue
                dd = U2[0]; w = next(j for j in range(I.n) if Y[j] == Y2[u])
                if w == dd or Y2[w] != Y[dd] or Y2[dd] not in P0.J: continue      # A1 shape: u -> w -> d, d takes junk
                C['A1 starts'] += 1
                Ww = [Y2[w]] + list(P.J); pd = P.pv[dd]
                good = []
                for h in P.J:
                    rest = [x for x in Ww if x != h]
                    comp = h in I.R[dd] and not threatened(I, dd, pd + I.v[dd][h], rest)
                    unexposed = not threatened(I, dd, pd, rest)
                    frz = [q for q in P.F if q != w and threatened(I, q, P.pv[q], rest)]
                    ok = (comp or unexposed) and not frz
                    if ok: good.append(h)
                    else:
                        for q in frz: C['  a rejected h leaves threatened: %s' % ('u' if q == u else ('a dangerous agent' if q in P.D else 'a frozen non-dangerous agent'))] += 1
                        if not (comp or unexposed): C['  a rejected h fails to compensate d'] += 1
                B = bundles_of(I, base); F2 = set(frozen_set(I, base)); holders = [j for j in range(I.n) if len(B[j]) <= 1 and j not in F2]
                raw = shaped_completion(I, base, w, holders)
                C['  raw S* completion owned by w'] += raw
                C['  some single h works (Lemma 2* with N1 = {d})'] += bool(good)
                if raw != bool(good): C['  MISMATCH raw vs count'] += 1
                yu = Y[u]
                C['  h = Y_u works'] += yu in good
                best = max((x for x in P.J if x in I.R[dd]), key=lambda x: I.key[dd][x], default=None)
                C['  h = d\'s favourite good of J\' works'] += best in good
                C['  number of working h: %d' % len(good)] += 1
                C['  d values Y_u'] += yu in I.R[dd]
                C['  w is dangerous at Y (D)'] += w in P0.D
                C['  w truly dangerous at Y'] += w in [k for k in P0.D if threatened(I, k, P0.pv[k], P0.J)]
                C['  d frozen at Y'] += dd in P0.F
                if shown < 2:
                    shown += 1
                    print('A1 EXAMPLE', hg['list'], hg['idx'], json.dumps((sets, vals)), 'Y', Y, 'u', u, 'w', w, 'd', dd, "Y'", Y2, "J'", P.J, 'good h', good, flush=True)
    for k in sorted(C): print(k, C[k])
