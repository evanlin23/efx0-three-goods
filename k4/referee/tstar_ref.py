#!/usr/bin/env python3
"""Referee replay of girth's 32 three-ring (T*) certificates (k4/girth.md §7; k4/girth/oc1_tstar.py,
results/k4_girth_oc1_tstar.log on claude/k4-girth at bbf55da7). Own code (c13_ref.py, cert_ref.py, rkmax_ref.py);
nothing from k4/girth/ or k4/sdc/ is run or imported. The certifier's n = 5 exports are read as data.

Rebuild the n = 5 DEMOTE-0 RF starts (|U'| = 1, D_T' empty; as in c13_ref.py build). Keep those with no one-absorber
completion at the picks (the starts that need a move). For each:
  - (T): some improving trade of d with a pick-dangerous p (frozen, values junk, not threatened by J'): p takes
    {Y'_d, j}, d takes Y'_p; and whether some such trade completes with every remaining junk good to a different agent;
  - (T*) at the starts with no improving trade at all: every ring c1 -> c2 -> d with c1 pick-dangerous,
    c1 takes {Y'_d, j}, c2 takes Y'_c1, d takes Y'_c2 (all strict gains), checked to be an official move (cert_ref.moves
    with rings), followed by d absorbing all remaining junk; raw EFX0; roles at Y; the RF path;
  - OC1 at the picks by my own search (rkmax_ref.oc1: one addition, chain or ring, then one-absorber).
    python3 tstar_ref.py EXPORT..."""
import sys, gzip, json, itertools
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from c13_ref import val, efx0, sd, mkv, wants, receivers, threat_J, rf_path
from cert_ref import complete, moves
from rkmax_ref import oc1

def role(v, Y, i):
    n = len(Y); m = len(v[0]); J = sorted(set(range(m)) - set(Y))
    if not any(j != i and wants(v, j, Y[i], Y) for j in range(n)):
        return 'U'
    if not any(v[i][g] > 0 for g in J):
        return 'F'
    return 'DT' if threat_J(v, i, J, v[i][Y[i]]) else 'Dp'

def main(exports):
    c = Counter(); seen = set(); shown = 0
    for f in exports:
        d0 = json.load(gzip.open(f))
        for hgr in d0['hypergraphs']:
            sets = hgr['sets']; name = '%s#%d' % (hgr['list'], hgr['idx'])
            for s in hgr['starts']:
                v = mkv(sets, s['vals']); Y = list(s['picks']); n = len(Y); m = len(v[0])
                for o in s['orders']:
                    for u in receivers(v, Y):
                        Y2 = sd(v, [u] + [a for a in o if a != u])
                        if None in Y2:
                            continue
                        key = json.dumps([sets, s['vals'], Y2])
                        if key in seen:
                            continue
                        seen.add(key)
                        U2 = receivers(v, Y2); J2 = sorted(set(range(m)) - set(Y2))
                        DT2 = [a for a in range(n) if a not in U2 and threat_J(v, a, J2, v[a][Y2[a]])]
                        if not (len(U2) == 1 and not DT2):
                            continue
                        c['DEMOTE-0 starts'] += 1
                        B = [{y} for y in Y2]
                        if complete(v, B) is not None:
                            continue
                        c['need a move'] += 1
                        d = U2[0]
                        r = oc1(v, Y2)
                        c['  OC1 after one move (mine)' if r == 1 else '  OC1 FAILS (mine)'] += 1
                        rl2 = [role(v, Y2, i) for i in range(n)]
                        Dp = [p for p in range(n) if rl2[p] == 'Dp']
                        trades = [(p, j) for p in Dp for j in J2 if v[p][j] > 0
                                  and val(v, p, [Y2[d], j]) > v[p][Y2[p]] and v[d][Y2[p]] > v[d][Y2[d]]]
                        if trades:
                            c['  (T) improving trade exists'] += 1
                            ok = False
                            for p, j in trades:
                                rest = [g for g in J2 if g != j]
                                for f_ in itertools.permutations(range(n), len(rest)):
                                    X = [[y] for y in Y2]; X[p] = [Y2[d], j]; X[d] = [Y2[p]]
                                    for g, a in zip(rest, f_):
                                        X[a].append(g)
                                    if efx0(v, X):
                                        ok = True; break
                                if ok:
                                    break
                            c['    ... some trade completes with every remaining junk good to a different agent'
                              if ok else '    ... NO such trade completion'] += 1
                            continue
                        c['  no improving trade: the (T*) starts'] += 1
                        c['    on ' + name] += 1
                        P = rf_path(Y, Y2, u)
                        c['    RF path length %d' % (len(P) - 1 if P else -1)] += 1
                        official = {tuple(frozenset(b) for b in st) for st in moves(v, [set(b) for b in B], rings=True)}
                        found = []
                        for c1 in Dp:
                            for c2 in range(n):
                                if c2 in (d, c1):
                                    continue
                                for j in J2:
                                    if not (v[c1][j] > 0 and val(v, c1, [Y2[d], j]) > v[c1][Y2[c1]]
                                            and v[c2][Y2[c1]] > v[c2][Y2[c2]] and v[d][Y2[c2]] > v[d][Y2[d]]):
                                        continue
                                    st = [set(b) for b in B]; st[c1] = {Y2[d], j}; st[c2] = {Y2[c1]}; st[d] = {Y2[c2]}
                                    off = tuple(frozenset(b) for b in st) in official
                                    X = [sorted(b) for b in st]; X[d] += [g for g in J2 if g != j]
                                    found.append((c1, c2, j, off, efx0(v, X)))
                        good = [x for x in found if x[3] and x[4]]
                        c['    improving 3-rings found: %d, official and EFX0 after d absorbs: %d' % (
                            len(found), len(good))] += 1
                        if any(not x[3] for x in found):
                            c['    A RING NOT OFFICIAL'] += 1
                        if good:
                            c1, c2, j, _, _ = good[0]
                            c['    certificate OK'] += 1
                            c['    roles at Y: u %s, d %s, c1 %s, c2 %s; c2 keeps its pick %s' % (
                                role(v, Y, u), role(v, Y, d), role(v, Y, c1), role(v, Y, c2), Y2[c2] == Y[c2])] += 1
                            c['    roles at Y\': c1 %s, c2 %s' % (rl2[c1], rl2[c2])] += 1
                            if shown < 1:
                                shown += 1
                                X = [[y] for y in Y2]; X[c1] = [Y2[d], j]; X[c2] = [Y2[c1]]; X[d] = [Y2[c2]] + [g for g in J2 if g != j]
                                print('  example', json.dumps(dict(h=name, sets=sets, vals=s['vals'], Y=Y, Y2=Y2, u=u, d=d,
                                                                   c1=c1, c2=c2, j=j, X=X)))
                        else:
                            c['    NO CERTIFICATE'] += 1
    for k in sorted(c):
        print('  %-100s %d' % (k, c[k]))

if __name__ == '__main__':
    print('$ python3 k4/referee/tstar_ref.py', *sys.argv[1:], flush=True)
    main(sys.argv[1:])
