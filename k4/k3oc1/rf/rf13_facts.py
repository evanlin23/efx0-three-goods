"""RF class (1, 3) at n = 5 (k4/k3_oc1.md §13): structural census of the starts, from girth's build of the
certifier's exports (k4/girth/oc1_residue_n5.py build, on claude/k4-girth).  For each start Y' (one receiver d, three
truly dangerous agents, RF path u -> w -> d with d taking a junk good g of Y):
  - |J'|, roles at Y', whether w is truly dangerous, whether every truly dangerous agent holds its top good;
  - which (H, x, y) make girth's form X EFX0: w takes H u {y}, d takes {Y'_w, Y'_d, x} (raw EFX0, own code);
  - candidate rules for H, x, y.
    python3 k4/k3oc1/rf/rf13_facts.py RESIDUE.jsonl.gz"""
import sys, gzip, json, itertools, collections

def efx0(v, X):
    n = len(X)
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in X[i])
        for j in range(n):
            if i == j or len(X[j]) < 2: continue
            vs = [v[i].get(g, 0) for g in X[j]]
            if sum(vs) - min(vs) > own: return False
    return True

def threat(v, i, S, val):
    vs = [v[i].get(g, 0) for g in S]
    return len(S) >= 2 and sum(vs) - min(vs) > val

def main():
  C = collections.Counter(); ex = []
  for line in gzip.open(sys.argv[1], 'rt'):
      r = json.loads(line)
      if r['cls'] != '(1, 3)': continue
      sets, vals, Y, Y2, path = r['sets'], r['vals'], r['Y'], r['Y2'], r['path']
      n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
      allg = sorted(set(g for s in sets for g in s)); J2 = [g for g in allg if g not in Y2]; J = [g for g in allg if g not in Y]
      p2 = [v[i][Y2[i]] for i in range(n)]
      u, w, d = path[0], path[1], path[-1]
      top = [max(sets[i], key=lambda g: v[i][g]) for i in range(n)]
      DT = [i for i in range(n) if i != d and any(v[j].get(Y2[i], 0) > p2[j] for j in range(n) if j != i) and threat(v, i, J2, p2[i]) or
            (i != d and any(v[j].get(Y2[i], 0) > p2[j] for j in range(n) if j != i) and any(g not in v[i] for g in J2) and any(g in v[i] for g in J2) and sum(v[i].get(g, 0) for g in J2) > p2[i])]
      C['|J\'| = %d' % len(J2)] += 1
      C['w truly dangerous at Y\' %s' % (w in DT)] += 1
      C['|D_T\'| (recomputed) = %d' % len(DT)] += 1
      C['every D_T\' agent holds its top at Y\' %s' % all(Y2[i] == top[i] for i in DT)] += 1
      C['d holds at Y\' a junk good of Y %s' % (Y2[d] in J)] += 1
      C['Y\'_w = Y_d %s' % (Y2[w] == Y[d])] += 1
      works = []
      for H in itertools.combinations(J2, 2):
          if sum(v[w].get(g, 0) for g in H) <= p2[w]: continue
          rest = [g for g in J2 if g not in H]
          for x in rest:
              for y in [g for g in rest if g != x]:
                  if len(rest) != 2: continue
                  for orient in ('d owns', 'w owns'):
                      X = [[Y2[i]] for i in range(n)]
                      if orient == 'd owns': X[w] = list(H) + [y]; X[d] = [Y2[w], Y2[d], x]
                      else: X[w] = list(H) + [y, Y2[d]]; X[d] = [Y2[w], x]
                      if efx0(v, X): works.append((H, x, y, orient))
      C['some (H, x, y) works: %s' % bool(works)] += 1
      C['orientations that work: %s' % sorted(set(o for *_, o in works))] += 1
      if works:
          H0 = max([H for H, *_ in works], key=lambda H: 0)
          # rule: H = w's best improving pair? x = d's favourite of the rest?
          bestH = max((H for H in itertools.combinations(J2, 2) if sum(v[w].get(g, 0) for g in H) > p2[w]), key=lambda H: sum(v[w].get(g, 0) for g in H))
          C['w\'s best pair H is among working H %s' % any(H == bestH for H, *_ in works)] += 1
          C['number of working H: %d' % len(set(H for H, *_ in works))] += 1
      if len(ex) < 3: ex.append((r['h'], sets, vals, Y, Y2, path, J2, works[:3]))
  for k in sorted(C): print(C[k], k)
  for e in ex: print(e)

if __name__ == '__main__':
    main()
