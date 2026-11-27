"""Contrapositive search for RF-A1*'s facts (k4/k3_oc1.md §13.6): random strict values on the n = 5 hypergraphs of the
certifier's exports, every order.  At every perfect SD start Y with one receiver u (the last picker), RF start
Y' = SD(u, sigma - u) perfect with the DEMOTE-0 path shape (one receiver d at Y', no truly dangerous agent at Y', RF
path u -> w -> d with d taking a junk good g of Y): do (A1-i) and (A1-iii) hold?  Where one fails, is Y hard (no
one-absorber completion at Y and none after any official improving chain; exact, rf_dea_full's enumeration)?
    python3 k4/k3oc1/rf/a1_contra.py EXPORT.json.gz... SAMPLES SEED"""
import sys, gzip, json, itertools, random, collections
import rf_dea_full as R

def sd(sets, v, order):
    taken = set(); Y = [None] * len(sets)
    for i in order:
        av = [g for g in sets[i] if g not in taken]
        if av: Y[i] = max(av, key=lambda g: v[i][g]); taken.add(Y[i])
    return Y

def red(vs): return sum(vs) - min(vs)

def roles(sets, v, Y, J):
    n = len(sets); p = [v[i][Y[i]] for i in range(n)]; out = []
    for i in range(n):
        if not any(v[j].get(Y[i], 0) > p[j] for j in range(n) if j != i): out.append('U'); continue
        if not any(x in v[i] for x in J): out.append('F'); continue
        vs = [v[i].get(x, 0) for x in J]
        out.append('DT' if (sum(vs) > p[i] if 0 in vs else red(vs) > p[i]) else 'Dp')
    return out

def hard(sets, vals, Y):
    """OC1 fails at Y: no completion at the picks and no repairing official chain"""
    return R.analyse(sets, vals, Y) == 'needs a move; NO repairing chain'

if __name__ == '__main__':
    files, S, seed = sys.argv[1:-2], int(sys.argv[-2]), int(sys.argv[-1])
    rng = random.Random(seed); C = collections.Counter(); hyps = []
    for f in files:
        for h in json.load(gzip.open(f))['hypergraphs']: hyps.append(('%s#%d' % (h['list'], h['idx']), h['sets']))
    for name, sets in hyps:
        n = len(sets); allg = sorted(set(x for s in sets for x in s))
        for _ in range(S):
            vals = [rng.sample(range(1, 31), len(s)) for s in sets]; v = [dict(zip(sets[i], vals[i])) for i in range(n)]
            seen = set()
            for o in itertools.permutations(range(n)):
                Y = sd(sets, v, o)
                if None in Y or tuple(Y) in seen: continue
                seen.add(tuple(Y))
                J = [x for x in allg if x not in Y]; rl = roles(sets, v, Y, J)
                if rl.count('U') != 1: continue
                u = rl.index('U')
                if o[-1] != u: continue
                Y2 = sd(sets, v, (u,) + tuple(a for a in o if a != u))
                if None in Y2: continue
                J2 = [x for x in allg if x not in Y2]; rl2 = roles(sets, v, Y2, J2)
                if rl2.count('U') != 1 or 'DT' in rl2: continue
                d = rl2.index('U')
                changed = [a for a in range(n) if Y2[a] != Y[a]]
                if len(changed) != 3 or Y2[d] not in J: continue
                w = next(a for a in changed if a not in (u, d))
                if not (Y2[u] == Y[w] and Y2[w] == Y[d]): continue
                C[name + ': DEMOTE-0 path-2 RF shape'] += 1
                g = Y2[d]; Jd = [x for x in J2 if x in v[d]]; h = max(Jd, key=lambda x: v[d][x]) if Jd else None
                A1i = h is not None and sorted(x for x in J if x in v[d]) == sorted([g, h]) and Jd == [h] and v[d][g] + v[d][h] > v[d][Y[d]]
                k2s = [k for k in range(n) if rl[k] == 'DT' and k != d]
                A1iii = h is not None and len(k2s) == 1 and g in v[k2s[0]] and h in v[k2s[0]] and v[k2s[0]].get(Y[d], 0) <= v[k2s[0]][Y2[k2s[0]]]
                if A1i and A1iii: C[name + ':   facts hold'] += 1; continue
                hd = hard(sets, vals, Y)
                C[name + ':   (A1-i) %s (A1-iii) %s; Y hard %s' % (A1i, A1iii, hd)] += 1
                if hd: print('HARD-WITHOUT-FACTS', name, json.dumps(sets), json.dumps(vals), list(o), Y, Y2, flush=True)
    for k in sorted(C): print(C[k], k)
