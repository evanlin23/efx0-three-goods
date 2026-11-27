"""Targeted contrapositive search for RF-A1*'s facts (k4/k3_oc1.md §13.6).  Start from DEMOTE-0 path-2 RF starts of
girth's build (every STEP-th), re-sample the values of one agent (d, k2, or u; strict, 1..30) TRIES times, and keep the
perturbed instances whose start Y (SD of the same order, ending with u) and RF start Y' keep the DEMOTE-0 path-2 shape.
Where (A1-i), (A1-ii) or (A1-iii) fails, test exactly whether Y is hard (rf_dea_full.analyse).
    python3 k4/k3oc1/rf/a1_perturb.py RESIDUE.jsonl.gz STEP TRIES SEED"""
import sys, gzip, json, itertools, random, collections
import rf_dea_full as R
from a1_contra import sd, roles

def shape_and_facts(sets, vals, o):
    n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]; allg = sorted(set(x for s in sets for x in s))
    Y = sd(sets, v, o)
    if None in Y: return None
    J = [x for x in allg if x not in Y]; rl = roles(sets, v, Y, J)
    if rl.count('U') != 1: return None
    u = rl.index('U')
    if o[-1] != u: return None
    Y2 = sd(sets, v, (u,) + tuple(a for a in o if a != u))
    if None in Y2: return None
    J2 = [x for x in allg if x not in Y2]; rl2 = roles(sets, v, Y2, J2)
    if rl2.count('U') != 1 or 'DT' in rl2: return None
    d = rl2.index('U'); ch = [a for a in range(n) if Y2[a] != Y[a]]
    if len(ch) != 3 or Y2[d] not in J: return None
    w = next(a for a in ch if a not in (u, d))
    if not (Y2[u] == Y[w] and Y2[w] == Y[d]): return None
    g = Y2[d]; Jd = [x for x in J2 if x in v[d]]; h = max(Jd, key=lambda x: v[d][x]) if Jd else None
    A1i = h is not None and sorted(x for x in J if x in v[d]) == sorted([g, h]) and Jd == [h] and v[d][g] + v[d][h] > v[d][Y[d]]
    W = [Y[d]] + [x for x in J2 if x != h]
    A1ii = h is not None and sorted(x for x in W if x in v[u]) == sorted([Y[d], Y[u]]) and v[u][Y[d]] + v[u][Y[u]] < v[u][Y[w]]
    k2s = [k for k in range(n) if rl[k] == 'DT' and k != d]
    A1iii = h is not None and len(k2s) == 1 and g in v[k2s[0]] and h in v[k2s[0]] and v[k2s[0]].get(Y[d], 0) <= v[k2s[0]][Y2[k2s[0]]]
    return dict(Y=Y, Y2=Y2, u=u, w=w, d=d, k2=k2s[0] if len(k2s) == 1 else None, facts=(A1i, A1ii, A1iii))

if __name__ == '__main__':
    path, STEP, TRIES, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(seed); C = collections.Counter()
    for k, line in enumerate(gzip.open(path, 'rt')):
        r = json.loads(line)
        if r['cls'] != 'DEMOTE-0' or len(r['path']) != 3 or k % STEP: continue
        sets, vals, Y = r['sets'], r['vals'], r['Y']; n = len(sets); v = [dict(zip(sets[i], vals[i])) for i in range(n)]
        # an order giving Y, ending with u, whose RF reorder gives the stored Y' (the RF start depends on the order)
        o = next((o for o in itertools.permutations(range(n)) if sd(sets, v, o) == Y and o[-1] == r['u']
                  and sd(sets, v, (r['u'],) + tuple(a for a in o if a != r['u'])) == r['Y2']), None)
        if o is None: C['no order reproduces the stored RF start'] += 1; continue
        base = shape_and_facts(sets, vals, o)
        if base is None: C['base start lost its shape (?)'] += 1; continue
        targets = {'d': base['d'], 'u': base['u']}
        if base['k2'] is not None: targets['k2'] = base['k2']
        for role, a in targets.items():
            for _ in range(TRIES):
                nv = [list(x) for x in vals]; nv[a] = rng.sample(range(1, 31), len(sets[a]))
                res = shape_and_facts(sets, nv, o)
                if res is None: C['perturb %s: shape lost' % role] += 1; continue
                if all(res['facts']): C['perturb %s: shape kept, facts hold' % role] += 1; continue
                hd = R.analyse(sets, nv, res['Y']) == 'needs a move; NO repairing chain'
                C['perturb %s: shape kept, facts %s, Y hard %s' % (role, res['facts'], hd)] += 1
                if hd: print('HARD-WITHOUT-FACTS', role, json.dumps(sets), json.dumps(nv), list(o), flush=True)
    for k in sorted(C): print(C[k], k)
