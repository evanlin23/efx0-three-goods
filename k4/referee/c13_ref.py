#!/usr/bin/env python3
"""Referee check of TTC's Lemma C13 (k4/ttc.md §14.8 on claude/k4-ttc at 699cc115). Own code; nothing from k4/ttc/,
k4/girth/ or k4/sdc/ is run or imported. The certifier's n = 5 failure exports and girth's class-(1, 3) list are read as
data only.

  build EXPORT... : for every exported start (sets, vals, picks Y, orders), every order o and every receiver u of Y
      (an agent nobody wants the pick of), Y' = SD(u, o - u). Keep the distinct (sets, vals, Y') with a perfect Y', and
      classify by (|U'|, |D_T'|): U' = receivers at Y', D_T' = frozen agents threatened by the whole junk J' at their
      pick (v_i(J' - h) > p_i for some h in J'). Writes the class (1, 3) starts to c13_class13_ref.jsonl.gz.
  check FILE [GIRTH] : on every class (1, 3) start, the "data facts" of §14.8, Lemma C13's hypotheses (1)-(4) in the
      simple and the value form of (3), the hypothesis the proof uses but the statement omits ((0): nobody but d wants
      Y'_d), that the chain "w takes H, d takes Y'_w" is an official improving chain (k4/sdc.md §29) followed by a
      one-absorber completion, and the allocation by raw EFX0. With GIRTH, compares the start set with girth's list.
  rand N SEED : the lemma for any n: random SD starts (n = 3..6, ties allowed), every (w, d, H, x, y) meeting
      (0)-(4) gives a raw EFX0 allocation; mutants drop (0), (2), (3) or (4) and must produce failures.
  cex : the smallest counterexample to the lemma as stated (without (0)).
"""
import sys, gzip, json, itertools, random
from collections import Counter

def val(v, i, S):
    return sum(v[i][g] for g in S)

def efx0(v, X):
    """raw EFX0: v_i(X_i) >= v_i(X_j - g) for every i != j and every g in X_j (goods worth 0 to i included)"""
    n = len(X)
    for i in range(n):
        t = val(v, i, X[i])
        for j in range(n):
            if i == j:
                continue
            tot = val(v, i, X[j])
            for g in X[j]:
                if tot - v[i][g] > t:
                    return False
    return True

def sd(v, order):
    m = len(v[0]); left = set(range(m)); Y = [None] * len(v)
    for i in order:
        best = None
        for g in sorted(left):
            if v[i][g] > 0 and (best is None or v[i][g] > v[i][best]):
                best = g
        if best is not None:
            Y[i] = best; left.discard(best)
    return Y

def mkv(sets, vals):
    m = 1 + max(max(s) for s in sets)
    v = [[0] * m for _ in sets]
    for i, (s, x) in enumerate(zip(sets, vals)):
        for g, a in zip(s, x):
            v[i][g] = a
    return v

def wants(v, i, g, Y):
    return v[i][g] > v[i][Y[i]]

def receivers(v, Y):
    n = len(Y)
    return [a for a in range(n) if not any(i != a and wants(v, i, Y[a], Y) for i in range(n))]

def threat_J(v, i, J, p):
    tot = val(v, i, J)
    return any(tot - v[i][h] > p for h in J)

def roles(v, Y):
    n = len(Y); m = len(v[0]); J = sorted(set(range(m)) - set(Y))
    U = receivers(v, Y)
    DT = [a for a in range(n) if a not in U and threat_J(v, a, J, v[a][Y[a]])]
    return U, DT, J

def rf_path(Y, Y2, u):
    """u -> holder at Y of u's new pick -> ... until an agent's new pick is junk of Y"""
    owner = {g: a for a, g in enumerate(Y)}
    path = [u]; cur = u
    while Y2[cur] in owner:
        nxt = owner[Y2[cur]]
        if nxt in path:
            return None
        path.append(nxt); cur = nxt
    return path

# ---------------------------------------------------------------- build
def build(exports, out):
    c = Counter(); seen = set(); rows = []
    for f in exports:
        d = json.load(gzip.open(f))
        for h in d['hypergraphs']:
            sets = h['sets']; name = '%s#%d' % (h['list'], h['idx'])
            for s in h['starts']:
                v = mkv(sets, s['vals']); Y = list(s['picks']); n = len(Y)
                U = receivers(v, Y)
                c['starts'] += 1; c['receivers at Y: %d' % len(U)] += 1
                for o in s['orders']:
                    for u in U:
                        Y2 = sd(v, [u] + [a for a in o if a != u])
                        if None in Y2:
                            c['RF picks not perfect'] += 1; continue
                        key = json.dumps([sets, s['vals'], Y2])
                        if key in seen:
                            continue
                        seen.add(key)
                        U2, DT2, J2 = roles(v, Y2)
                        cls = 'R2' if len(U2) >= 2 else ('U1' if len(DT2) == 1 else '(1, %d)' % len(DT2))
                        c['distinct perfect RF starts'] += 1; c['class ' + cls] += 1
                        if cls == '(1, 3)':
                            rows.append(dict(h=name, sets=sets, vals=s['vals'], Y=Y, Y2=Y2, u=u))
    with gzip.open(out, 'wt') as fo:
        for r in rows:
            fo.write(json.dumps(r) + '\n')
    for k in sorted(c):
        print('  %-40s %d' % (k, c[k]))
    print('wrote', out, len(rows))

# ---------------------------------------------------------------- lemma
def hyps(v, Y, w, d, J, Hp, x, y, drop=()):
    """Lemma C13's hypotheses at (w, d, H, x, y); returns dict of booleans; (3s) simple form, (3v) value form"""
    n = len(Y); p = [v[i][Y[i]] for i in range(n)]
    Xw = list(Hp) + [x]; Xd = [Y[w], Y[d], y]
    h = {}
    h['1'] = (len(Hp) == 2 and set(Hp) <= set(J) and all(v[w][g] > 0 for g in Hp) and val(v, w, Hp) > p[w]
              and sorted(set(J) - set(Hp)) == sorted([x, y]) and wants(v, d, Y[w], Y))
    h['0'] = not any(i != d and wants(v, i, Y[d], Y) for i in range(n))
    h['2'] = not any(i != d and wants(v, i, Y[w], Y) for i in range(n))
    h['3s'] = all(sum(1 for g in Xw if v[i][g] > 0) <= 1 for i in range(n) if i != w)
    h['3v'] = all(val(v, i, Xw) - v[i][g] <= p[i] for i in range(n) if i != w for g in Xw)
    h['4'] = all(sum(1 for g in Xd if v[i][g] > 0) <= 1 for i in range(n) if i != d)
    return h

def alloc(Y, w, d, Hp, x, y):
    X = [[g] for g in Y]
    X[w] = list(Hp) + [x]; X[d] = [Y[w], Y[d], y]
    return X

def official(v, Y, w, d, J, Hp, X):
    """§29 chain x0 = w (H0 = H inside J and R_w, strict gain), x1 = d (takes B_w = {Y_w}, nonempty, strict gain),
    Y_d released to the junk; completion gives the junk {x, y, Y_d} with at most one agent taking >= 2 junk goods"""
    p = [v[i][Y[i]] for i in range(len(Y))]
    ok = set(Hp) <= set(J) and all(v[w][g] > 0 for g in Hp) and val(v, w, Hp) > p[w] and v[d][Y[w]] > p[d]
    B = [{g} for g in Y]; B[w] = set(Hp); B[d] = {Y[w]}
    newJ = (set(J) - set(Hp)) | {Y[d]}
    extra = [set(X[i]) - B[i] for i in range(len(Y))]
    ok = ok and all(B[i] <= set(X[i]) for i in range(len(Y))) and set().union(*extra) == newJ
    ok = ok and sum(1 for e in extra if len(e) >= 2) <= 1
    return ok

def check(path, girth=None):
    rows = [json.loads(l) for l in gzip.open(path)]
    c = Counter(); keys = set(); ex485 = None
    for r in rows:
        sets, vals, Y, Y2, u = r['sets'], r['vals'], r['Y'], r['Y2'], r['u']
        keys.add(json.dumps([sets, vals, Y2]))
        v = mkv(sets, vals); n = len(Y2); p = [v[i][Y2[i]] for i in range(n)]
        U2, DT2, J = roles(v, Y2)
        P = rf_path(Y, Y2, u)
        changed = sorted(a for a in range(n) if Y[a] != Y2[a])
        c['starts'] += 1
        if P is None or sorted(P) != changed or Y2[P[-1]] not in set(range(len(v[0]))) - set(Y):
            c['FAIL rf path'] += 1; continue
        c['path length %d' % (len(P) - 1)] += 1
        w, d = P[1], P[-1]
        c['|J\'| = %d' % len(J)] += 1
        c['U\' = {d}' if U2 == [d] else 'U\' != {d}'] += 1
        c['d values %d junk goods of J\'' % sum(1 for g in J if v[d][g] > 0)] += 1
        c['Y\'_w = Y_d (d\'s old pick)' if Y2[w] == Y[d] else 'Y\'_w != Y_d'] += 1
        c['d wants Y\'_w' if wants(v, d, Y2[w], Y2) else 'd does not want Y\'_w'] += 1
        c['w in D_T\'' if w in DT2 else 'w not in D_T\''] += 1
        c['u in D_T\'' if u in DT2 else 'u not in D_T\''] += 1
        pairs = [Hp for Hp in itertools.combinations([g for g in J if v[w][g] > 0], 2) if val(v, w, Hp) > p[w]]
        c['w has %d improving junk pairs (inside R_w)' % len(pairs)] += 1
        anypairs = [Hp for Hp in itertools.combinations(J, 2) if val(v, w, Hp) > p[w]]
        c['w has %d improving pairs of J\' (any)' % len(anypairs)] += 1
        # every split of R = (J' - H) + {Y'_d} between w and d (others keep picks)
        wk = set(); works = 0
        for Hp in pairs:
            Rr = [g for g in J if g not in Hp] + [Y2[d]]
            for mask in itertools.product([0, 1], repeat=len(Rr)):
                X = [[g] for g in Y2]
                X[w] = list(Hp) + [g for g, s in zip(Rr, mask) if s == 0]
                X[d] = [Y2[w]] + [g for g, s in zip(Rr, mask) if s == 1]
                if efx0(v, X):
                    works += 1
                    wk.add(sum(1 for g, s in zip(Rr, mask) if s == 0 and g != Y2[d]))
        c['working w/d splits give w %s goods of J\' - H' % sorted(wk)] += 1
        # Lemma C13
        simple = value = full0 = False; best = None
        for Hp in pairs:
            rest = [g for g in J if g not in Hp]
            if len(rest) != 2:
                continue
            for x, y in (rest, rest[::-1]):
                h = hyps(v, Y2, w, d, J, Hp, x, y)
                if h['1'] and h['2'] and h['4'] and h['3v']:
                    value = True
                    if best is None or h['3s']:
                        best = (Hp, x, y, h)
                    if h['3s']:
                        simple = True
        c['(1),(2),(4),(3) value form hold for some (H,x,y)' if value else 'FAIL (1),(2),(4),(3v)'] += 1
        c['  ... with (3) in simple form' if simple else '  ... (3) only in value form'] += 1
        if best:
            Hp, x, y, h = best
            c['  (0) nobody but d wants Y\'_d' if h['0'] else '  (0) FAILS'] += 1
            X = alloc(Y2, w, d, Hp, x, y)
            c['  allocation raw EFX0' if efx0(v, X) else '  ALLOCATION NOT EFX0'] += 1
            c['  official chain + one-absorber completion' if official(v, Y2, w, d, J, Hp, X) else '  NOT OFFICIAL'] += 1
            vx = sorted(i for i in range(n) if v[i][x] > 0 or v[i][y] > 0)
            other = sorted(set(DT2) - {w})
            c['  {x,y} valued exactly by D_T\' - w' if vx == other else '  {x,y} valued by %s, D_T\'-w %s' % (
                'superset' if set(other) <= set(vx) else 'other', 'size %d' % len(other))] += 1
            if not h['3s']:
                bad = [i for i in range(n) if i != w and sum(1 for g in X[w] if v[i][g] > 0) >= 2]
                for i in bad:
                    c['  value-form case: agent values %d goods of X_w, in D_T\' %s, values a good of H %s, '
                      'goods of X_w valued sum < p_i %s' % (sum(1 for g in X[w] if v[i][g] > 0), i in DT2,
                                                            any(v[i][g] > 0 for g in Hp),
                                                            val(v, i, X[w]) < p[i])] += 1
                if ex485 is None:
                    ex485 = dict(sets=sets, vals=vals, Y2=Y2, w=w, d=d, H=list(Hp), x=x, y=y, X=X, bad=bad,
                                 vals_bad=[[v[i][g] for g in X[w]] + [p[i]] for i in bad])
    for k in sorted(c):
        print('  %-72s %d' % (k, c[k]))
    if ex485:
        print('  value-form example', json.dumps(ex485))
    if girth:
        g = set()
        for l in gzip.open(girth):
            r = json.loads(l); g.add(json.dumps([r['sets'], r['vals'], r['Y2']]))
        print('  girth list %d, mine %d, common %d, only girth %d, only mine %d' % (
            len(g), len(keys), len(g & keys), len(g - keys), len(keys - g)))

# ---------------------------------------------------------------- random, any n
def rand_inst(rng, n, m, k, ties):
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        R = rng.sample(range(m), rng.randint(1, min(k, m)))
        for g in R:
            v[i][g] = rng.randint(1, 4 if ties else 40)
    return v

def rand(N, seed):
    rng = random.Random(seed); c = Counter(); ex = {}
    MUT = {'full': ('0', '1', '2', '3v', '4'), 'no0': ('1', '2', '3v', '4'), 'no2': ('0', '1', '3v', '4'),
           'no3': ('0', '1', '2', '4'), 'no4': ('0', '1', '2', '3v')}
    for t in range(N):
        n = rng.randint(3, 6); m = n + 4; k = rng.choice([3, 4, 5])
        v = rand_inst(rng, n, m, k, rng.random() < 0.5)
        o = list(range(n)); rng.shuffle(o)
        Y = sd(v, o)
        if None in Y:
            continue
        J = sorted(set(range(m)) - set(Y)); c['perfect starts'] += 1
        for w in range(n):
            for d in range(n):
                if w == d:
                    continue
                for Hp in itertools.combinations(J, 2):
                    rest = [g for g in J if g not in Hp]
                    for x, y in (rest, rest[::-1]):
                        h = hyps(v, Y, w, d, J, Hp, x, y)
                        if not h['1']:
                            continue
                        ok = efx0(v, alloc(Y, w, d, Hp, x, y))
                        for name, req in MUT.items():
                            if all(h[q] for q in req):
                                c['%s: instances meeting hypotheses' % name] += 1
                                if not ok:
                                    c['%s: NOT EFX0' % name] += 1
                                    if name not in ex or len(v) < len(ex[name]['v']):
                                        ex[name] = dict(v=v, Y=Y, w=w, d=d, H=list(Hp), x=x, y=y)
    for k_ in sorted(c):
        print('  %-50s %d' % (k_, c[k_]))
    for name in sorted(ex):
        print('  smallest failure', name, json.dumps(ex[name]))

def cex():
    # goods: a = 0 (Y'_w), b = 1 (Y'_d), c = 2 (Y'_i), h1 = 3, h2 = 4, x = 5, y = 6; agents w = 0, d = 1, i = 2
    # strict values (distinct subset sums per agent), every good valued by someone, k = 3
    v = [[10, 0, 0, 6, 5, 0, 0],   # w: picks a, values H = {h1, h2} at 11 > 10
         [10, 5, 0, 0, 0, 0, 1],   # d: wants a (its old pick), picks b, values y at 1
         [0, 10, 5, 0, 0, 1, 0]]   # i: wants b = Y'_d, picks c, values x at 1
    Y = sd(v, [0, 1, 2]); print('  SD(w, d, i) =', Y, '(expect [0, 1, 2])')
    J = sorted(set(range(7)) - set(Y)); print('  J\' =', J)
    h = hyps(v, Y, 0, 1, J, (3, 4), 5, 6); print('  hypotheses', h)
    X = alloc(Y, 0, 1, (3, 4), 5, 6); print('  X =', X, 'raw EFX0:', efx0(v, X))
    print('  agent 2: v(X_2) = %d, v(X_d - a) = %d' % (val(v, 2, X[2]), val(v, 2, [1, 6])))
    print('  official chain + one absorber:', official(v, Y, 0, 1, J, (3, 4), X))

if __name__ == '__main__':
    print('$ python3 c13_ref.py', *sys.argv[1:], flush=True)
    mode = sys.argv[1]
    if mode == 'build':
        build(sys.argv[2:], 'c13_class13_ref.jsonl.gz')
    elif mode == 'check':
        check(sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else None)
    elif mode == 'rand':
        rand(int(sys.argv[2]), int(sys.argv[3]))
    elif mode == 'cex':
        cex()
