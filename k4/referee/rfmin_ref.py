#!/usr/bin/env python3
"""Referee check of twins' PR #156 (proof/k4-rf-min, k4/RFMIN.md at d32e566d): Lemma RF-TOP, Lemma ABS, and the data
claims behind Corollaries RF-TOP / RF-PRIV / ABS. Own code (c13_ref.py, cert_ref.py); nothing from k4/rfmin/ is run.

  top N SEED     : RF-TOP on random strict instances (k <= 5, any order): an agent u holding its top good moved to the
                   front changes no pick. Mutant: u holding a non-top good (must change picks sometimes).
  abs N SEED K   : Lemma ABS on random SD starts with at most K goods per agent, ties never (strict sums): when some
                   agent f holds a private good and every frozen agent i has v_i(J) <= v_i(Y_i), the construction
                   (receivers r != f in random order take their best free junk good if the free junk is worth more
                   than their pick to them; f takes the rest) is one-absorber and raw EFX0. Mutants: drop the frozen
                   hypothesis; take f with a non-private pick.
  data EXPORT... : on the certifier's stored OC1^max-failing starts: receivers per start; receiver holds its top;
                   receiver's pick private; some agent's top good private; some agent holding a private good; ABS's
                   two hypotheses together; receiver kinds (goods, private goods).
"""
import sys, gzip, json, itertools, random
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from c13_ref import val, efx0, sd, mkv, receivers

def rand_strict(rng, n, m, kmin, kmax, vmax=40):
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        R = rng.sample(range(m), rng.randint(kmin, min(kmax, m)))
        while True:
            vals = [rng.randint(1, vmax) for _ in R]
            sums = [sum(c) for r in range(1, len(vals) + 1) for c in itertools.combinations(vals, r)]
            if len(set(sums)) == len(sums):
                break
        for g, a in zip(R, vals):
            v[i][g] = a
    return v

def recv_gen(v, Y):
    """receivers in RFMIN's sense: pick holders whose pick no other agent prefers (a pickless agent prefers any good it
    values)"""
    n = len(Y)
    def pref(i, g):
        return v[i][g] > (v[i][Y[i]] if Y[i] is not None else 0)
    return [a for a in range(n) if Y[a] is not None and not any(i != a and pref(i, Y[a]) for i in range(n))]

def top(N, seed):
    rng = random.Random(seed); c = Counter()
    for t in range(N):
        n = rng.randint(2, 6); m = n + rng.randint(0, 5)
        v = rand_strict(rng, n, m, 1, 5)
        o = list(range(n)); rng.shuffle(o)
        Y = sd(v, o)
        for u in range(n):
            if Y[u] is None:
                continue
            Y2 = sd(v, [u] + [a for a in o if a != u])
            istop = v[u][Y[u]] == max(v[u])
            key = 'u holds its top' if istop else 'u holds a non-top good (mutant)'
            c[key + ': cases'] += 1
            c[key + ': picks unchanged' if Y2 == Y else key + ': PICKS CHANGE'] += 1
    for k in sorted(c):
        print('  %-55s %d' % (k, c[k]))

def abs_construct(v, Y, f, order_r):
    n = len(Y); m = len(v[0]); J = set(range(m)) - set(y for y in Y if y is not None)
    X = [([Y[i]] if Y[i] is not None else []) for i in range(n)]
    free = set(J)
    for r in order_r:
        if v[r][Y[r]] < val(v, r, free):
            fr = [g for g in free if v[r][g] > 0]
            g = max(fr, key=lambda g: v[r][g])
            X[r].append(g); free.discard(g)
    X[f] += sorted(free)
    return X

def absrun(N, seed, K):
    rng = random.Random(seed); c = Counter(); ex = {}
    for t in range(N):
        n = rng.randint(3, 6); m = n + rng.randint(1, 5)
        v = rand_strict(rng, n, m, 2, K)
        o = list(range(n)); rng.shuffle(o)
        Y = sd(v, o)
        J = set(range(m)) - set(y for y in Y if y is not None)
        U = recv_gen(v, Y)
        Fr = [a for a in range(n) if Y[a] is not None and a not in U]
        hypF = all(val(v, i, J) <= v[i][Y[i]] for i in Fr)
        for f in range(n):
            if Y[f] is None:
                continue
            priv = not any(i != f and v[i][Y[f]] > 0 for i in range(n))
            rs = [r for r in U if r != f]; rng.shuffle(rs)
            X = abs_construct(v, Y, f, rs)
            one = sum(1 for i in range(n) if len(X[i]) - (1 if Y[i] is not None else 0) >= 2) <= 1
            ok = efx0(v, X) and one
            for name, cond in (('full', priv and hypF), ('no frozen hypothesis', priv and not hypF),
                               ('f not private', (not priv) and hypF)):
                if cond:
                    c['%s: cases' % name] += 1
                    if not ok:
                        c['%s: NOT EFX0 or not one-absorber' % name] += 1
                        if name not in ex or n < len(ex[name]['v']):
                            ex[name] = dict(v=v, order=o, f=f, X=X)
                        if name == 'full':
                            for i in range(n):
                                for j in range(n):
                                    if i != j and len(X[j]) >= 2 and any(val(v, i, X[j]) - v[i][g] > val(v, i, X[i]) for g in X[j]):
                                        c['  full failure: violator %s (|R_i| = %d, took a junk good %s) against %s, '
                                          'junk of X_j it values %d' % (
                                              'receiver' if i in U else ('frozen' if Y[i] is not None else 'pickless'),
                                              sum(1 for g in range(m) if v[i][g] > 0), len(X[i]) == 2,
                                              'X_f' if j == f else 'a {Y_r, g_r}',
                                              sum(1 for g in X[j] if g in J and v[i][g] > 0))] += 1
    print('  K = %d' % K)
    for k in sorted(c):
        print('  %-50s %d' % (k, c[k]))
    for k in sorted(ex):
        print('  smallest failure', k, json.dumps(ex[k]))

def data(paths):
    c = Counter()
    for p in paths:
        d = json.load(gzip.open(p))
        tag = p.rsplit('/', 1)[-1]
        for h in d['hypergraphs']:
            sets = h['sets']
            for s in h['starts']:
                v = mkv(sets, s['vals']); Y = list(s['picks']); n = len(Y); m = len(v[0])
                J = set(range(m)) - set(y for y in Y if y is not None)
                U = recv_gen(v, Y)
                c[(tag, 'starts')] += 1
                c[(tag, 'receivers %d' % len(U))] += 1
                Fr = [a for a in range(n) if Y[a] is not None and a not in U]
                privgood = lambda g, a: not any(i != a and v[i][g] > 0 for i in range(n))
                pt = any(privgood(max(range(m), key=lambda g: v[a][g]), a) for a in range(n))
                c[(tag, 'some agent\'s top good private')] += pt
                ph = [a for a in range(n) if Y[a] is not None and privgood(Y[a], a)]
                c[(tag, 'some agent holds a private good')] += bool(ph)
                hypF = all(val(v, i, J) <= v[i][Y[i]] for i in Fr)
                c[(tag, 'ABS hypotheses both hold')] += bool(ph) and hypF
                for u in U:
                    k = len(sets[u]); npriv = sum(1 for g in sets[u] if privgood(g, u))
                    c[(tag, 'receiver kind: %d goods, %d private' % (k, npriv))] += 1
                    c[(tag, 'receiver holds its top')] += v[u][Y[u]] == max(v[u])
                    c[(tag, 'receiver\'s pick private')] += privgood(Y[u], u)
                    c[(tag, 'receiver is the only private-good holder')] += (ph == [u])
    for k in sorted(c):
        print('  %-30s %-45s %d' % (k[0], k[1], c[k]))

if __name__ == '__main__':
    print('$ python3 k4/referee/rfmin_ref.py', *sys.argv[1:], flush=True)
    md = sys.argv[1]
    if md == 'top':
        top(int(sys.argv[2]), int(sys.argv[3]))
    elif md == 'abs':
        absrun(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    elif md == 'data':
        data(sys.argv[2:])
