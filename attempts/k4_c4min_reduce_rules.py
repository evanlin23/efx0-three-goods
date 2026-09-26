"""Key-choice rules and the narrow role swap for reduction (a)/(c) of k4/c4min_reduce.md (attempts/k4-c4min-reduce-a.md,
attempts/k4-c4min-reduce-c.md), with k4/red_lib.py only (Python, from the definitions).

For every f = 1 profile of a seeded random sample (R profiles per core of the given certificate file):
  - a key-choice rule picks the keys (g, x) that maximize a score of x alone, or the best maximum of (r', Lambda') of I';
    the rule succeeds if every (r', Lambda')-maximum at every picked key is completable ('all picked keys'), so a rule
    counts as failing when ANY of the tied picked keys fails ('rule fails'); the tie-independent counts are also printed:
    'rule fails at every tied key' (no tie-break rescues the rule) and 'rule fails, unique pick' (no tie at all);
  - the narrow role swap: at every non-completable (r', Lambda')-maximum, some terminal z (a key by Lemma T) and some
    admissible pair S of x inside L ∪ Q_z make the configuration 'x holds S, z frozen on g, everyone else unchanged'
    completable; the first failures are printed as 'narrow swap example' (profile, key, pairs, pool).
Usage: python3 attempts/k4_c4min_reduce_rules.py results/k4_certs_3.json.gz 6000 11   (about 20 s)"""
import os, sys, random, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'k4'))
from red_lib import Prof, Key, fewest_frozen_le1, bits, pc, load_cores, profiles


def lvl(P, i, S):
    R = list(P.vals[i]); w = P.v(i, S)
    return sum(1 for k in range(len(R) + 1) for c in itertools.combinations(R, k) if sum(P.vals[i][h] for h in c) < w)


def completable(K, Q, L):
    return any(K.owner_status(Q, L, o)[2] for o in K.free)


def main():
    path, rand, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    cnt = collections.Counter(); examples = []
    for n, m, sets in load_cores(path):
        if m < 2 * n: continue
        deg = [sum(g in S for S in sets) for g in range(m)]
        for vals in profiles(sets, m, rand, rng):
            P = Prof(vals, m)
            f, keys = fewest_frozen_le1(P)
            if f != 1: continue
            cnt['f1 profiles'] += 1
            info, Ks = [], {}
            for g, x in keys:
                K = Key(P, g, x); Ks[x] = K
                cf = []
                for Q, L in K.configs():
                    cf.append(((sum(K.robust(y, Q[y]) for y in K.free), sum(K.level(y, Q[y]) for y in K.free)), Q, L, completable(K, Q, L)))
                best = max(c[0] for c in cf)
                mx = [c for c in cf if c[0] == best]
                priv = [h for h in bits(K.Ux) if deg[h] == 1]
                info.append(dict(x=x, g=g, K=K, mx=mx, good=all(c[3] for c in mx), best=best,
                                 lx=lvl(P, x, 1 << g), npriv=len(priv),
                                 vpriv=sum(P.vals[x][h] for h in priv) / P.vals[x][g],
                                 rel=P.vals[x][g] / P.v(x, K.Ux)))
            rules = {
                'max level of top (lx)': lambda i: i['lx'],
                'fewest private goods': lambda i: -i['npriv'],
                'least value of private goods / a': lambda i: -i['vpriv'],
                'largest a / v(U_x)': lambda i: i['rel'],
                'largest a / v(U_x) - private share': lambda i: i['rel'] - i['vpriv'],
                "best (r', Lambda')-maximum of I'": lambda i: i['best'],
            }
            for rn, rf in rules.items():
                b = max(rf(i) for i in info)
                sel = [i for i in info if rf(i) == b]
                if not all(i['good'] for i in sel): cnt['rule fails: ' + rn] += 1
                if not any(i['good'] for i in sel): cnt['rule fails at every tied key: ' + rn] += 1
                if len(sel) == 1 and not sel[0]['good']: cnt['rule fails, unique pick: ' + rn] += 1
            if not any(i['good'] for i in info): cnt['no key has every (r\', Lambda\')-maximum completable'] += 1
            # narrow role swap
            for i in info:
                K = i['K']; x, g = i['x'], i['g']
                for sc, Q, L, comp in i['mx']:
                    if comp: continue
                    cnt['non-completable (r\', Lambda\')-maxima'] += 1
                    terms = [y for y in K.free if K.needs_g(y, Q[y])]
                    ok = False
                    for z in terms:
                        if z not in Ks: cnt['terminal that is not a key'] += 1; continue
                        Kz = Ks[z]; pool = L | Q[z]
                        for S in Kz.pairs[x]:
                            if S & ~pool: continue
                            Q2 = {y: Q[y] for y in K.free if y != z}; Q2[x] = S
                            if completable(Kz, Q2, pool & ~S): ok = True; break
                        if ok: break
                    if not ok:
                        cnt['narrow swap fails'] += 1
                        if len(examples) < 6:
                            examples.append((vals, (g, x), {y: sorted(bits(q)) for y, q in Q.items()}, sorted(bits(L))))
    for k, v in sorted(cnt.items()): print('%-60s %d' % (k, v))
    for e in examples: print('narrow swap example', e)


if __name__ == '__main__':
    main()
