#!/usr/bin/env python3
"""Brute-force checks of Theorem Z and its lemmas (k4/c4min.md §3), from the definitions; independent of c4min.c.

Setting: a strict profile of a k = 4 core whose fewest frozen agents is 0 and with m >= 2n + 1. An all-pairs
allocation (APA) gives every agent a pair Q_i (two goods) whose relevant part is admissible (worth more than every
relevant good outside it); the pool L is the rest. Owner o is valid if no agent strongly envies Q_o ∪ L.
Checked on every APA of every profile examined:
  A (Lemma P) at a pool-optimal APA every agent is threatened by at most one owner, robust agents by none;
  B (Lemma R) at a pool-optimal APA without a valid owner, owner -> threatened agent is a permutation, and on each of
    its cycles the rotation (plain, or modified at a rich-pair agent) is an APA in which some agent is robust, unless
    every agent of the cycle is a 4-good agent holding its top with a good it does not value;
  B' (Lemma R, case by case) on every such cycle the plain rotation is an APA, and for every agent c of the cycle,
    with Q' the pair of its predecessor: (i) c 3-good, or of kind (D): Q' is robust for c; (ii) c of kind (R) with its
    fourth good s in Q': Q' is robust for c; (iii) c of kind (R) with s in the pool: the plain rotation with c given
    {a_c, s} instead (the other good of Q' to the pool) is an APA in which c is robust. Kind (R) agents with s
    elsewhere, or without their top in Q', are violations; agents of kind (T) with four goods are only counted;
  C at a pool-optimal APA no pool good is irrelevant to everyone... (the pool of a core is always valued by someone,
    so an APA whose agents all hold top + junk is never pool-optimal);
  D (Theorem Z) every APA maximizing (number of robust agents, sum of levels) has a valid owner.
usage: python3 k4/c4min_z.py FILE [--rand=N] [--seed=S] [--only=I,J]"""
import collections, itertools, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c4min_lib import load_cores, profiles, Profile, v, threatened, fmt_profile


def admissible(val, S):
    R = S & frozenset(val)
    return all(val[g] < v(val, R) for g in val if g not in R)


def robust(val, Q):
    return v(val, Q) >= sum(val[g] for g in val if g not in Q)


def level(val, S):
    x = v(val, S); gs = list(val)
    return sum(1 for r in range(len(gs) + 1) for T in itertools.combinations(gs, r) if sum(val[g] for g in T) < x)


def apas(pr):
    n, m = pr.n, pr.m
    opts = [[frozenset(p) for p in itertools.combinations(range(m), 2) if admissible(pr.vals[i], frozenset(p))] for i in range(n)]
    def gen(k, used, cur):
        if k == n: yield tuple(cur); return
        for p in opts[k]:
            if p & used: continue
            cur.append(p); yield from gen(k + 1, used | p, cur); cur.pop()
    for Q in gen(0, frozenset(), []):
        yield Q, frozenset(range(m)) - frozenset().union(*Q)


def threat_edges(pr, Q, L):
    return [(o, y) for o in range(pr.n) for y in range(pr.n) if y != o and threatened(pr.vals[y], Q[o] | L, Q[y] & pr.R[y])]


def pool_optimal(pr, Q, L):
    return all(v(pr.vals[i], p) <= v(pr.vals[i], Q[i]) for i in range(pr.n) for p in itertools.combinations(sorted(Q[i] | L), 2))


def top(val):
    return max(val, key=lambda g: val[g])


def kind(val, Q):
    """T3j/T4j: top + a good not in R; T4d: {a, d}; R: a rich pair without the top (4-good); robust ones are 'rob'."""
    if robust(val, Q): return 'rob'
    a = top(val); R = Q & frozenset(val)
    if a in R: return ('T%dj' % len(val)) if len(R) == 1 else 'T4d'
    return 'R'


def rotation(pr, Q, L, cyc, sigma):
    """cyc: list of agents with sigma[c] = successor (threatened by c). Plain rotation: the successor gets Q_c; at a
    rich-pair agent c' the successor takes {top, s'} with s' in L when Q_c does not contain s' (modified)."""
    newQ = list(Q); newL = set(L)
    pred = {sigma[c]: c for c in cyc}
    for c2 in cyc:
        newQ[c2] = Q[pred[c2]]
    for c2 in cyc:
        val = pr.vals[c2]
        if kind(val, Q[c2]) == 'R':
            a = top(val); s = [g for g in val if g not in Q[c2] and g != a][0]
            if s in L and a in Q[pred[c2]]:
                y = next(iter(Q[pred[c2]] - {a}))
                newQ[c2] = frozenset([a, s]); newL.discard(s); newL.add(y)
                return newQ, frozenset(newL), c2
    return newQ, frozenset(newL), None


def is_apa(pr, Q, L):
    U = frozenset().union(*Q)
    return (all(len(q) == 2 for q in Q) and len(U) == 2 * pr.n and not (U & L) and len(U | L) == pr.m
            and all(admissible(pr.vals[i], Q[i]) for i in range(pr.n)))


RKEYS = ['Lemma R (i), 3-good agent robust after the plain rotation', 'Lemma R (i), kind (D) robust after the plain rotation',
         'Lemma R (ii), kind (R), s in the predecessor pair, robust after the plain rotation',
         'Lemma R (iii), kind (R), s in the pool, robust in the modified rotation (an APA)',
         'Lemma R, plain rotations that are APAs (cycles)', 'kind (T) 4-good agents on rotated cycles (no claim)',
         'VIOLATION R: plain rotation not an APA', 'VIOLATION R (i): not robust', 'VIOLATION R (ii): not robust',
         'VIOLATION R (iii): modified rotation not an APA, or not robust', "VIOLATION R: kind (R) without its top in Q', or s elsewhere"]


def lemma_r_cases(pr, Q, L, cyc, sigma, C):
    """B': Lemma R (i)-(iii) for each agent of the cycle separately (the counts are per agent and cycle)."""
    pred = {sigma[c]: c for c in cyc}
    newQ = list(Q)
    for c in cyc: newQ[c] = Q[pred[c]]
    if is_apa(pr, newQ, L): C[RKEYS[4]] += 1
    else: C[RKEYS[6]] += 1
    for c in cyc:
        val = pr.vals[c]; k = kind(val, Q[c]); Qp = Q[pred[c]]
        if len(val) == 3 or k == 'T4d':
            ok = robust(val, Qp)
            C[RKEYS[0 if len(val) == 3 else 1] if ok else RKEYS[7]] += 1
        elif k == 'R':
            a = top(val); s = [g for g in val if g not in Q[c] and g != a][0]
            if a not in Qp: C[RKEYS[10]] += 1
            elif s in Qp: C[RKEYS[2] if robust(val, Qp) else RKEYS[8]] += 1
            elif s in L:
                y = next(iter(Qp - {a})); mQ = list(newQ); mQ[c] = frozenset([a, s])
                ok = is_apa(pr, mQ, (L - {s}) | {y}) and robust(val, mQ[c])
                C[RKEYS[3] if ok else RKEYS[9]] += 1
            else: C[RKEYS[10]] += 1
        elif k == 'T4j': C[RKEYS[5]] += 1


def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=') for a in sys.argv[1:] if a.startswith('--'))
    rand = int(opt.get('rand', 0)); seed = int(opt.get('seed', 1))
    only = set(map(int, opt['only'].split(','))) if 'only' in opt else None
    for f in files:
        C = collections.Counter({k: 0 for k in RKEYS}); t0 = time.time(); rng = random.Random(seed)
        for ci, (n, m, sets) in enumerate(load_cores(f)):
            if only is not None and ci not in only: continue
            if m < 2 * n + 1: continue
            for vals in profiles(sets, m, rng, rand if rand else None):
                pr = Profile(vals, m)
                if not any(not pr.info(P)[1] for P in pr.valid()): continue      # fewest frozen agents is 0
                C['profiles (f = 0, omega >= 1)'] += 1
                A = list(apas(pr))
                if not A: C['VIOLATION: no APA'] += 1; continue
                keyv = []
                for Q, L in A:
                    rb = [robust(pr.vals[i], Q[i]) for i in range(n)]
                    E = threat_edges(pr, Q, L)
                    owners = [o for o in range(n) if not any(e[0] == o for e in E)]
                    keyv.append((sum(rb), sum(level(pr.vals[i], Q[i]) for i in range(n))))
                    if any(rb[y] for o, y in E): C['VIOLATION: robust agent threatened'] += 1
                    if not pool_optimal(pr, Q, L): continue
                    C['pool-optimal APAs'] += 1
                    if any(c > 1 for c in collections.Counter(y for o, y in E).values()): C['VIOLATION A: two owners'] += 1
                    if all(kind(pr.vals[i], Q[i]) == 'T4j' for i in range(n)): C['VIOLATION C: all top+junk at a pool-optimal APA'] += 1
                    if owners: continue
                    C['pool-optimal APAs without valid owner'] += 1
                    sigma = {o: y for o, y in E}
                    if sorted(sigma.values()) != list(range(n)) or any(rb): C['VIOLATION B: not a permutation / robust agent'] += 1; continue
                    seen = set()
                    for s0 in range(n):
                        if s0 in seen: continue
                        cyc = []; x = s0
                        while x not in seen: seen.add(x); cyc.append(x); x = sigma[x]
                        kinds = [kind(pr.vals[c], Q[c]) for c in cyc]
                        newQ, newL, mod = rotation(pr, Q, L, cyc, sigma)
                        ok = (len(frozenset().union(*newQ)) == 2 * n and not (frozenset().union(*newQ) & newL)
                              and all(admissible(pr.vals[i], newQ[i]) for i in range(n)))
                        rob_new = any(robust(pr.vals[c], newQ[c]) for c in cyc)
                        if all(k == 'T4j' for k in kinds): C['cycles of top+junk 4-good agents'] += 1
                        elif not (ok and rob_new): C['VIOLATION B: rotation'] += 1
                        else: C['rotations checked (%s)' % ('modified' if mod is not None else 'plain')] += 1
                        lemma_r_cases(pr, Q, L, cyc, sigma, C)
                best = max(keyv)
                for (Q, L), kv in zip(A, keyv):
                    if kv == best:
                        C['(r, sum-level)-maxima'] += 1
                        E = threat_edges(pr, Q, L)
                        if all(any(e[0] == o for e in E) for o in range(n)): C['VIOLATION D: maximum without valid owner'] += 1
        print(f'FILE {f} ({time.time() - t0:.0f} s)')
        for k in sorted(C): print(f'  {k}: {C[k]}')
        sys.stdout.flush()


if __name__ == '__main__':
    main()
