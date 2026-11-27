"""Brute-force checks of the written lemmas of k4/de4.md §3, as stated, on every valid state of every suite instance
with n <= 4 and m <= 10, and on random profiles of the certified cores with n <= 4. Prints counts; exit status 0 iff
no violation.  python3 k4/de4/verify_lemmas.py [RANDOM_PROFILES_PER_CORE]"""
import json
import os
import random
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from de4lib import *  # noqa: F401,F403
from check import SUITE, ROOT, draft, suite_instances

C = Counter()
BAD = []


def bad(name, *info):
    C['VIOLATION ' + name] += 1
    if len(BAD) < 10:
        BAD.append((name,) + info)


def strictly_better_pareto(I, Y, Z):
    vy, vz = values(I, Y), values(I, Z)
    return all(a >= b for a, b in zip(vz, vy)) and vz != vy


def lemma4_upgrade(I, Y, x):
    """step (i): an allowed N ⊆ J ∩ R_x worth more than Y_x (for a free big-top holder of a: {a, b})"""
    J = leftover(I, Y)
    W = wanted_goods(I, Y)
    r = I.ranked(x)
    if (len(r) == 4 and Y[x] == (r[0],) and not set(Y[x]) & W and set(r[1:]) <= set(J)
            and I.v[x][r[1]] + I.v[x][r[2]] < I.v[x][r[0]]):
        return (r[0], r[1])
    ups = upgrades(I, x, J, Y[x])
    return ups[0] if ups else None


def lemma4_chain(I, Y, x, N):
    """step (ii): the chain of x taking N (or the want-ring it closes)"""
    W = wanted_goods(I, Y)
    free = not set(Y[x]) & W
    kind, p = want_path(I, Y, x) if not free else ('path', [x])
    if kind == 'ring':
        takes = {p[t + 1]: Y[p[t]] for t in range(len(p) - 1)}
        takes[p[0]] = Y[p[-1]]
    else:
        takes = {x: N}
        for t in range(1, len(p)):
            takes[p[t]] = Y[p[t - 1]]
    return apply_takes(I, Y, takes)


def check_lemma4(I, Y):
    J = leftover(I, Y)
    for x in range(I.n):
        if I.val(x, [g for g in J if g in I.v[x]]) <= I.val(x, Y[x]):
            continue
        C['lemma4 instances'] += 1
        N = lemma4_upgrade(I, Y, x)
        if N is None:
            bad('lemma4 (i): no upgrade', Y, x)
            continue
        if len(N) == 3:
            r = I.ranked(x)
            if not (Y[x] == (r[0],) and set(N) == set(r[1:])):
                bad('lemma4 (i): triple not {b,c,d} of a holder of a', Y, x, N)
        Z = lemma4_chain(I, Y, x, N)
        if Z is not None and valid(I, Z) and strictly_better_pareto(I, Y, Z):
            continue
        if Z is None or len(N) != 3:
            bad('lemma4 (ii): chain invalid', Y, x, N, Z)
            continue
        # (iii): N threatens some i; i's chain must be valid with a non-triple upgrade
        thr = [i for i in range(I.n) if i != x and I.theta(i, N) > I.val(i, Z[i])]
        if not thr:
            bad('lemma4 (ii): triple chain invalid for another reason', Y, x, N, Z)
            continue
        C['lemma4 triple switches'] += 1
        i = thr[0]
        Ni = lemma4_upgrade(I, Y, i)
        if Ni is None or len(Ni) == 3:
            bad('lemma4 (iii): threatened agent has no non-triple upgrade', Y, x, i, Ni)
            continue
        Zi = lemma4_chain(I, Y, i, Ni)
        if not (Zi is not None and valid(I, Zi) and strictly_better_pareto(I, Y, Zi)):
            bad('lemma4 (iii): chain of the threatened agent invalid', Y, i, Ni, Zi)


def cor5_holds_a(I, Y):
    J = leftover(I, Y)
    return all(I.val(x, [g for g in J if g in I.v[x]]) <= I.val(x, Y[x]) for x in range(I.n))


def prop6_hyp(I, Y):
    J = set(leftover(I, Y))
    for i, A in enumerate(Y):
        if len(A) >= 2 and I.val(i, A) < I.val(i, [g for g in I.sets[i] if g not in A]):
            return False
        r = I.ranked(i)
        if (len(r) == 4 and A == (r[0],) and I.v[i][r[1]] + I.v[i][r[2]] < I.v[i][r[0]]
                and sum(g in J for g in r[1:]) >= 2):
            return False
    return True


def de_finish_F1(I, Y):
    """DE's single-owner rule with the owner in F1 (free, at most one good), as in Proposition 6"""
    J = leftover(I, Y)
    W = wanted_goods(I, Y)
    F1 = [i for i in range(I.n) if not set(Y[i]) & W and len(Y[i]) <= 1]
    import itertools
    for o in F1:
        recv = [i for i in F1 if i != o]
        for r in range(min(len(recv), len(J)) + 1):
            for H in itertools.combinations(J, r):
                for assign in itertools.permutations(recv, r):
                    X = [list(A) for A in Y]
                    for g, i in zip(H, assign):
                        X[i].append(g)
                    X[o] += [g for g in J if g not in H]
                    if efx0(I, X):
                        return X
    return None


def prop6_ring(I, Y):
    """Proposition 6's construction: distinct leftover goods for the agents of F1 in index order (first blocker,
    in index order, with an arc avoiding the used goods), first wanters for frozen agents; walk from the first agent."""
    J = leftover(I, Y)
    W = wanted_goods(I, Y)
    F1 = [i for i in range(I.n) if not set(Y[i]) & W and len(Y[i]) <= 1]
    sigma, take, used = {}, {}, set()
    for o in F1:
        found = None
        for x in range(I.n):
            if x == o:
                continue
            ups = [N for N in upgrades(I, x, list(Y[o]) + [g for g in J if g not in used], Y[x], must=Y[o])
                   if len(set(N) & set(J)) == 1]
            if ups:
                found = (x, ups[0])
                break
        if found is None:
            return 'no arc'
        sigma[o], take[o] = found
        used |= set(found[1]) & set(J)
    for j in range(I.n):
        if j not in sigma and len(Y[j]) == 1 and Y[j][0] in W:
            g = Y[j][0]
            sigma[j] = next(w for w in range(I.n) if g in wanted(I, w, Y[w]))
            take[j] = (g,)
    start = next((j for j in range(I.n) if len(Y[j]) == 1), None)
    if start is None:      # nobody holds a single good: the remark after Proposition 6 says Y is completable
        return 'ok' if completion(I, Y) is not None else 'no single good and not completable'
    path, pos, j = [], {}, start
    while j not in pos:
        pos[j] = len(path)
        path.append(j)
        if j not in sigma:
            return 'walk leaves'
        j = sigma[j]
    Z = apply_takes(I, Y, {sigma[w]: take[w] for w in path[pos[j]:]})
    if Z is None or not valid(I, Z):
        return 'invalid'
    return 'ok' if strictly_better_pareto(I, Y, Z) else 'not better'


def check_instance(I):
    if not valid(I, draft(I)):
        bad('lemma2: draft invalid', I.sets)
    for Y in all_states(I):
        C['valid states'] += 1
        for j, A in enumerate(Y):
            if len(A) == 2 and any(I.theta(i, A) > I.val(i, Y[i]) for i in range(I.n) if i != j):
                bad('lemma1(c): a pair threatens', Y)
            if len(A) == 3:
                r = I.ranked(j)
                if not (set(A) == set(r[1:]) and I.v[j][r[1]] + I.v[j][r[2]] < I.v[j][r[0]]):
                    bad('lemma1(c): a triple that is not {b,c,d} of a big-top agent', Y)
        check_lemma4(I, Y)
        if not cor5_holds_a(I, Y):
            continue
        C['states with cor5(a)'] += 1
        J = leftover(I, Y)
        W = wanted_goods(I, Y)
        F1 = [i for i in range(I.n) if not set(Y[i]) & W and len(Y[i]) <= 1]
        if any(not A for A in Y) and completion(I, Y) is None:
            bad('cor5(b)', Y)
        if len(J) <= len(F1) and completion(I, Y) is None:
            bad('cor5(c)', Y)
        if prop6_hyp(I, Y) and de_finish_F1(I, Y) is None:
            C['prop6 instances'] += 1
            res = prop6_ring(I, Y)
            C['prop6 ' + res] += 1
            if res != 'ok':
                bad('prop6: ' + res, Y)


if __name__ == '__main__':
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    for d, I in suite_instances(4, 10):
        if I is not None:
            check_instance(I)
    rng = random.Random(11)
    for f in ['k4_certs_2.json.gz', 'k4_certs_3.json.gz', 'k4_certs_4_n4_1.json.gz', 'k4_certs_4_n4_2.json.gz',
              'k4_certs_4_n4_3.json.gz', 'k4_certs_4_pure.json.gz']:
        for sets in load_cores(os.path.join(ROOT, 'results', f)):
            for _ in range(per if not f.startswith('k4_certs_4') else 1):
                check_instance(Inst(sets, random_profile(sets, rng)))
    for k in sorted(C):
        print(f'{k}: {C[k]}')
    for b in BAD:
        print(b)
    sys.exit(1 if any(k.startswith('VIOLATION') for k in C) else 0)
