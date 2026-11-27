"""The ring step of DE4 (k4/de4.md §7): danger sets, arcs, DE's walk with self-absorbing labels, partial paths.

  python3 k4/de4/cycle.py danger                 Lemma 7: threat <=> strict containment of a danger set (brute force)
  python3 k4/de4/cycle.py walk FILES PER SEEDS   Lemma 8 and Theorem 9 on every non-completable valid state of PER
                                                 random profiles per job (SEEDS jobs) of the cores in FILES, and the
                                                 coverage of the move catalogue (Conjecture 11)
  python3 k4/de4/cycle.py suite                  the same on the suite instances with n <= 5, m <= 12

Definitions (k4/de4.md §7). In a valid state Y with leftover goods J:
- a danger set of agent i is a minimal set D of goods of R_i, outside Y_i and not wanted by i, with v_i(D) > v_i(Y_i);
- an arc into a free agent o is a pair (x, D) with D a danger set of x, D ⊆ Y_o ∪ J and D ∩ Y_o nonempty; its label is
  D ∩ J; it is full if Y_o ⊆ D and partial otherwise.
"""
import collections
import itertools
import glob
import json
import multiprocessing as mp
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from de4lib import *  # noqa: F401,F403

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def danger_sets(I, i, Yi):
    vY = I.val(i, Yi)
    W = set(wanted(I, i, Yi))
    cand = [g for g in I.sets[i] if g not in Yi and g not in W]
    return [D for D in subsets(cand)
            if D and I.val(i, D) > vY and all(I.val(i, [g for g in D if g != h]) <= vY for h in D)]


def better(I, Y, Z):
    a, b = levsum(I, Z), levsum(I, Y)
    if a != b:
        return a > b
    vz, vy = values(I, Z), values(I, Y)
    return all(x >= y for x, y in zip(vz, vy)) and vz != vy


def strictly_pareto(I, Y, Z):
    vz, vy = values(I, Z), values(I, Y)
    return all(x >= y for x, y in zip(vz, vy)) and vz != vy


def arcs_into(I, Y, o, J, avoid=()):
    """arcs (key, x, D) into free agent o whose label avoids `avoid`, best first: fewest labels, then smallest D"""
    out = []
    for x in range(I.n):
        if x == o:
            continue
        for D in danger_sets(I, x, Y[x]):
            S = set(D)
            if S & set(Y[o]) and S <= set(Y[o]) | J and not S & set(avoid):
                out.append(((len(S & J), len(S), x), x, D))
    return sorted(out)


def walk(I, Y):
    """DE's walk. F1 (free, one good): distinct labels greedily in index order, best arc avoiding used labels.
    Frozen: first wanter. Free with >= 2 goods: best arc avoiding used labels, when reached. Start: first agent holding
    one good (else the first free agent). Returns (status, Z, info): status 'ok' with the traded state, 'F1 stuck',
    'F2 stuck' (agent), or 'invalid'."""
    J = set(leftover(I, Y))
    W = wanted_goods(I, Y)
    F = [i for i in range(I.n) if not set(Y[i]) & W]
    sigma, take, used = {}, {}, set()
    for o in F:
        if len(Y[o]) != 1:
            continue
        a = arcs_into(I, Y, o, J, used)
        if not a:
            return 'F1 stuck', None, o
        _, x, D = a[0]
        sigma[o], take[o] = x, D
        used |= set(D) & J
    for j in range(I.n):
        if j not in sigma and len(Y[j]) == 1 and Y[j][0] in W:
            g = Y[j][0]
            sigma[j] = next(w for w in range(I.n) if g in wanted(I, w, Y[w]))
            take[j] = (g,)
    start = next((j for j in range(I.n) if len(Y[j]) == 1), None)
    if start is None:
        start = next((j for j in F if Y[j]), None)
    path, pos, j = [], {}, start
    while j not in pos:
        pos[j] = len(path)
        path.append(j)
        if j not in sigma:
            a = arcs_into(I, Y, j, J, used)
            if not a:
                return 'F2 stuck', None, j
            _, x, D = a[0]
            sigma[j], take[j] = x, D
            used |= set(D) & J
        j = sigma[j]
    cyc = path[pos[j]:]
    Z = apply_takes(I, Y, {sigma[w]: take[w] for w in cyc})
    if Z is None or not valid(I, Z):
        return 'invalid', Z, cyc
    return 'ok', Z, cyc


def partial_paths(I, Y):
    """Move P (k4/de4.md §7.5): a free agent u holding >= 2 goods, an arc (x, D) into u that is partial; x takes D,
    u keeps its best allowed subset of Y_u minus D, x's old holding passes down the first-wanter walk (if x is frozen)
    to its end, whose old holding becomes leftover. Yields the improving valid results."""
    J = set(leftover(I, Y))
    W = wanted_goods(I, Y)
    for u in range(I.n):
        if set(Y[u]) & W or len(Y[u]) < 2:
            continue
        for _, x, D in arcs_into(I, Y, u, J):
            if set(Y[u]) <= set(D):
                continue
            rest = [g for g in Y[u] if g not in D]
            for K in sorted([K for K in subsets(rest) if allowed(I, u, K)], key=lambda K: -I.val(u, K)):
                takes = {x: tuple(D), u: tuple(K)}
                if set(Y[x]) & W:
                    kind, p = want_path(I, Y, x)
                    if kind == 'ring':
                        continue
                    for t in range(1, len(p)):
                        takes[p[t]] = Y[p[t - 1]]
                Z = apply_takes(I, Y, takes)
                if Z and valid(I, Z) and better(I, Y, Z):
                    yield Z
                    break


def keep_own_exchanges(I, Y):
    """Move K: two free agents exchange parts of their holdings (and leftover goods), each keeping part of its own,
    both strictly gaining value (the move of induct-g-r1)."""
    J = list(leftover(I, Y))
    W = wanted_goods(I, Y)
    F = [i for i in range(I.n) if not set(Y[i]) & W]
    for p in F:
        for q in F:
            if p >= q:
                continue
            pool = list(Y[p]) + list(Y[q]) + J
            for Np in subsets([g for g in pool if g in I.v[p]]):
                if not Np or not allowed(I, p, Np) or I.val(p, Np) <= I.val(p, Y[p]):
                    continue
                rest = [g for g in pool if g not in Np]
                for Nq in subsets([g for g in rest if g in I.v[q]]):
                    if not Nq or not allowed(I, q, Nq) or I.val(q, Nq) <= I.val(q, Y[q]):
                        continue
                    Z = apply_takes(I, Y, {p: Np, q: Nq})
                    if Z and valid(I, Z):
                        yield Z


def classify(I, Y, C, EX, name):
    """one non-completable valid state: check Lemma 8 / Theorem 9 and the catalogue"""
    C['non-completable valid states'] += 1
    if chain_move(I, Y) is not None:
        C['move: chain or self-upgrade (Lemma 4, 4\')'] += 1
        return
    st, Z, info = walk(I, Y)
    if st == 'F1 stuck':
        C['VIOLATION Lemma 8: single-good owner stuck'] += 1
        EX.append(('lemma8', name, Y))
        return
    if st == 'invalid':
        C['VIOLATION Theorem 9: closed walk invalid'] += 1
        EX.append(('thm9', name, Y))
        return
    if st == 'ok':
        if not strictly_pareto(I, Y, Z):
            C['VIOLATION Theorem 9: closed walk not Pareto-improving'] += 1
            EX.append(('thm9b', name, Y))
        else:
            C['move: walk ring (Theorem 9)'] += 1
        return
    C['walk stuck at a free agent holding >= 2 goods'] += 1
    st2, Z2, _ = walk2(I, Y)
    if st2 == 'ok' and strictly_pareto(I, Y, Z2):
        C['  resolved by walk2 (keep-own arcs, cycle-closing first)'] += 1
    elif any(True for _ in partial_paths(I, Y)):
        C['  resolved by move P (partial path)'] += 1
    elif any(True for _ in keep_own_exchanges(I, Y)):
        C['  resolved by move K (keep-own exchange)'] += 1
    else:
        C['  NOT RESOLVED by the catalogue'] += 1
        EX.append(('open', name, Y))


def _job(args):
    files, per, seed = args
    cores = []
    for f in files.split(','):
        cores += load_cores(os.path.join(ROOT, 'results', f))
    rng = random.Random(seed)
    C, EX = collections.Counter(), []
    for _ in range(per):
        sets = rng.choice(cores)
        I = Inst(sets, random_profile(sets, rng))
        for Y in all_states(I):
            if completion(I, Y) is None:
                classify(I, Y, C, EX, (sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)]))
    return C, EX


def mode_danger():
    bad = tot = notallowed = 0
    for f in sorted(glob.glob(os.path.join(ROOT, 'k4', 'suite', 'instances', '*.json'))):
        d = json.load(open(f))
        if 'sets' not in d or d.get('kind') or d['n'] > 4 or d['m'] > 9:
            continue
        I = Inst.from_json(d)
        for Y in all_states(I):
            W = wanted_goods(I, Y)
            for i in range(I.n):
                Ds = danger_sets(I, i, Y[i])
                notallowed += sum(not allowed(I, i, D) for D in Ds)
                pool = [g for g in range(I.m) if g not in Y[i] and g not in W]
                for r in (2, 3, 4):
                    for B in itertools.combinations(pool, r):
                        tot += 1
                        bad += (I.theta(i, B) > I.val(i, Y[i])) != any(set(D) < set(B) for D in Ds)
    print(f'Lemma 7 on the suite instances with n <= 4, m <= 9: {tot} bundles, {bad} mismatches; '
          f'danger sets that are not allowed holdings: {notallowed}')
    return bad == 0 and notallowed == 0


def report(C, EX):
    for k in sorted(C):
        print(f'{k}: {C[k]}')
    for e in EX[:10]:
        print(e)
    return not any(k.startswith('VIOLATION') or 'NOT RESOLVED' in k for k in C)



def keep_arcs_into(I, Y, o, J, W, avoid=(), given=None):
    """keep-own arcs into free agent o: a free x != o takes N ⊆ Y_o ∪ J ∪ Y_x (N meets Y_o and Y_x), allowed, worth
    more than Y_x; label N ∩ J avoids `avoid`; x may not keep goods it has already given away (given[x])."""
    out = []
    given = given or {}
    for x in range(I.n):
        if x == o or set(Y[x]) & W or not Y[x]:
            continue
        pool = [g for g in list(Y[o]) + list(J) + [g for g in Y[x] if g not in given.get(x, set())] if g in I.v[x]]
        for N in subsets(pool):
            S = set(N)
            if not S & set(Y[o]) or not S & set(Y[x]) or S & set(avoid) & J:
                continue
            if not allowed(I, x, N) or I.val(x, N) <= I.val(x, Y[x]):
                continue
            out.append(((len(S & J), 1, len(S), x), x, N))
    return sorted(out)


def walk2(I, Y):
    """Theorem 9's walk where a free agent holding >= 2 goods, when reached, may also use a keep-own arc (its blocker
    keeps part of its own holding). Kept goods may not be taken later. Returns (status, Z, info)."""
    J = set(leftover(I, Y))
    W = wanted_goods(I, Y)
    F = [i for i in range(I.n) if not set(Y[i]) & W]
    sigma, take, used, kept, given = {}, {}, set(), {}, {}
    for o in F:
        if len(Y[o]) != 1:
            continue
        a = arcs_into(I, Y, o, J, used)
        if not a:
            return 'F1 stuck', None, o
        _, x, D = a[0]
        sigma[o], take[o] = x, D
        used |= set(D) & J
        given[o] = set(Y[o])
    for j in range(I.n):
        if j not in sigma and len(Y[j]) == 1 and Y[j][0] in W:
            g = Y[j][0]
            sigma[j] = next(w for w in range(I.n) if g in wanted(I, w, Y[w]))
            take[j] = (g,)
            given[j] = {g}
    start = next((j for j in range(I.n) if len(Y[j]) == 1), None)
    if start is None:
        start = next((j for j in F if Y[j]), None)
    path, pos, j = [], {}, start
    while j not in pos:
        pos[j] = len(path)
        path.append(j)
        if j not in sigma:
            # closing arcs first: blocker already on the walk, label disjoint from the labels on that cycle
            close = []
            for k, x, N in ([((k[0], 0) + k[1:], x, D) for k, x, D in arcs_into(I, Y, j, J)]
                            + keep_arcs_into(I, Y, j, J, W, (), given)):
                if x not in pos or set(N) & kept.get(j, set()):
                    continue
                cyc_labels = set()
                for w in path[pos[x]:]:
                    if w in take:
                        cyc_labels |= set(take[w]) & J
                if not set(N) & J & cyc_labels:
                    close.append((k, x, N))
            if close:
                _, x, N = min(close)
                sigma[j], take[j] = x, N
                given[j] = set(N) & set(Y[j])
                j = x
                continue
            cand = [((k[0], 0) + k[1:], x, D) for k, x, D in arcs_into(I, Y, j, J, used)
                    if not set(D) & kept.get(j, set())]
            cand += [c for c in keep_arcs_into(I, Y, j, J, W, used, given) if not set(c[2]) & kept.get(j, set())]
            if not cand:
                return 'F2 stuck', None, j
            _, x, N = min(cand)
            sigma[j], take[j] = x, N
            used |= set(N) & J
            given[j] = set(N) & set(Y[j])
            if set(N) & set(Y[x]):
                kept[x] = set(N) & set(Y[x])
        j = sigma[j]
    cyc = path[pos[j]:]
    takes = {sigma[w]: take[w] for w in cyc}
    Z = apply_takes(I, Y, takes)
    if Z is None or not valid(I, Z):
        return 'invalid', Z, cyc
    return 'ok', Z, cyc

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'danger':
        sys.exit(0 if mode_danger() else 1)
    elif mode == 'suite':
        C, EX = collections.Counter(), []
        for f in sorted(glob.glob(os.path.join(ROOT, 'k4', 'suite', 'instances', '*.json'))):
            d = json.load(open(f))
            if 'sets' not in d or d.get('kind') or d['n'] > 5 or d['m'] > 12:
                continue
            I = Inst.from_json(d)
            for Y in all_states(I):
                if completion(I, Y) is None:
                    classify(I, Y, C, EX, d['id'])
        sys.exit(0 if report(C, EX) else 1)
    elif mode == 'walk':
        files, per, jobs = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
        C, EX = collections.Counter(), []
        with mp.Pool(os.cpu_count()) as p:
            for c, ex in p.imap_unordered(_job, [(files, per, 7000 + s) for s in range(jobs)]):
                C.update(c)
                EX += ex
        print(f'{files}: {jobs} jobs x {per} random profiles')
        sys.exit(0 if report(C, EX) else 1)
    else:
        sys.exit(__doc__)
