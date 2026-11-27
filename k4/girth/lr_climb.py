"""Adversarial hill climbing against Conjecture LR (k4/girth.md section 4).  EVIDENCE only.

State: a linear hypergraph with degree <= 4 and additive values.  Score of an instance: over every vertex 0 (default
labels) and R random labelings, the number of LSS-ROT terminal states in which some leftover good (all valuers envied)
has no common safe vertex, weighted up when no non-envied agent holds a single good (no slack absorber), and a large
bonus for a state that no parking completes (a counterexample).  Mutations: change one value, add a good on agents with
spare degree (keeping linearity), delete a good.  Restarts when stuck.

    python3 k4/girth/lr_climb.py SEED SECONDS
"""
import itertools
import random
import sys
import time

from lss import Inst, labels, random_labels, lss_rot, envied, park_any_state, two_cycles


def to_inst(n, edges, vals):
    sets = [[g for g, e in enumerate(edges) if a in e] for a in range(n)]
    return Inst(sets, [[vals[(a, g)] for g in sets[a]] for a in range(n)], len(edges))


def score(I, rng, R=3):
    s = 0
    for z in range(I.n):
        for rep in range(R):
            lab = labels(I, z) if rep == 0 else random_labels(I, z, rng)
            r = lss_rot(I, lab)
            X, U = r.X, r.U
            env = {i for i in range(I.n) if envied(I, X, i)}
            N = [u for u in range(I.n) if u not in env]
            S = {i: {u for u in N if I.val(i, X[u] | (U & I.R[i])) <= I.val(i, X[i])} for i in env}
            bad = 0
            for e in U:
                if I.edge[e] and all(i in env for i in I.edge[e]):
                    com = set(N)
                    for i in I.edge[e]:
                        com &= S[i]
                    bad += not com
            if bad:
                poor = sum(1 for u in N if len(X[u]) == 1)
                s += 1 + bad + (5 if poor == 0 else 0)
                if park_any_state(I, X, U) is None:
                    return 10 ** 6, (lab, [sorted(b) for b in X], sorted(U))
    return s, None


def random_start(rng):
    n = rng.randint(4, 8)
    edges, deg, pairs = [], [0] * n, set()
    for _ in range(rng.randint(6, 16)):
        k = rng.choice([1, 2, 2, 3])
        free = [a for a in range(n) if deg[a] < 4]
        if len(free) < k:
            continue
        e = sorted(rng.sample(free, k))
        if any(p in pairs for p in itertools.combinations(e, 2)):
            continue
        edges.append(e)
        pairs |= set(itertools.combinations(e, 2))
        for a in e:
            deg[a] += 1
    vals = {(a, g): rng.randint(1, 30) for g, e in enumerate(edges) for a in e}
    return n, edges, vals


def mutate(n, edges, vals, rng):
    edges = [list(e) for e in edges]
    vals = dict(vals)
    r = rng.random()
    if r < 0.7 and vals:
        k = rng.choice(list(vals))
        vals[k] = max(1, vals[k] + rng.choice([-5, -3, -2, -1, 1, 2, 3, 5]))
    elif r < 0.85:
        deg = [sum(a in e for e in edges) for a in range(n)]
        pairs = {p for e in edges for p in itertools.combinations(e, 2)}
        k = rng.choice([1, 2, 2, 3])
        free = [a for a in range(n) if deg[a] < 4]
        if len(free) >= k:
            e = sorted(rng.sample(free, k))
            if not any(p in pairs for p in itertools.combinations(e, 2)):
                g = len(edges)
                edges.append(e)
                for a in e:
                    vals[(a, g)] = rng.randint(1, 30)
    elif len(edges) > 3:
        g = rng.randrange(len(edges))
        edges.pop(g)
        nv = {}
        for (a, h), x in vals.items():
            if h < g:
                nv[(a, h)] = x
            elif h > g:
                nv[(a, h - 1)] = x
        vals = nv
    return n, edges, vals


def main():
    seed, secs = int(sys.argv[1]), float(sys.argv[2])
    rng = random.Random(seed)
    t0 = time.time()
    print('$ python3 k4/girth/lr_climb.py', *sys.argv[1:], flush=True)
    best_overall = 0
    restarts = evals = 0
    while time.time() - t0 < secs:
        n, edges, vals = random_start(rng)
        if not edges:
            continue
        restarts += 1
        I = to_inst(n, edges, vals)
        cur, _ = score(I, rng)
        stale = 0
        while stale < 60 and time.time() - t0 < secs:
            n2, e2, v2 = mutate(n, edges, vals, rng)
            if not e2:
                continue
            J = to_inst(n2, e2, v2)
            if two_cycles(J):
                continue
            sc, cex = score(J, rng)
            evals += 1
            if cex is not None:
                print('COUNTEREXAMPLE TO LR', J, cex, flush=True)
                return
            if sc >= cur:
                if sc > cur:
                    stale = 0
                n, edges, vals, cur = n2, e2, v2, sc
            else:
                stale += 1
        if cur > best_overall:
            best_overall = cur
            print('restart %d: best score %d on %s' % (restarts, cur, to_inst(n, edges, vals)), flush=True)
    print('no counterexample; restarts %d, evaluations %d, best score %d' % (restarts, evals, best_overall), flush=True)


if __name__ == '__main__':
    main()
