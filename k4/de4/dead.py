"""Stopped walks and dead goods (k4/de4.md §7.7). EVIDENCE only.

  python3 k4/de4/dead.py stuck SOURCE PER JOBS SEED   every (H) state where DE's walk stops: is some leftover good dead,
                                                    is F1 empty, which moves improve it, and does a better state that
                                                    lowers no level exist (brute force over all valid states)
  python3 k4/de4/dead.py dead SOURCE PER JOBS SEED    every (H) state with a dead good: a cycle of label-free arcs
                                                    (Lemma 14), a cycle with one label, or hard; for the hard ones,
                                                    move PR, the refined walk and brute force

For a cycle of label-free arcs (Lemma 14) and a cycle with one label, the trade is built and checked (valid, strict
Pareto improvement); where it fails, move PR is tried as in the hard case.

SOURCE is a comma-separated list of certified core files under results/ (random strict profiles of random cores),
'rand' (random R1-cores: n = 3..5, m <= 11, agents with 3 or 4 goods, distinct random values, strictly balanced, no
tie between subset sums), or 'fixed:<sets as JSON>' (random strict profiles of one hypergraph), or 'hypergraphs:<file>' (random strict profiles of
random hypergraphs from the JSON file, path relative to the repository root).

Definitions (k4/de4.md §7.7). (H): every agent holds a good, Lemma 4/4' gives nothing, the state is not completable.
A leftover good h is dead if every free agent u is closed (Y_u is a danger set of another agent) or has a partial arc
with label {h}. G0: the label-free arcs, frozen j -> every agent wanting j's good, closed u -> every agent whose danger
set is Y_u. Hard: G0 is acyclic and no hungry agent (free, not closed) u has an arc with label {h} whose blocker reaches
u in G0. Move PR: a hungry u, an arc (x, D) into u with label {h}, a G0 path x = p_0, ..., p_k = r (r a sink, r != u);
x takes D, p_t takes p_(t-1)'s holding, r's holding is released, u takes its best allowed holding among the unassigned
goods. A move counts only if the result is valid and better in the order of §1 with no agent's level lower.
"""
import collections
import json
import multiprocessing as mp
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from de4lib import *  # noqa: F401,F403
from cycle import walk, walk2, arcs_into, strictly_pareto, ROOT
from check import better


def level_monotone(I, Y, Z):
    return all(level(I, i, Z[i]) >= level(I, i, Y[i]) for i in range(I.n)) and better(I, Y, Z)


def structure(I, Y):
    J = set(leftover(I, Y))
    W = wanted_goods(I, Y)
    free = [i for i in range(I.n) if not set(Y[i]) & W]
    G0 = collections.defaultdict(set)
    closed, arcs = set(), {}
    for j in range(I.n):
        if set(Y[j]) & W:
            for w in range(I.n):
                if Y[j][0] in wanted(I, w, Y[w]):
                    G0[j].add(w)
    for o in free:
        arcs[o] = arcs_into(I, Y, o, J)
        for _, x, D in arcs[o]:
            if not set(D) & J:
                G0[o].add(x)
                closed.add(o)
    return J, W, free, G0, closed, arcs


def dead_goods(I, Y, J, free, arcs, closed):
    return [h for h in sorted(J)
            if all(z in closed or any(set(D) & J == {h} and not set(Y[z]) <= set(D) for _, _, D in arcs[z])
                   for z in free)]


def reach(G0, x):
    seen, st = {x}, [x]
    while st:
        z = st.pop()
        for w in G0[z]:
            if w not in seen:
                seen.add(w)
                st.append(w)
    return seen


def acyclic(G0, n):
    color = [0] * n

    def dfs(z):
        color[z] = 1
        for w in G0[z]:
            if color[w] == 1 or (color[w] == 0 and not dfs(w)):
                return False
        color[z] = 2
        return True
    return all(color[z] or dfs(z) for z in range(n))


def sink_paths(G0, x, avoid):
    out = []

    def rec(p):
        if not G0[p[-1]]:
            out.append(p)
            return
        for w in G0[p[-1]]:
            if w not in p and w not in avoid:
                rec(p + [w])
    rec([x])
    return out


def best_holding(I, i, pool):
    c = [A for A in subsets([g for g in pool if g in I.v[i]]) if allowed(I, i, A)]
    return max(c, key=lambda A: I.val(i, A)) if c else ()


def pr_moves(I, Y, h, st):
    J, W, free, G0, closed, arcs = st
    out = []
    for u in free:
        if u in closed:
            continue
        for _, x, D in arcs[u]:
            if set(D) & J != {h} or set(Y[u]) <= set(D):
                continue
            for p in sink_paths(G0, x, {u}):
                Z = [tuple(A) for A in Y]
                Z[x] = tuple(D)
                for t in range(1, len(p)):
                    Z[p[t]] = tuple(Y[p[t - 1]])
                Z[u] = ()
                held = [g for A in Z for g in A]
                if len(held) != len(set(held)):
                    continue
                Z[u] = tuple(best_holding(I, u, [g for g in range(I.m) if g not in set(held)]))
                if valid(I, Z) and level_monotone(I, Y, Z):
                    out.append(Z)
    return out


def g0_cycle(G0, n):
    color, stack = [0] * n, []

    def dfs(z):
        color[z] = 1
        stack.append(z)
        for w in sorted(G0[z]):
            if color[w] == 1:
                return stack[stack.index(w):]
            if color[w] == 0:
                c = dfs(w)
                if c:
                    return c
        stack.pop()
        color[z] = 2
        return None
    for z in range(n):
        if not color[z]:
            c = dfs(z)
            if c:
                return c
    return None


def g0_path(G0, x, o):
    prev, st = {x: None}, [x]
    while st:
        z = st.pop(0)
        if z == o:
            p = [o]
            while prev[p[-1]] is not None:
                p.append(prev[p[-1]])
            return p[::-1]
        for w in sorted(G0[z]):
            if w not in prev:
                prev[w] = z
                st.append(w)
    return None


def trade_ok(I, Y, takes):
    Z = [tuple(A) for A in Y]
    for i, N in takes.items():
        Z[i] = tuple(N)
    held = [g for A in Z for g in A]
    return len(held) == len(set(held)) and valid(I, Z) and strictly_pareto(I, Y, Z)


def classify_dead(I, Y, dg, st):
    """('G0 cycle' | 'one-label cycle' | 'hard', whether the cycle's trade is a valid strict Pareto improvement)"""
    J, W, free, G0, closed, arcs = st
    c = g0_cycle(G0, I.n)
    if c:
        return 'G0 cycle', trade_ok(I, Y, {c[(t + 1) % len(c)]: Y[c[t]] for t in range(len(c))})
    found = False
    for o in free:
        if o in closed:
            continue
        for _, x, D in arcs[o]:
            if not set(D) & J or o not in reach(G0, x):
                continue
            found = True
            p = g0_path(G0, x, o)
            takes = {x: D}
            for t in range(1, len(p)):
                takes[p[t]] = Y[p[t - 1]]
            if trade_ok(I, Y, takes):
                return 'one-label cycle', True
    return ('one-label cycle', False) if found else ('hard', None)


def strict_ok(I):
    for i in range(I.n):
        sums = [I.val(i, A) for A in subsets(I.sets[i])]
        if len(sums) != len(set(sums)):
            return False
    return True


def random_r1(rng):
    while True:
        n = rng.randint(3, 5)
        m = rng.randint(n + 2, min(3 * n + 1, 11))
        sets = [sorted(rng.sample(range(m), rng.choice([3, 4, 4, 4]))) for _ in range(n)]
        vals = [rng.sample(range(1, 30), len(S)) for S in sets]
        if any(max(V) >= sum(V) - max(V) for V in vals):
            continue
        I = Inst(sets, vals, m)
        if strict_ok(I):
            return I


def instances(source, per, rng):
    if source == 'rand':
        for _ in range(per):
            yield random_r1(rng)
        return
    if source.startswith('fixed:'):
        cores = [json.loads(source[6:])]
    elif source.startswith('hypergraphs:'):
        cores = json.load(open(os.path.join(ROOT, source[12:])))['hypergraphs']
    else:
        cores = []
        for f in source.split(','):
            cores += load_cores(os.path.join(ROOT, 'results', f))
    for _ in range(per):
        s = rng.choice(cores)
        yield Inst(s, random_profile(s, rng))


def h_states(I):
    """valid states with every agent holding a good and no Lemma 4/4' move (completability checked by the caller)"""
    for Y in all_states(I):
        if all(Y) and chain_move(I, Y) is None:
            yield Y


def job_stuck(args):
    source, per, seed = args
    C, ex = collections.Counter(), []
    for I in instances(source, per, random.Random(seed)):
        S = None
        for Y in h_states(I):
            C['valid states, every agent holding a good, no Lemma 4/4\' move'] += 1
            ws, _, _ = walk(I, Y)
            if ws == 'ok':
                continue
            if completion(I, Y) is not None:
                C['walk stops, completable (not (H))'] += 1
                continue
            C['(H) and the walk stops'] += 1
            st = structure(I, Y)
            dg = dead_goods(I, Y, st[0], st[2], st[5], st[4])
            F1 = [i for i in st[2] if len(Y[i]) == 1]
            C['  some leftover good dead (D): %s; F1 empty: %s' % (bool(dg), not F1)] += 1
            S = S if S is not None else all_states(I)
            lm = [Z for Z in S if level_monotone(I, Y, Z)]
            C['  better state lowering no level exists (Conjecture 11\'\'): %s' % bool(lm)] += 1
            s2, Z2, _ = walk2(I, Y)
            how = []
            if s2 == 'ok' and strictly_pareto(I, Y, Z2):
                how.append('refined walk')
            if dg:
                kind, ok = classify_dead(I, Y, dg, st)
                how.append('dead good: ' + kind + ('' if ok is None else ' (trade valid)' if ok else ' (TRADE INVALID)'))
                if not ok and any(pr_moves(I, Y, h, st) for h in dg):
                    how.append('PR')
            C['  ' + ', '.join(how or ['none of these'])] += 1
            if not dg or not lm:
                ex.append((I.sets, I.v, I.m, Y))
    return C, ex


def job_dead(args):
    source, per, seed = args
    C, ex = collections.Counter(), []
    for I in instances(source, per, random.Random(seed)):
        S = None
        for Y in h_states(I):
            st = structure(I, Y)
            if not st[0]:
                continue
            dg = dead_goods(I, Y, st[0], st[2], st[5], st[4])
            if not dg:
                continue
            if completion(I, Y) is not None:
                C['dead good, completable (not (H))'] += 1
                continue
            C['(H) with a dead good'] += 1
            kind, ok = classify_dead(I, Y, dg, st)
            C['  ' + kind + ('' if ok is None else ': trade valid and Pareto-improving' if ok else ': TRADE INVALID')] += 1
            if not ok:
                pr = any(pr_moves(I, Y, h, st) for h in dg)
                s2, Z2, _ = walk2(I, Y)
                w2 = s2 == 'ok' and strictly_pareto(I, Y, Z2)
                S = S if S is not None else all_states(I)
                lm = any(level_monotone(I, Y, Z) for Z in S)
                C['    move PR: %s; refined walk: %s; better state lowering no level: %s' % (pr, w2, lm)] += 1
                if not lm or not (pr or w2):
                    ex.append((I.sets, I.v, I.m, Y))
    return C, ex


if __name__ == '__main__':
    mode, source, per, jobs, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    f = {'stuck': job_stuck, 'dead': job_dead}[mode]
    tot, EX = collections.Counter(), []
    with mp.Pool(os.cpu_count()) as p:
        for c, ex in p.imap_unordered(f, [(source, per, seed + s) for s in range(jobs)]):
            tot.update(c)
            EX += ex
    print(f'{mode} {source}: {jobs} jobs x {per} profiles, seeds {seed}..{seed + jobs - 1}')
    for k in sorted(tot):
        print(f'{tot[k]:>10}  {k}')
    for e in EX[:10]:
        print('NOT RESOLVED BY THE MOVES ABOVE', json.dumps({'sets': e[0], 'vals': [[e[1][i][g] for g in e[0][i]] for i in range(len(e[0]))],
                                       'm': e[2], 'Y': e[3]}))
    sys.exit(1 if EX else 0)
