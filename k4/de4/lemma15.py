"""Brute-force check of Lemma 15 of k4/de4.md §7.7 (the lateral path), as stated, on every valid state.

  python3 k4/de4/lemma15.py suite                 suite instances with n <= 5, m <= 12
  python3 k4/de4/lemma15.py SOURCE PER JOBS SEED   random profiles (SOURCE as in k4/de4/dead.py)

Lemma 15. Let Y be valid, u a free agent holding its lower pair, (x, D) an arc into u with x frozen, D ∩ J = {h} and
D ∩ Y_u = {g}; let x = p_0 -> p_1 -> ... -> p_k = r (k >= 1) be a simple path of label-free arcs avoiding u that ends
at a free agent r, and let b_u lie in Y_r or in J minus {h}. Trade: x takes D; p_t takes p_(t-1)'s good (want arc) or
holding (closed arc); r's old holding is released; u takes N_u = {b_u, k_u} if that is an upper set of u (k_u the good
of Y_u other than g), else {b_u}. Then the result is valid, no level is lower, and the level sum is higher.

The script enumerates every such (Y, u, x, D, path) and checks the conclusion; it exits 1 on a violation.
"""
import collections
import json
import multiprocessing as mp
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from de4lib import *  # noqa: F401,F403
from dead import structure, instances, level_monotone
from check import suite_instances


def label_free_paths(I, Y, W, G0, x, u):
    """simple G0 paths from x avoiding u, ending at a free agent (any length >= 1)"""
    out = []

    def rec(p):
        z = p[-1]
        if len(p) > 1 and not set(Y[z]) & W:
            out.append(p)
        for w in sorted(G0[z]):
            if w not in p and w != u:
                rec(p + [w])
    rec([x])
    return out


def check_state(I, Y, C, bad):
    st = structure(I, Y)
    J, W, free, G0, closed, arcs = st
    for u in free:
        if not is_lower_pair(I, u, Y[u]):
            continue
        r_u = I.ranked(u)
        b_u = r_u[1]
        for _, x, D in arcs[u]:
            if not set(Y[x]) & W:
                continue                        # x must be frozen
            lab = set(D) & J
            inter = set(D) & set(Y[u])
            if len(lab) != 1 or len(inter) != 1:
                continue
            (h,), (g,) = tuple(lab), tuple(inter)
            k_u = next(q for q in Y[u] if q != g)
            for p in label_free_paths(I, Y, W, G0, x, u):
                r = p[-1]
                if not (b_u in Y[r] or (b_u in J and b_u != h)):
                    continue
                C['instances of the hypotheses'] += 1
                Z = [tuple(A) for A in Y]
                Z[x] = tuple(D)
                for t in range(1, len(p)):
                    Z[p[t]] = tuple(Y[p[t - 1]])
                N = (b_u, k_u)
                Z[u] = N if is_upper(I, u, N) else (b_u,)
                held = [q for A in Z for q in A]
                ok = (len(held) == len(set(held)) and valid(I, Z) and level_monotone(I, Y, Z)
                      and levsum(I, Z) > levsum(I, Y))
                C['  conclusion holds' if ok else '  VIOLATION'] += 1
                C['  u takes ' + ('{b, k}' if len(Z[u]) == 2 else '{b}') + (' from r' if b_u in Y[r] else ' from J')] += 1
                if not ok:
                    bad.append((I.sets, [[I.v[i][q] for q in I.sets[i]] for i in range(I.n)], I.m, Y, p, list(D)))


def job(args):
    source, per, seed = args
    C, bad = collections.Counter(), []
    for I in instances(source, per, random.Random(seed)):
        for Y in all_states(I):
            C['valid states'] += 1
            check_state(I, Y, C, bad)
    return C, bad


if __name__ == '__main__':
    C, bad = collections.Counter(), []
    if sys.argv[1] == 'suite':
        for d, I in suite_instances(5, 12):
            if I is None:
                continue
            for Y in all_states(I):
                C['valid states'] += 1
                check_state(I, Y, C, bad)
        print('lemma 15, suite instances with n <= 5, m <= 12')
    else:
        source, per, jobs, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        with mp.Pool(os.cpu_count()) as pool:
            for c, b in pool.imap_unordered(job, [(source, per, seed + s) for s in range(jobs)]):
                C.update(c)
                bad += b
        print(f'lemma 15, {source}: {jobs} jobs x {per} profiles, seeds {seed}..{seed + jobs - 1}')
    for k in sorted(C):
        print(f'{C[k]:>10}  {k}')
    for b in bad[:5]:
        print('VIOLATION', json.dumps(b))
    sys.exit(1 if bad else 0)
