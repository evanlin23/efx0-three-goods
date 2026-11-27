"""Inspect the two OC1-HD failures found by head_bign_climb.py at n = 6, m = 10 (results/k4_ttc/head_bign_climb_6_8.log):
which repairing chains exist, which can the head own, and which shape conditions they violate (k4/ttc.md §10).
Every improving chain of de_free's moves is enumerated (ttclib.iter_chains_path), completions by SAT.

    python3 k4/ttc/hd_fail_check.py"""
import json, collections
import ttclib as T

CASES = [
    ([[0, 2, 3, 1], [1, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]],
     [[2, 7, 8, 5], [2, 9, 5, 10], [10, 2, 6, 5], [8, 7, 1, 5], [10, 1, 2], [10, 9, 3, 1]], 10, [0, 1, 2, 3, 4, 5]),
    ([[0, 2, 3, 1], [1, 4, 5, 9], [1, 2, 0, 8], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]],
     [[2, 7, 8, 5], [5, 6, 4, 9], [13, 5, 4, 8], [10, 7, 1, 4], [7, 2, 10], [10, 6, 4, 1]], 10, [0, 1, 2, 3, 4, 5]),
]

if __name__ == '__main__':
    for k, (sets, vals, m, pi) in enumerate(CASES):
        E = T.Enc(sets, vals, m); Y = tuple(T.sd(E, pi)[0]); b = T.base_of(E, Y); B = T.bundles(E, b)
        D = T.dangerous_set(E, b); F = T.frozen_set(E, b)
        print('case', k, 'picks', Y, 'junk', [g for g in range(m) if b[g] < 0], 'frozen', sorted(F), 'dangerous', sorted(D))
        print('  one-absorber completion of the picks:', T.extends_A(E, b, 1))
        C = collections.Counter(); shown = 0; seen = set()
        for b2, path in T.iter_chains_path(E, b):
            if (b2, path) in seen:
                continue
            seen.add((b2, path))
            if not T.extends_A(E, b2, 1):
                continue
            B2 = T.bundles(E, b2)
            midjunk = any(sorted(B2[path[i]]) != sorted(B[path[i - 1]]) for i in range(1, len(path) - 1))
            owners = [o for o in range(E.n) if T.extends_owner(E, b2, o)]
            C['repairing chains'] += 1
            C['  head can own'] += path[-1] in owners and len(path) > 1
            C['  x0 dangerous'] += path[0] in D
            C['  head can own, x0 dangerous'] += path[-1] in owners and len(path) > 1 and path[0] in D
            C['  head can own, no middle junk'] += path[-1] in owners and len(path) > 1 and not midjunk
            if shown < 6:
                shown += 1
                print('  repairing chain', path, 'bases', B2, 'possible absorbers', owners, 'middle junk', midjunk)
        for kk in sorted(C):
            print(' ', kk, C[kk])
