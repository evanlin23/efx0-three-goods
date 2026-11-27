"""The certifier's counterexamples to R2-M and R2* (k4/ttc.md §14.6; attempts/k4-ttc-r2-owner-free.md), replayed with
this workstream's code, and the target R2-O tested on them: for every repairing move, is it canonical (x_0 dangerous,
x_1 wants y_{x_0}), does it end at a receiver, which owners give a one-absorber completion (oc_absorb-style SAT with a
prescribed absorber, ttclib.extends_owner), is there an owner-free completion (every agent at most one junk good), and
(with MC_DIR set to proof/k4-oc1max-multi's k4/oc1max_multi) which owners satisfy Lemma M^c with max_rest = 1.

    [MC_DIR=...] python3 k4/ttc/r2_owner_check.py"""
import sys, os
import ttclib as T
MCD = os.environ.get('MC_DIR')
if MCD:
    sys.path.insert(0, MCD)
    import mc as MC
    from mmlib import Inst

CASES = [  # from compute/k4-oc1max-cert, results/k4_oc1max/r2m_fails_n4.jsonl (the two examples of its 01:10 message)
    ([[0, 5, 6], [1, 5, 6], [2, 3, 4, 5], [2, 3, 4, 6]], [[2, 3, 4], [2, 3, 4], [6, 4, 5, 8], [6, 5, 4, 8]], (0, 1, 5, 6)),
    ([[0, 2, 6, 7], [1, 4, 5, 6], [3, 6, 7], [4, 5, 7]], [[4, 2, 10, 7], [3, 5, 6, 7], [2, 3, 4], [3, 2, 4]], (0, 6, 3, 7)),
    # the certifier's R2-O (generous) / R2-O' counterexample (r2og_fails_n4.jsonl, message of 01:35)
    ([[0, 2, 4, 8], [1, 4, 6, 8], [3, 5, 6, 7], [5, 7, 8]], [[2, 4, 8, 7], [3, 8, 4, 2], [3, 5, 7, 6], [3, 2, 4]], (4, 1, 6, 8)),
]

if __name__ == '__main__':
    print('$ python3 k4/ttc/r2_owner_check.py')
    for sets, vals, picks in CASES:
        m = 1 + max(max(s) for s in sets); E = T.Enc(sets, vals, m); b = T.base_of(E, picks); B = T.bundles(E, b)
        F = T.frozen_set(E, b); U = [i for i in range(E.n) if i not in F]; D = T.dangerous_set(E, b)
        print('sets', sets, 'vals', vals, 'picks', list(picks), 'receivers', U, 'dangerous', sorted(D),
              'hard', not T.extends_A(E, b, 1))
        r2o = False; r2m = False; r2s = False; r2op = False; r2op_ = False; r2c_ = False
        for b2, path in T.iter_chains_path(E, b):
            if not T.extends_A(E, b2, 1):
                continue
            canon = len(path) >= 2 and path[0] in D and E.v[path[1]].get(B[path[0]][0], 0) > T.val(E, path[1], B[path[1]])
            owners = [o for o in range(E.n) if T.extends_owner(E, b2, o)]
            free = T.extends_owner(E, b2, None)
            line = '  repairing %s %s, ends at %s; one-absorber owners %s; owner-free %s' % (
                path, 'canonical' if canon else 'non-canonical', 'a receiver' if path[-1] in U else 'a frozen agent',
                owners, free)
            if MCD:
                I = Inst(sets, vals, m); B2 = tuple(tuple(T.bundles(E, b2)[i]) for i in range(E.n))
                mc1 = [o for o in range(E.n) if MC.model(I, B2, o, 0, max_rest=1)]
                line += '; M^c max_rest 1 owners %s' % mc1
                if canon and path[-1] in U and path[0] in mc1:
                    r2m = True
            print(line)
            if canon and path[-1] in U:
                r2o |= any(o in U and o not in path for o in owners); r2s |= free
                r2op = locals().get('r2op', False) or free or any(o in U and o != path[-1] for o in owners)
                r2op_ = r2op; r2c_ = True
        print('  R2-C (some canonical chain to a receiver repairs, any owner):', r2c_,
              "| R2-O' (owner a receiver other than the end, or none):", r2op_)
        print('  R2-O (canonical chain to a receiver, another receiver owns):', r2o,
              '| R2* (same chains, owner-free):', r2s, *(('| R2-M (owner x_0, max_rest 1):', r2m) if MCD else ()))
