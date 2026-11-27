"""The smallest gap configurations of K4.C4.GAP (attempts/k4-c4-exposure-counting.md) and how LB4r repairs them
(k4/sdc.md §26).  For each configuration: the LB4r state of the recorded picks after envy-free upgrades, then every
rotation sequence of length <= 2 that reaches a state with an output, with the owner and the completion.

    python3 k4/sdc/gap_explain.py"""
import os, sys, itertools
import _paths
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4'))
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4', 'c4_verify_H'))
import lb4r as M
import rulef_model as RM

# picks as recorded in attempts/k4-c4-exposure-counting.md (agent -> pick)
CONFIGS = [
    ('1. exposed non-leader', [[0, 1, 3, 4], [2, 3, 4], [2, 3, 4]], [[3, 6, 8, 4], [2, 3, 4], [2, 3, 4]], [3, 2, 4]),
    ('2. deficit 2', [[0, 2, 3, 4], [1, 2, 3, 4]], [[2, 7, 10, 4], [6, 3, 7, 5]], [2, 3]),
    ('3. earlier-block deficit', [[0, 1, 2, 3], [2, 4, 5], [3, 4, 5]], [[3, 4, 2, 8], [2, 4, 3], [4, 2, 3]], [1, 4, 3]),
]


def describe(inst, s):
    base, pick, marked = s
    needs = M.all_needs(inst, s); NA = M.NA_of(needs); fr = M.frozen_pre(inst, s, NA)
    J = [g for g in range(inst.m) if base[g] == -1]
    out = []
    for i in range(inst.n):
        out.append('a%d base=%s%s%s needs=%s' % (i, M.base_of(inst, s, i), ' marked' if marked[i] else '', ' FROZEN' if fr[i] else '', sorted(needs[i])))
    return '; '.join(out) + ' | J=%s omega=%d' % (J, M.omega(inst, s, needs))


def outputs(inst, s):
    res = []
    for o in [None] + list(range(inst.n)):
        ok, X = M.output_sat(inst, s, o, 'bundle', want_model=True)
        if ok: res.append((o, X))
    return res


if __name__ == '__main__':
    print('$ python3 k4/sdc/gap_explain.py')
    for name, sets, vals, picks in CONFIGS:
        inst = RM.make_inst(sets, vals)
        base = [-1] * inst.m
        for i, g in enumerate(picks): base[g] = i
        s0 = (tuple(base), tuple(picks), tuple([False] * inst.n))
        s1 = M.up_run(inst, s0, 'envyFree')[0]
        print('==', name, 'picks', picks)
        print('   state:', describe(inst, s1))
        print('   outputs without rotation:', [o for o, _ in outputs(inst, s1)], '; Lemma K deficit', RM.deficit_K(inst, s1))
        for s2, (c, O) in M.rot_steps(inst, s1).items():
            outs = outputs(inst, s2)
            tag = 'OUTPUT owners %s' % [o for o, _ in outs] if outs else 'no output'
            print('   rotate chain %s, O=%s -> %s | %s' % (list(c), list(O), tag, describe(inst, s2)))
            if outs:
                o, X = outs[0]
                print('        completion (owner %s):' % o, X)
            else:
                for s3, (c2, O2) in M.rot_steps(inst, s2).items():
                    outs3 = outputs(inst, s3)
                    if outs3:
                        print('        then chain %s, O=%s -> OUTPUT owners %s | %s' % (list(c2), list(O2), [o for o, _ in outs3], describe(inst, s3)))
