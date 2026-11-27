"""Where the greedy k* rule (greedy_kstar.py) fails from a start, classify the first rotations that do lead to an LB4r
output within two rotations: does the chain end at r (the last non-frozen unmarked agent of the order), is k threatened by
the end's bundle W, chain length (k4/sdc.md §24).  Screen set, n <= 5, every order.

    python3 k4/sdc/rot_classify.py"""
import sys, itertools, collections
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from blocks4 import M, RM
from rd_check import state_of
from greedy_kstar import greedy
print('$ python3 k4/sdc/rot_classify.py')
C = collections.Counter()
for name, sets, vals, m in instances('screen'):
    n = len(sets)
    if n > 5: continue
    E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
    for i, (S, V) in enumerate(zip(sets, vals)):
        for g, x in zip(S, V): v[i][g] = x
    inst = M.Inst(v)
    for o in itertools.permutations(range(n)):
        s0 = state_of(inst, sd(E, list(o))[0])
        res = None
        for pol in ('shrink', 'envyFree', 'none'):
            s1 = M.up_run(inst, s0, pol)[0] if pol != 'none' else s0
            d, how = greedy(inst, s1, o, n)
            if d is not None: res = d; break
        if res is not None: continue
        # greedy failed from this order: find successful first rotations (one-step to output, or two-step)
        for pol in ('shrink', 'envyFree', 'none'):
            s1 = M.up_run(inst, s0, pol)[0] if pol != 'none' else s0
            if M.any_output(inst, s1, 'bundle'): C['(output w/o rotation under another policy?)'] += 1; break
            needs = M.all_needs(inst, s1); NA = M.NA_of(needs); fa = M.frozen_at(inst, s1, NA)
            cand_r = [i for i in o if not fa[i] and not s1[2][i]]; r = cand_r[-1] if cand_r else None
            for s2, (c, O) in M.rot_steps(inst, s1).items():
                ok1 = bool(M.any_output(inst, s2, 'bundle'))
                ok2 = ok1 or any(M.any_output(inst, s3, 'bundle') for s3 in M.rot_steps(inst, s2))
                if not ok2: continue
                k, t = c[0], c[-1]
                Wt = set(g for g in range(m) if s1[0][g] == -1) | set(M.base_of(inst, s1, t))
                thr_t = RM.threatened(inst, k, Wt, M.base_of(inst, s1, k))
                C['good first rotation: chain end %s, k threatened by W_end %s, end marked %s, chain len %d, %s' % (
                    'r' if t == r else 'other', thr_t, bool(s1[2][t]), len(c), 'one step' if ok1 else 'two steps')] += 1
            break
for k in sorted(C, key=lambda x: -C[x]): print(C[k], k)
