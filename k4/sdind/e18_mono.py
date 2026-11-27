"""E18: AB1 in monotone form (k4/sd_induct.md §3).  For each start Y and each unfrozen agent o that absorbs some
one-absorber completion: is there a completion X* with absorber o (or with no absorber) whose projections are EFX0
along some reverse-SD insertion order starting at o?  (Each inserted agent takes its X*-junk good from o and keeps it:
a monotone insertion.)

    python3 k4/sdind/e18_mono.py special|screen|suite|logs|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, completions, picks_base
from e1_delete import load
from e3_suffix import absorber
from e8_projection import schedulable

if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = 0
    print('$ python3 k4/sdind/e18_mono.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); seen = set(); C['instances'] += 1
        for o_ in itertools.permutations(range(I.n)):
            Y = list(sd(I, o_)[0])
            if tuple(Y) in seen: continue
            seen.add(tuple(Y))
            try:
                J, A = completions(I, picks_base(I, Y), 1)
            except ValueError:
                continue
            if len(A) == 0: continue
            W = wanted_by(I, Y)
            absb = collections.defaultdict(list)
            for x in A: absb[absorber(x, I.n)].append(x)
            for o in range(I.n):
                if W[o]: continue
                cands = absb.get(o, []) + absb.get(None, [])
                if not cands: continue
                C['(Y, o) cases'] += 1
                ok = any(schedulable(I, Y, J, x, o, W) for x in cands)
                C['(Y, o): some completion with absorber o (or none) is monotone-schedulable'] += ok
                if not ok and shown < 4:
                    shown += 1; print('NOT MONOTONE', name, json.dumps((sets, vals)), 'picks', Y, 'o', o, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
