"""E13: TP-SD-C (k4/sd_induct.md §5): does SOME serial-dictatorship outcome of every instance have a TP-shaped
one-absorber completion (every pick-frozen agent alone, absorber not pick-frozen)?  Also: an R1-priority outcome?
Lemma BOTH-TP (written proof in the note) makes TP-SD-C reducible over agents with a private top.

    python3 k4/sdind/e13_tpsdc.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, completions, picks_base
from e1_delete import load
from e3_suffix import absorber


def tp_ok(I, Y):
    W = wanted_by(I, Y); fr = [bool(w) for w in W]
    J, A = completions(I, picks_base(I, Y), 1)
    for x in A:
        o = absorber(x, I.n)
        if o is not None and fr[o]: continue
        if any(fr[x[t]] for t in range(len(J)) if x[t] != o): continue
        return True, len(A) > 0
    return False, len(A) > 0


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdind/e13_tpsdc.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 1: continue
        I = Inst(sets, vals, m); C['instances'] += 1
        seen = {}; anytp = False; anyone = False
        for o in itertools.permutations(range(I.n)):
            Y = tuple(sd(I, o)[0])
            if Y in seen: continue
            try:
                seen[Y] = tp_ok(I, list(Y))
            except ValueError:
                seen[Y] = (None, None)
            anytp |= bool(seen[Y][0]); anyone |= bool(seen[Y][1])
        C['some outcome has a one-absorber completion'] += anyone
        C['some outcome has a TP completion'] += anytp
        if not anytp:
            print('NO TP OUTCOME', name, json.dumps((sets, vals)), 'one-absorber outcome exists:', anyone, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
