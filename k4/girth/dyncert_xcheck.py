"""Cross-check of the two implementations of the DYN pipeline (Algorithm 2 with the G1 repair, then dynamic parking
with envy-cycle rotation): dyncert.Run (ordinal, written for the certification) against lss.py (Run.alg2_safe +
park_dynamic_ec), on random strict profiles of random cores, every labeling, comparing success per labeling.

    python3 k4/girth/dyncert_xcheck.py PROFILES SEED
"""
import collections
import random
import sys

from dyncert import Core, FastRun as Run, labelings
from lss import Inst, Run as LRun, park_dynamic_ec, is_efx0
from sources import cores, domains


def main():
    per, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    allc = cores(3) + cores(4)
    C = collections.Counter()
    for t in range(per):
        f, idx, sets, m = rng.choice(allc)
        doms = domains(sets, m)
        core = Core(sets, m, doms)
        rep = [rng.randrange(len(d)) for d in doms]
        ds = [doms[i][rep[i]] for i in range(len(sets))]
        I = Inst([sorted(d) for d in ds], [[d[g] for g in sorted(d)] for d in ds], m)
        for lab in labelings(core):
            a = Run(core, rep, lab).go()
            r = LRun(I, lab)
            r.alg2_safe()
            b = is_efx0(I, r.X) and park_dynamic_ec(I, r.X, r.U) is not None
            C['runs'] += 1
            C['agree'] += a == b
            if a != b:
                print('MISMATCH', I, lab, a, b, flush=True)
            # soundness of the class: profiles agreeing on every recorded comparison run the same way
            run = Run(core, rep, lab)
            run.go()
            cls = run.box(tuple(core.full))
            for _ in range(2):
                rep2 = []
                for i in range(len(sets)):
                    ts = [t for t in range(len(doms[i])) if cls[i] >> t & 1]
                    rep2.append(rng.choice(ts))
                ds2 = [doms[i][rep2[i]] for i in range(len(sets))]
                J = Inst([sorted(d) for d in ds2], [[d[g] for g in sorted(d)] for d in ds2], m)
                r2 = LRun(J, lab)
                r2.alg2_safe()
                b2 = is_efx0(J, r2.X) and park_dynamic_ec(J, r2.X, r2.U) is not None
                C['class samples'] += 1
                C['class samples with the same outcome'] += b2 == a
                if b2 != a:
                    print('CLASS UNSOUND', I, lab, rep, rep2, flush=True)
    print('$ python3 k4/girth/dyncert_xcheck.py', per, seed, dict(C))


if __name__ == '__main__':
    main()
