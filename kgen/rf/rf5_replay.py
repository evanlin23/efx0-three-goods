"""Independent replay of ksens's RF5 (k4/ksens/refute_rf_k5.py on claude/k4-ksens @ 0db58f4b, not run here): a strict
n = 4, k = 5 instance where RF in its 'every receiver-first maximum-matching order' form fails.  Own checker
(rf_lib.Inst.oc1) and k4/sdc's oc1_mc2_rand.Inst.check (main, via MAINWT).  Also the weak form RF-exists: some
receiver-first maximum-matching order satisfies OC1.

    MAINWT=<main> python3 rf5_replay.py"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(os.environ['MAINWT'], 'k4', 'sdc'))
from rf_lib import Inst
from rf_run import strict_balanced
from oc1_mc2_rand import Inst as Inst2

SETS = [[0, 1, 2, 5, 6], [1, 2, 4, 5, 6], [3, 4, 5, 6], [3, 4, 5, 6]]
VALS = [[3, 35, 33, 43, 39], [20, 26, 16, 43, 32], [8, 2, 7, 4], [8, 2, 7, 4]]

if __name__ == '__main__':
    print('$ MAINWT=<main> python3 kgen/rf/rf5_replay.py')
    I = Inst(SETS, VALS); I2 = Inst2(SETS, VALS); N = I.nu(); n = I.n
    print('strict and balanced:', [strict_balanced(v) for v in VALS], 'nu', N)
    res = {}
    for o in itertools.permutations(range(n)):
        p = I.sd(o)
        if sum(x is not None for x in p) != N: continue
        if p not in res: res[p] = (I.oc1(p), I2.check(p))
    for p, r in sorted(res.items()): print('max vector', p, 'own:', r[0], '| second:', r[1])
    for p, (r, r2) in sorted(res.items()):
        if r != 'OC1 fails': continue
        rec, out, nonmax = I.rf(p, N)
        print('failing start', p, 'receivers', rec)
        for o, q, rq in out: print('   receiver-first order', o, 'picks', q, 'own:', rq, '| second:', I2.check(q))
        print('   RF (every form):', all(rq != 'OC1 fails' for o, q, rq in out), '| RF-exists:', any(rq != 'OC1 fails' for o, q, rq in out))
