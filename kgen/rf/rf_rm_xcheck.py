"""Second check of the RM results (rf_rm.py): for the known k >= 5 failures and every FAILSTART instance of the climb
logs, recompute independently -- SD vectors and the matching number nu by brute force over injective assignments, the
rank signatures from the definition, and OC1 with k4/sdc's checker (oc1_mc2_rand.Inst.check, main, read-only via
MAINWT) -- which RM-optimal vectors fail OC1, and whether some RM-optimal vector satisfies OC1.  Also reports whether
the instance is strict and balanced.

    MAINWT=<main> python3 rf_rm_xcheck.py"""
import sys, os, json, glob, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, os.path.join(os.environ['MAINWT'], 'k4', 'sdc'))
from oc1_mc2_rand import Inst as Inst2
from rf_known import items
from rf_run import strict_balanced

if __name__ == '__main__':
    print('$ MAINWT=<main> python3 kgen/rf/rf_rm_xcheck.py')
    insts = list(items); here = os.path.dirname(os.path.abspath(__file__))
    for fn in sorted(glob.glob(os.path.join(here, '..', '..', 'results', 'kgen_rf', 'rf_climb_*.log'))):
        for line in open(fn):
            if line.startswith('FAILSTART '):
                d = json.loads(line.split(' ', 1)[1]); insts.append((os.path.basename(fn) + ':%d' % d['seed'], d['sets'], d['vals']))
    tot = [0, 0, 0]
    for nm, sets, vals in insts:
        I2 = Inst2(sets, vals); n = len(sets); vecs = set(I2.sd(o) for o in itertools.permutations(range(n)))
        N = 0
        for p in itertools.product(*[list(s) + [None] for s in sets]):
            q = [g for g in p if g is not None]
            if len(q) == len(set(q)): N = max(N, len(q))
        mv = [p for p in vecs if sum(g is not None for g in p) == N]
        def sig(p):
            c = [0] * 8
            for i, g in enumerate(p):
                if g is not None: c[sum(1 for x in vals[i] if x > I2.v[i][g])] += 1
            return tuple(c)
        best = max(sig(p) for p in mv); rm = [p for p in mv if sig(p) == best]
        res = {p: I2.check(p) for p in rm}; fail = [p for p in rm if res[p] == 'OC1 fails']
        tot[0] += 1; tot[1] += bool(fail); tot[2] += any(r != 'OC1 fails' for r in res.values())
        print('%-38s k = %d n = %d strict+balanced %s | %d RM-optimal (signature %s), failing %s; some RM-optimal satisfies OC1: %s'
              % (nm, max(map(len, sets)), n, all(strict_balanced(v) for v in vals), len(rm), best[:max(map(len, sets))], fail or '-', any(r != 'OC1 fails' for r in res.values())))
    print('instances %d; some RM-optimal vector fails OC1: %d; some RM-optimal vector satisfies OC1: %d' % tuple(tot))
