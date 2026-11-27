"""RF (rf_lib.py) on the known k >= 5 one-chain failures: the 13 witness profiles of ksens's kcegar run at n = 3, k = 5
(results/k4_ksens/kcegar_k5_n3_D1.log on main, read here as data), RD5 (k4/ksens/refute_rd_k5.py), the n = 4, k = 5
instance of attempts/kgen-n4-oc1.md, and any witness of kcegar_k6_n3_D2.log with a D = 1 failure.  For each: every
order's maximum-matching starts, OC1 (own checker, rf_lib) and the second checker (k4/sdc/oc1_mc2_rand.Inst.check,
main, imported read-only via MAINWT); at every failing start the receivers and every receiver-first maximum-matching
order.

    MAINWT=<checkout of main> python3 rf_known.py"""
import sys, os, json, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rf_lib import Inst
MW = os.environ['MAINWT']; sys.path.insert(0, os.path.join(MW, 'k4', 'sdc'))
from oc1_mc2_rand import Inst as Inst2

items = []
for fn in ('kcegar_k5_n3_D1.log', 'kcegar_k6_n3_D2.log', 'kcegar_k5_D2.log'):
    p = os.path.join(MW, 'results', 'k4_ksens', fn)
    if not os.path.exists(p): continue
    for line in open(p):
        if line.startswith('{') and '"FAIL"' in line:
            d = json.loads(line)
            if d.get('D') == 1 and 'recheck' in d: items.append((fn + ':' + d['name'], d['sets'], d['recheck']['vals']))
items.append(('RD5', [[0, 3, 4, 5, 1], [1, 2, 3], [1, 3, 4, 2], [0, 2, 6, 5]], [[26, 44, 24, 33, 57], [12, 11, 6], [9, 6, 1, 8], [36, 53, 4, 47]]))
v = [[34, 0, 0, 0, 38, 35, 37, 33], [0, 10, 5, 0, 0, 4, 2, 0], [0, 2, 0, 0, 3, 0, 1, 0], [52, 54, 53, 4, 0, 0, 0, 51]]
S = [[g for g in range(8) if r[g] > 0] for r in v]; items.append(('kgen-n4-k5 (not balanced)', S, [[r[g] for g in s] for r, s in zip(v, S)]))

if __name__ == '__main__':
    print('$ MAINWT=<main> python3 kgen/rf/rf_known.py'); T = collections.Counter()
    for name, sets, vals in items:
        I = Inst(sets, vals); I2 = Inst2(sets, vals); n = I.n; N = I.nu(); res = {}
        for o in itertools.permutations(range(n)):
            p = I.sd(o)
            if p in res or sum(x is not None for x in p) != N: continue
            r = I.oc1(p); r2 = I2.check(p); res[p] = r
            T['max starts'] += 1; T['checkers agree on OC1'] += ((r == 'OC1 fails') == (r2 == 'OC1 fails'))
        fails = [p for p, r in res.items() if r == 'OC1 fails']
        print('%s: k = %d, n = %d, nu = %d, %d max-matching pick vectors, %d fail OC1' % (name, max(map(len, sets)), n, N, len(res), len(fails)))
        for p in fails:
            rec, out, nonmax = I.rf(p, N)
            bad = [(o, q) for o, q, r in out if r == 'OC1 fails']; bad2 = [(o, q) for o, q, r in out if I2.check(q) == 'OC1 fails']
            T['failing starts'] += 1; T['RF holds (own)'] += not bad; T['RF holds (second checker)'] += not bad2
            print('   failing start %s: receivers %s; %d receiver-first max orders (%d non-max): %s; RF %s / second checker %s'
                  % (p, rec, len(out), nonmax, dict(collections.Counter(r for o, q, r in out)), 'holds' if not bad else 'FAILS %s' % bad, 'holds' if not bad2 else 'FAILS'))
    for k in sorted(T): print(T[k], k)
