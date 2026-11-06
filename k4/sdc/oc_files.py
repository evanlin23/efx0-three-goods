"""OC and OC1 on the gadget families (k4/sdc.md §29): H_t (k4/c4.md §7; LB4r with a fixed insertion order needs
unboundedly many rotations, K4.C4.R) and HH_t (rule F fails, K4.LMBT.COR).  Orders tried: the index order, its reverse,
the neediest-first order, and S random orders.  For each: does the start extend (free completion / one absorber), and
otherwise does one improving chain make it extend?

    python3 k4/sdc/oc_files.py [S]"""
import sys, os, json, random, collections, time
import _paths
import de_free as DF
from sdclib import Enc
from sdc_orders import sd
from sdc_need import rule_order
from oc_absorb import extends_A

DF.CHAIN_ONLY = True

if __name__ == '__main__':
    Sn = int(sys.argv[1]) if len(sys.argv) > 1 else 5; t0 = time.time(); C = collections.Counter()
    print('$ python3 k4/sdc/oc_files.py', *sys.argv[1:], flush=True)
    sys.path.insert(0, os.path.join(_paths.ROOT, 'k4'))
    import adaptive_H as AH
    from sdc_ht import build_hh
    items = [('H%d' % t,) + tuple(AH.build(t)) for t in (1, 2, 3, 4, 5)] + [('HH%d' % t,) + tuple(build_hh(t)) for t in (3, 4)]
    for name, sets, vals, m in items:
        n = len(sets); E = Enc(sets, vals, m); rng = random.Random(len(name) * 7 + n)
        orders = [('index', list(range(n))), ('reverse', list(range(n))[::-1]), ('neediest-first', rule_order(E, 'need2', False)[1])]
        orders += [('random%d' % k, rng.sample(range(n), n)) for k in range(Sn)]
        for oname, o in orders:
            Y = sd(E, list(o))[0]
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            base = tuple(base)
            r = {}
            for comp, test in (('free', lambda b: DF.extends(E, b)), ('one absorber', lambda b: extends_A(E, b, 1))):
                if test(base): r[comp] = 0
                else:
                    seen = set(); r[comp] = None
                    for b2 in DF.iter_chains(E, base):
                        if b2 in seen: continue
                        seen.add(b2)
                        if test(b2): r[comp] = 1; break
                C['%s: chains needed %s' % (comp, r[comp])] += 1
            print(name, 'n', n, 'm', m, oname, r, 'time %.0f' % (time.time() - t0), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
