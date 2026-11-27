"""Serial-dictatorship outcomes versus Pareto-optimal matchings (k4/sdc.md §28).  In house allocation with strict
preferences, the outcomes of serial dictatorship over all orders are exactly the Pareto-optimal matchings
(Abdulkadiroglu and Sonmez 1998 [unverified here]; agents may stay unmatched when their relevant goods are gone).
Checked by enumeration: per instance, the set of SD pick vectors over all orders equals the set of matchings whose
value vectors are Pareto-maximal among matchings.  So value domination of every order's picks (vdom.py) is the same
statement as value domination of every matching (mdom.py).

    python3 k4/sdc/sd_po.py screen|suite|special"""
import sys, itertools, collections
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from nof_var import SPECIAL


def all_matchings(E):
    out = []
    def rec(i, used, Y):
        if i == E.n: out.append(tuple(Y)); return
        rec(i + 1, used, Y + [None])
        for g in E.R[i]:
            if g not in used: rec(i + 1, used | {g}, Y + [g])
    rec(0, frozenset(), [])
    return out


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/sdc/sd_po.py', *sys.argv[1:])
    items = SPECIAL if src == 'special' else instances(src)
    for name, sets, vals, m in items:
        if len(sets) > 6: continue
        E = Enc(sets, vals, m); C['instances'] += 1
        sdset = set(tuple(sd(E, list(o))[0]) for o in itertools.permutations(range(E.n)))
        ms = all_matchings(E)
        val = lambda Y: tuple(E.v[i][Y[i]] if Y[i] is not None else 0 for i in range(E.n))
        vs = {Y: val(Y) for Y in ms}
        po = set(Y for Y in ms if not any(all(a >= b for a, b in zip(vs[Z], vs[Y])) and vs[Z] != vs[Y] for Z in ms))
        same = sdset == po
        C['SD outcomes = Pareto-optimal matchings'] += same
        if not same: print('DIFFER', name, sorted(sdset ^ po)[:4])
    for k in sorted(C): print(k, C[k])
