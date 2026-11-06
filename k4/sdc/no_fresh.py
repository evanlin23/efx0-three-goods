"""Fresh owners in Conjecture NO: o is *fresh* in NO(o) if no other agent picks a good of o.  Does a fresh owner always
work, and does some owner work that is fresh?  Also counts instances with no fresh owner.

    python3 k4/sdc/no_fresh.py screen|suite"""
import sys, collections
import _paths
from sdclib import Enc
from sdc_orders import completable
from sdc_need import instances
from sdc_need_owner import order_with_last

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); ex = []
    print('$ python3 k4/sdc/no_fresh.py', *sys.argv[1:])
    for name, sets, vals, m in instances(src):
        E = Enc(sets, vals, m); C['instances'] += 1; fresh_any = False; fresh_work = False
        for o in range(E.n):
            Y, order = order_with_last(E, 'need2', False, o)
            fresh = all(Y[j] not in E.R[o] for j in range(E.n) if j != o)
            ok = completable(E, Y)
            if fresh:
                fresh_any = True; fresh_work |= ok
                C['fresh owners'] += 1; C['fresh owners that work'] += ok
                if not ok and len(ex) < 3: ex.append((name, o))
        C['instances with a fresh owner'] += fresh_any; C['instances where a fresh owner works'] += fresh_work
    for k in sorted(C, key=str): print(k, C[k])
    for e in ex: print('FRESH OWNER FAILS', e)
