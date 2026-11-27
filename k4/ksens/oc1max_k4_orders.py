"""Order classes on the 11 k = 4 counterexamples to OC1^max (refute_oc1max_k4.py; k4/ksens.md §5): for each instance,
how many distinct starts (every order), R1-priority starts (r1_pw.sd_r1, LB's Phase 1) and the neediest-first starts
(k4/sdc/nof_var.order: need2, need1, needall, plain and R1) fail OC1 (one chain, one-absorber completion; ocsat).

    python3 k4/ksens/oc1max_k4_orders.py"""
import sys, json, itertools
import _paths
sys.path.insert(0, _paths.SDC)
import ocsat
from sdclib import Enc
from nof_var import order as nf_order
from r1_pw import sd_r1
from refute_oc1max_k4 import CEX

if __name__ == '__main__':
    print('$ python3 k4/ksens/oc1max_k4_orders.py'); tot = {'r1 bad': 0, 'nf bad': 0}
    for c, (S, V, P) in enumerate(CEX):
        n = len(S); m = 1 + max(max(s) for s in S); O = ocsat.OC(S, V, m); E = Enc(S, V, m)
        bad = lambda Y: not O.holds(ocsat.bases_of(Y, n), chain='any', A=1)
        st = ocsat.starts(S, V, m); r1 = {}
        for o in itertools.permutations(range(n)): r1.setdefault(tuple(sd_r1(S, V, o, m)), o)
        nf = {}
        for kind in ('need2', 'need1', 'needall'):
            for flag in (False, True):
                Y, done = nf_order(E, kind, flag); nf['%s%s' % (kind, ' R1' if flag else '')] = (tuple(Y), bad(Y))
        rb = sum(1 for Y in r1 if bad(Y)); nb = sum(1 for _, b in nf.values() if b)
        tot['r1 bad'] += rb > 0; tot['nf bad'] += nb > 0
        print('#%d every order: OC1 fails on %d of %d starts (the failing picks %s); R1-priority: %d of %d fail; '
              'neediest-first: %s' % (c + 1, sum(1 for Y in st if bad(Y)), len(st), P, rb, len(r1),
              json.dumps({k: ('FAIL' if b else 'ok') for k, (Y, b) in nf.items()})), flush=True)
        O.close()
    print('instances where some R1-priority start fails: %d of 11; where some neediest-first start fails: %d of 11' % (
        tot['r1 bad'], tot['nf bad']))
