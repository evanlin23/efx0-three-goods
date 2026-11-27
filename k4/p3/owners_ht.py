"""On H_t (k4/c4.md section 7, p = 4) and its p = 3 analogues (k4/p3/ht3.py): do the index-order serial-dictatorship
picks extend to an EFX0 allocation with at most B bundles of three or more goods (B = 1, 2)?
    python3 k4/p3/owners_ht.py T1,T2,...
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
from p3lib import *
import c4_chain, ht3

def test(name, sets, vals, m):
    I = Inst(sets, vals, m, name); C = Complete(I)
    pk = sd(I, range(I.n)); fixed = {g: i for i, g in enumerate(pk) if g is not None}
    res = []
    for B in (1, 2):
        own = C.solve(fixed=fixed, extra=C.big_bound(B))
        ok = own is not None and efx0(I, bundles(I, own))
        res.append(f'<= {B} big: {"yes" if own else "no"}' + (f' (raw EFX0 {ok})' if own else ''))
    print(f'{name}: n = {I.n}, m = {m}, p = {I.p()}; index-SD picks extend with ' + '; '.join(res), flush=True)

if __name__ == '__main__':
    for t in [int(x) for x in sys.argv[1].split(',')]:
        test(f'H_{t}', *c4_chain.build(t))
        for var in 'ABC':
            test(f'H3{var}_{t}', *ht3.build(t, var))
