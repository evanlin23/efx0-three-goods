"""The per-block form of the owner-free count fails (k4/sdc.md §15): a hand-built strict k = 4 core (n = 3, m = 8) whose
plain neediest-first R1 run has a block with one slot place and two threatened agents with disjoint danger goods.
The plain run still extends, through a good shared with the next block.  Prints the run, blocks4j's per-block numbers,
and a brute-force EFX0 completion of the plain picks.

    python3 k4/sdc/blocks_hand.py"""
import itertools
import _paths
from sdclib import Enc
from sdc_need import rule_order
from sdc_orders import completable
import blocks4j as BJ
from blocks4 import blocks_of, min_service, M
from refute_nofl import efx0, extends

# goods: a = 0, w2 = 1, w3 = 2, w4 = 3, y = 4, p = 5, q = 6, s = 7  (values doubled to make every profile strict)
SETS = [[0, 1, 2, 3], [0, 4, 5, 6], [7, 5, 3]]
VALS = [[18, 8, 7, 6], [16, 8, 6, 4], [10, 7, 5]]

if __name__ == '__main__':
    print('$ python3 k4/sdc/blocks_hand.py')
    m = 8; n = 3; E = Enc(SETS, VALS, m)
    Y, pi = rule_order(E, 'need2', True); blk = blocks_of(E, pi, Y)
    print('order', pi, 'picks', Y, 'blocks', blk)
    v = [[0] * m for _ in SETS]
    for i, (S, V) in enumerate(zip(SETS, VALS)):
        for g, x in zip(S, V): v[i][g] = x
    inst = M.Inst(v)
    base = [-1] * m; pick = [-1] * n
    for i, g in enumerate(Y):
        if g is not None: base[g] = i; pick[i] = g
    s = (tuple(base), tuple(pick), (False,) * n); s, ups = M.up_run(inst, s, 'shrink')
    needs = M.all_needs(inst, s); opts, capK = BJ.options_J(inst, s, needs)
    print('upgrades', ups, 'threatened agents and their options', {x: [(k, sorted(S)) for k, S in ox] for x, ox in opts.items()}, 'places', capK)
    for b in sorted(set(blk.values())):
        ob = [(x, ox) for x, ox in opts.items() if blk[x] == b]
        print('block', b, 'places', sum(capK[x] for x in range(n) if blk[x] == b), 'need', min_service(ob))
    val = [dict(zip(SETS[i], VALS[i])) for i in range(n)]
    ok, B = extends(n, m, val, dict(enumerate(Y)))
    print('plain picks extend (brute force):', ok, B, '; SAT:', completable(E, Y))
