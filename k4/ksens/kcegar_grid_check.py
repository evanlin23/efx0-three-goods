"""Validation of kcegar's grid mode (k4/ksens.md §8): with a COMPLETE grid list (five goods, types5_B40.json.gz from
typesk.py; four goods, types4_B16), grid mode must give the same verdicts as the type lists.  The current grid check
(realize_grid) and its first version (realize_grid_ref) must also give the same verdicts and iteration counts.

    python3 k4/ksens/kcegar_grid_check.py"""
import time
import _paths
import kcegar, refute_rd_k5 as R
from refute_oc1_k5_n3 import SETS as N3
from refute_oc1max_k4 import CEX
G5 = '../../results/k4_ksens/types5_B40.json.gz'; G4 = '../../results/k4_ksens/types4_B16.json.gz'

if __name__ == '__main__':
    print('$ python3 k4/ksens/kcegar_grid_check.py', flush=True); agree = tot = 0
    for name, S, g in [('RD5', R.SETS, G5), ('N3K5', N3, G5), ('cex1 (k = 4)', CEX[0][0], G4), ('cex5 (k = 4)', CEX[4][0], G4)]:
        for D in (1, 2):
            t = time.time(); a = kcegar.Cegar(S, D=D); ra = a.run()[0]; a.close(); ta = time.time() - t
            t = time.time(); b = kcegar.Cegar(S, D=D, grid6=g); rb = b.run()[0]; ib = b.iters; b.close(); tb = time.time() - t
            t = time.time(); c = kcegar.Cegar(S, D=D, grid6=g, grid_fast=False); rc = c.run()[0]; ic = c.iters; c.close(); tc = time.time() - t
            tot += 1; ok = ra == rb == rc and ib == ic; agree += ok
            print('%s D=%d: type lists %s (%.1f s); grid mode %s (%d iterations, %.1f s); first grid version %s (%d '
                  'iterations, %.1f s); %s' % (name, D, ra, ta, rb, ib, tb, rc, ic, tc, 'agree' if ok else 'DISAGREE'), flush=True)
    G6 = '../../results/k4_ksens/types6_B48.json.gz'          # six goods: no type list; the two grid versions only
    for S in ([[0, 1, 2, 3, 4, 5], [3, 4, 5], [3, 4, 5]], [[0, 1, 2, 3, 4, 5], [2, 3, 5], [4, 5]]):
        for D in (1, 2):
            t = time.time(); b = kcegar.Cegar(S, D=D, grid6=G6); rb = b.run()[0]; ib, cb = b.iters, b.cuts; b.close(); tb = time.time() - t
            t = time.time(); c = kcegar.Cegar(S, D=D, grid6=G6, grid_fast=False); rc = c.run()[0]; ic, cc = c.iters, c.cuts; c.close(); tc = time.time() - t
            tot += 1; ok = rb == rc and (ib, cb) == (ic, cc); agree += ok
            print('k = 6 %s D=%d: grid mode %s (%d iterations, %d cuts, %.1f s); first grid version %s (%d iterations, %d '
                  'cuts, %.1f s); %s' % (S, D, rb, ib, cb, tb, rc, ic, cc, tc, 'agree' if ok else 'DISAGREE'), flush=True)
    print('agree on %d of %d' % (agree, tot))
