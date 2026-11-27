"""Validation of kcegar's LP route (k4/ksens.md §8): agents with >= lp_min goods use the exact LP (ratlp.realize_fast)
instead of their type list; on hypergraphs where both routes apply, the verdicts must agree.

    python3 k4/ksens/kcegar_lp_check.py"""
import time
import _paths
import kcegar, refute_rd_k5 as R
from refute_oc1_k5_n3 import SETS as N3
from refute_oc1max_k4 import CEX

if __name__ == '__main__':
    print('$ python3 k4/ksens/kcegar_lp_check.py', flush=True); agree = tot = 0
    for name, S, lp in [('RD5', R.SETS, 5), ('N3K5', N3, 5), ('cex1 (k = 4)', CEX[0][0], 4), ('cex2 (k = 4)', CEX[1][0], 4)]:
        for D in (1, 2):
            t = time.time(); a = kcegar.Cegar(S, D=D); ra = a.run()[0]; ia = a.iters; a.close(); ta = time.time() - t
            t = time.time(); b = kcegar.Cegar(S, D=D, lp_min=lp); rb = b.run()[0]; ib = b.iters; lc = b.lpcalls; b.close()
            tb = time.time() - t; tot += 1; agree += ra == rb
            print('%s D=%d: type lists %s (%d iterations, %.1f s); LP route for agents with >= %d goods %s (%d iterations, '
                  '%d LP calls, %.1f s); %s' % (name, D, ra, ia, ta, lp, rb, ib, lc, tb, 'agree' if ra == rb else 'DISAGREE'), flush=True)
    print('agree on %d of %d' % (agree, tot))
