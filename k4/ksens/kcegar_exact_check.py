"""Validation of kcegar's exact grid mode (grid_exact=True; k4/ksens.md §8).  In exact mode the grid only proposes
points and cores: every cut is confirmed by the exact LP of ratlp.py, and bits the grid cannot realize but the LP can
get the LP's point.  So the verdict must not depend on the grid, and must equal the verdict over every strict profile.

1. Five goods, with an INCOMPLETE grid (types5_B18: 145 of the 516 types per ranking): exact mode must agree with the
   type lists (every strict type), on instances where one chain fails and where it holds.  Plain grid mode on the same
   incomplete grid is shown too: it may certify where the type lists fail (it sees only a subset).
2. Six goods: exact mode on two different grids (B = 32 and B = 48) and the LP route (lp_min = 6, no grid) must agree.
Exact mode is the second version (grid_exact=True: points found by the LP join the grid, core verdicts are cached);
the first (grid_exact='v1') gave the same verdicts on these cases (results/k4_ksens/kcegar_exact_check_v1.log).

    python3 k4/ksens/kcegar_exact_check.py"""
import time
import _paths
import kcegar, refute_rd_k5 as R
from refute_oc1_k5_n3 import SETS as N3

G5 = '../../results/k4_ksens/types5_B18.json.gz'
G6 = {32: '../../results/k4_ksens/types6_B32.json.gz', 48: '../../results/k4_ksens/types6_B48.json.gz'}


def run(S, D, **kw):
    t = time.time(); C = kcegar.Cegar(S, D=D, **kw); r = C.run()[0]
    out = (r, C.iters, dict(C.gstats), round(time.time() - t, 1)); C.close(); return out


if __name__ == '__main__':
    print('$ python3 k4/ksens/kcegar_exact_check.py', flush=True); agree = tot = 0
    five = [('RD5', R.SETS), ('N3K5', N3), ('n3_m7_15 (k = 5)', [[0, 1, 2, 5, 6], [2, 3, 4, 5, 6], [3, 4, 5, 6]]),
            ('n3_m6 holds (k = 5)', [[0, 1, 2, 3, 4], [2, 3, 4], [3, 4]])]
    for name, S in five:
        for D in (1, 2):
            a = run(S, D); b = run(S, D, grid6=G5, grid_exact=True); c = run(S, D, grid6=G5)
            tot += 1; ok = a[0] == b[0]; agree += ok
            print('%s D=%d: type lists %s; exact mode on the B=18 grid %s (%d iterations, %s, %.1f s); plain grid mode '
                  'on it %s; %s' % (name, D, a[0], b[0], b[1], b[2], b[3], c[0], 'agree' if ok else 'DISAGREE'), flush=True)
    six = [[[0, 1, 2, 3, 4, 5], [3, 4, 5], [3, 4, 5]], [[0, 1, 2, 3, 4, 5], [2, 3, 5], [4, 5]],
           [[0, 1, 2, 3, 4, 5], [2, 3, 4, 5], [5]], [[0, 1, 2, 3, 4, 5], [2, 3], [4, 5]]]
    for S in six:
        for D in (1, 2):
            x = run(S, D, grid6=G6[32], grid_exact=True); y = run(S, D, grid6=G6[48], grid_exact=True); z = run(S, D)
            tot += 1; ok = x[0] == y[0] == z[0]; agree += ok
            print('k = 6 %s D=%d: exact mode B=32 %s (%d it, %s, %.1f s); exact mode B=48 %s (%d it, %s, %.1f s); LP route '
                  '%s (%.1f s); %s' % (S, D, x[0], x[1], x[2], x[3], y[0], y[1], y[2], y[3], z[0], z[3],
                                       'agree' if ok else 'DISAGREE'), flush=True)
    print('agree on %d of %d' % (agree, tot))
