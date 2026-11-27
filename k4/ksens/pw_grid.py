"""One chain on the clean PW(f, W, r) family (k4/ksens.md §7): for which (f, W, r) do the natural order's picks
(x_1..x_f, w_1..w_W) have no completion after one improving chain?  Clean values: x_j values p_j at 20 and the pool at
19, 18, ... (every pair above 20 needs r <= 10); wanters value p_1, ..., p_f at 2f, ..., 2 and q at 1.

    python3 k4/ksens/pw_grid.py FMAX WMAX RMAX"""
import sys
import _paths
import ocsat, fam_ladder

if __name__ == '__main__':
    FM, WM, RM = map(int, sys.argv[1:4])
    print('$ python3 k4/ksens/pw_grid.py', *sys.argv[1:], flush=True)
    for f in range(2, FM + 1):
        for W in range(1, WM + 1):
            row = []
            for r in range(2, RM + 1):
                sets, vals, m = fam_ladder.clean(f, W, r); n = f + W
                O = ocsat.OC(sets, vals, m); b = ocsat.bases_of(ocsat.sd(sets, vals, tuple(range(n)), m), n)
                one = O.holds(b, chain='any'); one1 = O.holds(b, chain='any', A=1); O.close()
                row.append('r=%d:%s' % (r, ('ok' if one1 else ('FAIL' if not one else 'fail1'))))
            print('f %d W %d  ' % (f, W) + '  '.join(row), flush=True)
