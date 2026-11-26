"""Question W (kgen/charity.md §6): S'(sigma, k) with the values of GM4-G cut to three goods (champion: y 8, x 3,
g 6; source: x 6, x' 3, child 10; relays: own rz, child rc).  For sigma = 2 this is the k = 3 counterexample to W with
f = 0; for sigma >= 3 the script reports the stranded state's welfare and the welfare maximum (chlib.welfare_max).

    python3 kgen/charity/w_family_vals.py"""
from stuck_family import build
from chlib import efx0, pool_ok, welfare_max, improve

if __name__ == '__main__':
    print('$ python3 kgen/charity/w_family_vals.py', flush=True)
    G = dict(y=8, x=3, g=6, sx=6, sxp=3, sc=10)
    for k, sigma, rz, rc in ((3, 2, 4, 5), (3, 3, 4, 5), (3, 3, 9, 10), (3, 4, 9, 10), (4, 3, 4, 5), (4, 4, 9, 10)):
        I, X, P, src, ch = build(sigma, k, own=True, vals=dict(G, rz=rz, rc=rc))
        W, p, Y = welfare_max(I)
        print('k %d sigma %d (relay values %d, %d): n %d, stranded state EFX0 with strong charity %s, Pareto maximum %s, '
              'welfare %d; welfare maximum %d with %d unallocated' % (
                  k, sigma, rz, rc, I.n, efx0(I, X) and pool_ok(I, X, P), improve(I, X) is None,
                  sum(I.val(a, X[a]) for a in range(I.n)), W, p), flush=True)
