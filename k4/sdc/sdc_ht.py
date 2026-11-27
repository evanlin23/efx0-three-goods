"""SD-C and SD-C-R1 on the cores H_t (k4/c4.md §7, built by k4/adaptive_H.py) and HH_t (two copies of H_t sharing one
good, k4/lemmam_bt.md §3; the instance on which Lemma M and rule F with one rotation fail).

    python3 k4/sdc/sdc_ht.py"""
import os, sys, time
import _paths
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4'))
import adaptive_H as AH
from sdsat import solve
from sdsat_r1 import solve_r1


def build_hh(t):                       # as k4/lemmam_bt_hh.py build_hh
    S, V, m = AH.build(t)
    u = t + 1
    SA = [list(s) for s in S]
    SB = [[g + m for g in s] for s in S]
    SB[0] = [u if g == u + m else g for g in SB[0]]
    sets = [SA[0], SB[0]] + SA[1:] + SB[1:]
    vals = [V[0], V[0]] + V[1:] + V[1:]
    used = sorted(set(g for s in sets for g in s))
    ren = {g: i for i, g in enumerate(used)}
    return [[ren[g] for g in s] for s in sets], vals, len(used)


if __name__ == '__main__':
    print('$ python3 k4/sdc/sdc_ht.py')
    for name in ['H2', 'H3', 'H4', 'H5', 'HH3', 'HH4']:
        t = int(name[-1])
        sets, vals, m = AH.build(t) if name[0:2] != 'HH' else build_hh(t)
        t0 = time.time(); ok, w = solve(sets, vals, m); ok1 = solve_r1(sets, vals, m)
        print(f'{name}: n = {len(sets)}, m = {m}, SD-C {ok}, SD-C-R1 {ok1}, time {time.time() - t0:.1f} s')
        if ok: print('   order', w[0]); print('   picks', w[1])
