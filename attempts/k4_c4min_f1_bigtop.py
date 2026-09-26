#!/usr/bin/env python3
"""The smallest profile on which no maximum of Psi = (r, Lambda) is completable (f = 1, big-top frozen agents),
attempts/k4-c4min-f1-bigtop.md, replayed by both implementations:
  - k4/c4min_cfg.py (Python): all configurations, the maxima of Psi, (r, Lambda, -t) and Phi' = (-t, r, Lambda, -p),
    and which are completable;
  - k4/c4min_f1.c (C) on the same profile: its counters starfail and rltfail (no completable (r, Lambda)-maximum;
    a non-completable (r, Lambda, -t)-maximum) and phi1fail.
For n = 2 the C run on every strict profile (results/k4_c4min_f1_n3.log, first FILE line) has starfail 0, so n = 3
is the smallest n.
usage: python3 attempts/k4_c4min_f1_bigtop.py"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4'))
from c4min_lib import Profile
from c4min_cfg import keys, configs
from c4min_f1 import r_of, lam_of, t_of, p_of, xtype, frozen_of
from c4min_f1_run import binary

SETS = [[0, 2, 6, 7], [1, 4, 6, 7], [3, 5, 6, 7]]
VALS = [{0: 3, 2: 6, 6: 10, 7: 2}, {1: 3, 4: 4, 6: 8, 7: 2}, {3: 3, 5: 4, 6: 8, 7: 2}]
M = 8


def main():
    ok = True
    pr = Profile(VALS, M)
    f, ks = keys(pr)
    cfs = [c for NA, phi in ks for c in configs(pr, NA, phi)]
    comp = [bool(c.owners()) for c in cfs]
    print(f'profile {VALS} (core 46 of results/k4_certs_3.json.gz), m = {M}: f = {f}, omega = {f - (2 * pr.n - M)}, '
          f'{len(cfs)} configurations, {sum(comp)} completable')
    print('  types:', [xtype(pr, i, None) for i in range(pr.n)])
    for name, key in [('Psi = (r, Lambda)', lambda c: (r_of(c), lam_of(c))),
                      ('(r, Lambda, -t)', lambda c: (r_of(c), lam_of(c), -t_of(c))),
                      ('(r, Lambda, -t, -p)', lambda c: (r_of(c), lam_of(c), -t_of(c), -p_of(c))),
                      ("Phi' = (-t, r, Lambda, -p)", lambda c: (-t_of(c), r_of(c), lam_of(c), -p_of(c)))]:
        K = [key(c) for c in cfs]; mx = max(K)
        mxs = [a for a in range(len(cfs)) if K[a] == mx]
        nc = sum(comp[a] for a in mxs)
        print(f'  {name}: {len(mxs)} maxima, {nc} completable')
        for a in mxs:
            c = cfs[a]
            print(f'    frozen {frozen_of(c)}, pairs {dict((i, sorted(q)) for i, q in c.Q.items())}, pool {sorted(c.L)}, completable {comp[a]}')
        ok &= (nc == 0) if name != "Phi' = (-t, r, Lambda, -p)" else (nc == len(mxs))
    inp = f'{pr.n} {M}\n' + ''.join(f'{len(S)} ' + ' '.join(map(str, S)) + ' 1\n' + ' '.join(str(v[g]) for g in S) + '\n' for S, v in zip(SETS, VALS)) + '0 1\n'
    out = subprocess.run([binary()], input=inp, capture_output=True, text=True, check=True).stdout
    w = out.split(); res = dict(zip(w[1::2], w[2::2]))
    print(f"  k4/c4min_f1.c: starfail {res['starfail']}, rltfail {res['rltfail']}, phi1fail {res['phi1fail']}")
    ok &= res['starfail'] == '1' and res['rltfail'] == '1' and res['phi1fail'] == '0'
    print('CONFIRMED' if ok else 'NOT CONFIRMED')


if __name__ == '__main__':
    main()
