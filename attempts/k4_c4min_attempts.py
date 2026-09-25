#!/usr/bin/env python3
"""Failing instances of the potentials of attempts/k4-c4min-potentials.md, replayed by both implementations:
k4/c4min.c (one profile) and the independent Python implementation k4/c4min_cfg.py (configurations, owners with the
unfreezing clause, features from the definitions). For each claim it also runs k4/c4min.c on every strict profile of
every core with n = 2, to show that n = 3 is the smallest n (the m of each instance is not claimed to be smallest).

usage: python3 attempts/k4_c4min_attempts.py            (about a minute)"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4'))
from c4min_run import binary
from c4min_lib import Profile, v
from c4min_cfg import keys, configs

# (label, c4min options, potential, kind, n, m, sets, profile). kind 'every': some maximum of the potential is not
# completable; 'pareto': some Pareto-maximal configuration is not completable; 'nounf': some configuration is
# completable with the unfreezing clause, none without it.
CLAIMS = [
    ('robust count alone, f = 0', ['-f', '0'], '9', 'every', 3, 7, [[0, 2, 5, 6], [1, 4, 5, 6], [3, 4, 5, 6]],
     [{0: 10, 2: 2, 5: 6, 6: 7}, {1: 2, 4: 7, 5: 4, 6: 8}, {3: 3, 4: 7, 5: 6, 6: 5}]),
    ('pool-optimality alone, f = 0', ['-f', '0'], '20', 'every', 2, 5, [[0, 2, 3, 4], [1, 2, 3, 4]],
     [{0: 1, 2: 4, 3: 6, 4: 8}, {1: 2, 2: 4, 3: 5, 4: 8}]),
    ('(r, Lambda), f = 1', ['-f', '1'], '9,16', 'every', 3, 8, [[0, 2, 6, 7], [1, 4, 6, 7], [3, 5, 6, 7]],
     [{0: 3, 2: 6, 6: 10, 7: 2}, {1: 3, 4: 6, 6: 10, 7: 2}, {3: 2, 5: 3, 6: 10, 7: 6}]),
    ('Lambda alone, f = 1', ['-f', '1'], '16', 'every', 3, 8, [[0, 2, 6, 7], [1, 4, 6, 7], [3, 5, 6, 7]],
     [{0: 3, 2: 6, 6: 10, 7: 2}, {1: 3, 4: 6, 6: 10, 7: 2}, {3: 2, 5: 3, 6: 10, 7: 6}]),
    ('(-t, Lambda), f = 2', ['-f', '2'], '8,16', 'every', 3, 6, [[0, 1, 2, 5], [2, 3, 4, 5], [3, 4, 5]],
     [{0: 4, 1: 3, 2: 2, 5: 8}, {2: 4, 3: 1, 4: 8, 5: 6}, {3: 2, 4: 4, 5: 3}]),
    ('Pareto-maximality, f = 1', ['-f', '1', '-Q'], '16', 'pareto', 3, 7, [[0, 1, 2, 3], [2, 4, 5, 6], [3, 4, 5, 6]],
     [{0: 3, 1: 2, 2: 10, 3: 6}, {2: 8, 4: 4, 5: 2, 6: 3}, {3: 3, 4: 2, 5: 6, 6: 10}]),
    ('configurations without the unfreezing clause', ['-U0'], '9,16', 'nounf', 2, 6, [[0, 1, 4, 5], [2, 3, 4, 5]],
     [{0: 6, 1: 3, 4: 10, 5: 2}, {2: 4, 3: 3, 4: 8, 5: 2}]),
    ('Conjecture Phi = (-t, r, Lambda), f = 2', ['-f', '2'], '8,9,16', 'every', 4, 8, [[0, 2, 4, 7], [1, 5, 6, 7], [3, 5, 6, 7], [4, 5, 6, 7]],
     [{0: 3, 2: 4, 4: 2, 7: 8}, {1: 3, 5: 6, 6: 10, 7: 2}, {3: 4, 5: 8, 6: 3, 7: 6}, {4: 4, 5: 8, 6: 6, 7: 5}]),
    ('(-t, leximin), f = 2', ['-f', '2'], '8,17', 'every', 4, 7, [[0, 1, 3, 6], [2, 3, 4], [2, 5, 6], [4, 5, 6]],
     [{0: 2, 1: 3, 3: 6, 6: 10}, {2: 3, 3: 2, 4: 4}, {2: 3, 5: 2, 6: 4}, {4: 4, 5: 3, 6: 2}]),
]
# the n = 4 instances: n = 3 is excluded by the exhaustive run of results/k4_c4min_phi_n3.log (0 failures of both)


def c_input(n, m, sets, vals):
    lines = [f'{n} {m}']
    for S, val in zip(sets, vals):
        lines.append(f'{len(S)} ' + ' '.join(map(str, S)) + ' 1')
        lines.append(' '.join(str(val[g]) for g in S))
    lines.append('0 1')
    return '\n'.join(lines) + '\n'


def run_c(opts, pot, inp):
    r = subprocess.run([binary()] + opts + ['-p', pot], input=inp, capture_output=True, text=True, check=True)
    res = {}
    for line in r.stdout.splitlines():
        w = line.split()
        if line.startswith('RESULT'): res.update(zip(w[1::2], map(int, w[2::2])))
        elif line.startswith('PHI'): res['every_fail'] = int(w[3]); res['some_fail'] = int(w[5])
    return res


def run_n2(opts, pot, kind):
    extra = ['-X'] if kind == 'nounf' else []
    r = subprocess.run([sys.executable, os.path.join(ROOT, 'k4', 'c4min_run.py'), os.path.join(ROOT, 'results', 'k4_certs_2.json.gz'),
                        '--jobs=2'] + opts + extra + ['-p', pot], capture_output=True, text=True, check=True)
    fl = [l for l in r.stdout.splitlines() if l.startswith('FILE')][0].split()
    tot = dict(zip(fl[2::2], fl[3::2]))
    ph = [l for l in r.stdout.splitlines() if 'every-max fails' in l][0].split()
    if kind == 'nounf': return int(tot['none']), 'profiles with no completable configuration (unfreezing off)'
    if kind == 'pareto': return int(tot['paretoevery']), 'profiles with a Pareto-maximum that is not completable'
    return int(ph[ph.index('every-max') + 2]), 'profiles where some maximum is not completable'


def feat(c, pot):
    n = c.pr.n
    t = -sum(c.pool_threat(x) for x in range(n) if c.phi[x] is not None)
    r = sum(c.robust(i) for i in range(n)); lam = sum(c.level(i) for i in range(n))
    lev = sorted(c.level(i) for i in range(n))
    return {'9': (r,), '16': (lam,), '9,16': (r, lam), '8,16': (t, lam), '20': (int(c.pool_optimal()),),
            '8,9,16': (t, r, lam), '8,17': (t, tuple(lev)),
            '8,9,16,3': (t, r, lam, -sum(len(c.L & c.U[x]) for x in range(n) if c.phi[x] is not None))}[pot]


def replay_py(pot, kind, n, m, vals):
    pr = Profile(vals, m)
    f, ks = keys(pr)
    cfs = [c for NA, phi in ks for c in configs(pr, NA, phi)]
    comp = [bool(c.owners()) for c in cfs]
    if kind == 'nounf':
        c0 = [bool(c.owners(unfreeze=False)) for c in cfs]
        return f'f = {f}, {len(cfs)} configurations, {sum(comp)} completable, {sum(c0)} without unfreezing', any(comp) and not any(c0)
    if kind == 'pareto':
        vv = [[v(pr.vals[i], c.H(i)) for i in range(n)] for c in cfs]
        par = [a for a in range(len(cfs)) if not any(all(vv[b][i] >= vv[a][i] for i in range(n)) and vv[b] != vv[a] for b in range(len(cfs)))]
        bad = [a for a in par if not comp[a]]
        return f'f = {f}, {len(cfs)} configurations, {len(par)} Pareto-maximal, {len(bad)} of them not completable, {sum(comp)} completable in all', bool(bad) and any(comp)
    K = [feat(c, pot) for c in cfs]
    mx = max(K)
    bad = [a for a in range(len(cfs)) if K[a] == mx and not comp[a]]
    return f'f = {f}, {len(cfs)} configurations, {sum(1 for k in K if k == mx)} maxima, {len(bad)} of them not completable, {sum(comp)} completable in all', bool(bad) and any(comp)


def main():
    allok = True
    for label, opts, pot, kind, n, m, sets, vals in CLAIMS:
        print(f'{label}: n = {n}, m = {m}, sets {sets}, values {vals}')
        res = run_c(opts, pot, c_input(n, m, sets, vals))
        if kind == 'nounf':
            res2 = run_c(opts[1:], pot, c_input(n, m, sets, vals))
            okc = res['none'] == 1 and res2['none'] == 0
            print(f'   c4min.c: without unfreezing none completable = {res["none"]}; with it = {res2["none"]}: {"confirmed" if okc else "NOT CONFIRMED"}')
        elif kind == 'pareto':
            okc = res['paretoevery'] == 1 and res['none'] == 0
            print(f'   c4min.c: Pareto every-form fails = {res["paretoevery"]}, profile without completable configuration = {res["none"]}: {"confirmed" if okc else "NOT CONFIRMED"}')
        else:
            okc = res['every_fail'] == 1 and res['none'] == 0
            print(f'   c4min.c: every-form fails = {res["every_fail"]}, profile without completable configuration = {res["none"]}: {"confirmed" if okc else "NOT CONFIRMED"}')
        msg, okp = replay_py(pot, kind, n, m, vals)
        print(f'   c4min_cfg.py: {msg}: {"confirmed" if okp else "NOT CONFIRMED"}')
        if n == 4:
            print('   n <= 3: every strict profile with f >= 1 has 0 failures of this potential (results/k4_c4min_phi_n3.log): n = 4 is the smallest n')
            if pot == '8,9,16':
                r2 = run_c(opts, '8,9,16,3', c_input(n, m, sets, vals))
                msg2, bad2 = replay_py('8,9,16,3', 'every', n, m, vals)
                ok2 = r2['every_fail'] == 0 and not bad2
                print(f"   refinement Phi' = (-t, r, Lambda, -p): c4min.c every-form fails = {r2['every_fail']}; c4min_cfg.py: {msg2}: {'every maximum completable' if ok2 else 'NOT CONFIRMED'}")
                allok &= ok2
        if n == 3:
            k, what = run_n2(opts, pot, kind)
            print(f'   n = 2, every strict profile of every core (k4/c4min.c): {k} {what}: n = 3 is the smallest n' if k == 0 else f'   n = 2: {k} {what}')
            allok &= k == 0
        allok &= okc and okp
        sys.stdout.flush()
    print('ALL CONFIRMED' if allok else 'SOME NOT CONFIRMED')


if __name__ == '__main__':
    main()
