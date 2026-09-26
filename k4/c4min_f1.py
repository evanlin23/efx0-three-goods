#!/usr/bin/env python3
"""c4min_f1: analyses for k4/c4min_f1.md (C4min with one frozen agent), on the independent Python implementation
k4/c4min_cfg.py. Profiles with fewest frozen agents f = 1 and omega >= 1 only.

The frozen agent x holds g = its top (k4/c4min_f1.md §1). Its type: 3 (three goods), 4 (four goods, a < b + c) or
BT (four goods, a > b + c: big-top, as in PR #46's k4/hall.md §5).

  --maxima   : for each potential, whether every maximum is completable, and the structure at the maxima (t = 0,
               pool-optimal), per type of x.
  --moves    : for every configuration without a valid owner and every potential: the smallest number of agents whose
               holdings change in some configuration of higher potential (1, 2, 3, ...), per type of x.
usage: python3 k4/c4min_f1.py FILE (--maxima|--moves) [--rand=N] [--seed=S] [--pots=a,b,...] [--ex=K]"""
import collections, itertools, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c4min_lib import load_cores, profiles, Profile, v, threatened, needs, fmt_profile
from c4min_cfg import keys, configs, Config, FOREIGN


def xtype(pr, x, g):
    val = pr.vals[x]
    if len(val) == 3: return '3'
    a, b, c, d = sorted(val.values(), reverse=True)
    return 'BT' if a > b + c else '4'


def frozen_of(c):
    return [i for i in range(c.pr.n) if c.phi[i] is not None]


def t_of(c):
    return sum(c.pool_threat(x) for x in frozen_of(c))


def r_of(c):
    return sum(c.robust(i) for i in range(c.pr.n))


def lam_of(c):
    return sum(c.level(i) for i in range(c.pr.n))


def p_of(c):
    return sum(len(c.L & c.U[x]) for x in frozen_of(c))


POTS = {
    'phi1': lambda c: (-t_of(c), r_of(c), lam_of(c), -p_of(c)),   # Conjecture Phi' of k4/c4min.md §4
    'phi': lambda c: (-t_of(c), r_of(c), lam_of(c)),
    'rl': lambda c: (r_of(c), lam_of(c)),
    'trl': lambda c: (-t_of(c), r_of(c), lam_of(c)),
    'tl': lambda c: (-t_of(c), lam_of(c)),
    'rlt': lambda c: (r_of(c), lam_of(c), -t_of(c)),
    'rltp': lambda c: (r_of(c), lam_of(c), -t_of(c), -p_of(c)),
    'rlp': lambda c: (r_of(c), lam_of(c), -p_of(c)),
    'rlb': lambda c: (r_of(c), lam_of(c), -bt_of(c)),
    'brl': lambda c: (-bt_of(c), r_of(c), lam_of(c)),
    'btphi1': lambda c: (-tbt_of(c), r_of(c), lam_of(c), -pbt_of(c)),   # protection first, for big-top frozen agents only
    'btphi': lambda c: (-tbt_of(c), r_of(c), lam_of(c)),
}


def bt_of(c):
    return sum(xtype(c.pr, x, c.phi[x]) == 'BT' for x in frozen_of(c))


def tbt_of(c):
    return sum(c.pool_threat(x) for x in frozen_of(c) if xtype(c.pr, x, c.phi[x]) == 'BT')


def pbt_of(c):
    return sum(len(c.L & c.U[x]) for x in frozen_of(c) if xtype(c.pr, x, c.phi[x]) == 'BT')


def holdings(c):
    return tuple(('F', c.phi[i]) if c.phi[i] is not None else ('Q', c.Q[i]) for i in range(c.pr.n))


def f1_profiles(fn, rand, seed):
    rng = random.Random(seed)
    for ci, (n, m, sets) in enumerate(load_cores(fn)):
        for vals in profiles(sets, m, rng, rand if rand else None):
            pr = Profile(vals, m)
            f, ks = keys(pr)
            if f != 1 or f - (2 * n - m) <= 0: continue
            yield ci, pr, ks


def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict((a[2:].split('=') + [''])[:2] for a in sys.argv[1:] if a.startswith('--'))
    rand = int(opt.get('rand', 0) or 0); seed = int(opt.get('seed', 1) or 1)
    pots = (opt.get('pots') or 'phi1,phi,rl,tl').split(',')
    nex = int(opt.get('ex', 3) or 3)
    for fn in files:
        C = collections.Counter(); ex = collections.defaultdict(list); t0 = time.time()
        for ci, pr, ks in f1_profiles(fn, rand, seed):
            n = pr.n
            cfs = [c for NA, phi in ks for c in configs(pr, NA, phi)]
            for c in cfs:   # sanity: someone needs the frozen good (else f = 0)
                x = frozen_of(c)[0]
                assert any(c.phi[x] <= needs(pr.vals[z], c.H(z)) for z in range(n) if z != x)
            comp = [bool(c.owners()) for c in cfs]
            C['profiles'] += 1; C['configurations'] += len(cfs); C['configurations without valid owner'] += comp.count(False)
            if not any(comp): C['PROFILES WITHOUT ANY COMPLETABLE CONFIGURATION'] += 1
            tmin = min(t_of(c) for c in cfs)
            if tmin > 0: C['profiles where every configuration has t > 0'] += 1
            for pn in pots:
                K = [POTS[pn](c) for c in cfs]
                if 'maxima' in opt:
                    mx = max(K)
                    for c, k, ok in zip(cfs, K, comp):
                        if k != mx: continue
                        x = frozen_of(c)[0]; ty = xtype(pr, x, c.phi[x])
                        C[f'{pn} maxima, x type {ty}'] += 1
                        if not ok:
                            C[f'{pn} maxima, x type {ty}: NOT COMPLETABLE'] += 1
                            if len(ex[pn]) < nex: ex[pn].append(f'core {ci} {fmt_profile(pr)} frozen {x}:{sorted(c.phi[x])} pairs {dict((i, sorted(q)) for i, q in c.Q.items())} pool {sorted(c.L)}')
                        if t_of(c): C[f'{pn} maxima, x type {ty}: t > 0'] += 1
                        if not c.pool_optimal(): C[f'{pn} maxima, x type {ty}: not pool-optimal'] += 1
                if 'moves' in opt:
                    H = [holdings(c) for c in cfs]
                    for a in range(len(cfs)):
                        if comp[a]: continue
                        x = frozen_of(cfs[a])[0]; ty = xtype(pr, x, cfs[a].phi[x])
                        best = None
                        for b in range(len(cfs)):
                            if K[b] > K[a]:
                                d = sum(1 for i in range(n) if H[a][i] != H[b][i])
                                if best is None or d < best: best = d
                        C[f'{pn} non-completable, x type {ty}: smallest raising change {best}'] += 1
                        if best is None and len(ex[pn + ' local max']) < nex:
                            c = cfs[a]
                            ex[pn + ' local max'].append(f'core {ci} {fmt_profile(pr)} frozen {x}:{sorted(c.phi[x])} pairs {dict((i, sorted(q)) for i, q in c.Q.items())} pool {sorted(c.L)}')
        print(f'FILE {fn} rand={rand} seed={seed} ({time.time() - t0:.0f} s)')
        for k in sorted(C): print(f'  {k}: {C[k]}')
        for k in ex:
            for e in ex[k]: print(f'  example ({k}):', e)
        sys.stdout.flush()


if __name__ == '__main__':
    main()
