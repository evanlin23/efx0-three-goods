#!/usr/bin/env python3
"""Analyses of k4/c4min.md §4 (Python, k4/c4min_cfg.py), on profiles with fewest frozen agents >= 1 and omega >= 1.

  --maxima : structure at the maxima of Phi = (-t, r, Lambda): completable, pool-optimal, t = 0, unfreezing needed,
             agents threatened by two owners, frozen agents threatened by some owner.
  --moves  : for every configuration without a valid owner (C = {}), whether some Phi-raising pool move exists (one
             free agent re-picks its pair inside its pair and the pool), else some Phi-raising cycle move of the
             exchange digraph (threat and need edges; receivers take the predecessor's pair, or their best admissible
             pair inside it and the pool), else neither.
usage: python3 k4/c4min_moves.py FILE --maxima|--moves [--rand=N] [--seed=S]"""
import collections, itertools, os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c4min_lib import load_cores, profiles, Profile, v, threatened, fmt_profile
from c4min_cfg import keys, configs, Config, exchange_digraph, simple_cycles, cycle_move


def pool_moves(c):
    pr = c.pr
    for y in c.free:
        vy = v(pr.vals[y], c.Q[y])
        for S in itertools.combinations(sorted(c.Q[y] | c.L), 2):
            S = frozenset(S)
            if v(pr.vals[y], S) > vy:
                Q = dict(c.Q); Q[y] = S
                yield Config(pr, c.NA, c.phi, Q, (c.L | c.Q[y]) - S)


def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict((a[2:].split('=') + [''])[:2] for a in sys.argv[1:] if a.startswith('--'))
    rand = int(opt.get('rand', 0) or 0); seed = int(opt.get('seed', 1) or 1)
    for fn in files:
        C = collections.Counter(); ex = []; t0 = time.time(); rng = random.Random(seed)
        for ci, (n, m, sets) in enumerate(load_cores(fn)):
            for vals in profiles(sets, m, rng, rand if rand else None):
                pr = Profile(vals, m)
                f, ks = keys(pr)
                if f == 0 or f - (2 * n - m) <= 0: continue
                C['profiles (f >= 1, omega >= 1)'] += 1
                cfs = [c for NA, phi in ks for c in configs(pr, NA, phi)]
                if 'maxima' in opt:
                    K = [c.phi_key() for c in cfs]; mx = max(K)
                    for c, k in zip(cfs, K):
                        if k != mx: continue
                        C['maxima'] += 1
                        if not c.owners(): C['maxima without valid owner (FAIL)'] += 1
                        if not c.owners(unfreeze=False): C['maxima needing unfreezing'] += 1
                        if not c.pool_optimal(): C['maxima not pool-optimal'] += 1
                        if k[0] < 0: C['maxima with t > 0'] += 1
                        E = c.threats()
                        if any(q > 1 for q in collections.Counter(x for o, x in E).values()): C['maxima with an agent threatened by two owners'] += 1
                        if any(c.phi[x] is not None for o, x in E): C['maxima with a frozen agent threatened by some owner'] += 1
                if 'moves' in opt:
                    for c in cfs:
                        if any(c.owner_ok(o, unfreeze=False) for o in c.free): continue
                        C['configurations without valid owner'] += 1
                        k0 = c.phi_key()
                        if any(c2.phi_key() > k0 for c2 in pool_moves(c)): C['  ... with a Phi-raising pool move'] += 1; continue
                        found = False
                        for cyc in simple_cycles(exchange_digraph(c), n):
                            for bp in (True, False):
                                c2 = cycle_move(c, cyc, bp)
                                if c2 is not None and c2.phi_key() > k0: found = True; break
                            if found: break
                        if found: C['  ... else with a Phi-raising cycle move'] += 1
                        else:
                            C['  ... neither'] += 1
                            if len(ex) < 5: ex.append(f'core {ci} {fmt_profile(pr)} frozen {[sorted(z) if z else "-" for z in c.phi]} pairs {dict((i, sorted(q)) for i, q in c.Q.items())} pool {sorted(c.L)}')
        print(f'FILE {fn} ({time.time() - t0:.0f} s)')
        for k in sorted(C): print(f'  {k}: {C[k]}')
        for e in ex: print('  example (neither):', e)
        sys.stdout.flush()


if __name__ == '__main__':
    main()
