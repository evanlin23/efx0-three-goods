#!/usr/bin/env python3
"""Brute-force checks of Theorem F (k4/c4min.md §3) and its lemmas, from the definitions (k4/c4min_cfg.py);
independent of k4/c4min.c.

Theorem F: if some configuration at the fewest frozen agents has every frozen agent robust (v_x(U_x) <= v_x(phi(x))),
every such configuration maximizing (r, Lambda) has a valid owner with C = {} (no unfreezing).
Checked on every configuration of every key whose frozen agents are all robust ("F-configurations"):
  A  at a pool-optimal F-configuration: no frozen agent and no robust free agent is threatened by any owner, and every
     free agent is threatened by at most one owner;
  B  at a pool-optimal F-configuration without a valid owner: owner -> threatened agent is a permutation of the free
     agents, and the rotation (plain, or modified at a rich-pair agent) of each cycle is a configuration with the same
     frozen agents in which some free agent is robust, unless every agent of the cycle is of kind T4;
  C  if every free agent is of kind T4 there: f >= 1 and some cycle of frozen agents each preferring its predecessor's
     good exists (f = 0: the pool is worthless to everyone, impossible in a core);
  D  every (r, Lambda)-maximal F-configuration has a valid owner with C = {}.
usage: python3 k4/c4min_f.py FILE [--rand=N] [--seed=S] [--only=I,J] [--minf=K]"""
import collections, itertools, os, sys, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c4min_lib import load_cores, profiles, Profile, v, needs, threatened, fmt_profile
from c4min_cfg import keys, configs, Config, FOREIGN


def top_of(val, U):
    return max(U, key=lambda g: val[g])


def kind(c, y):
    """robust, T3 (|U| = 3, holds top of U with a good outside U), T4, D, R (as in §3.2, relative to U_y)"""
    val = c.pr.vals[y]; U = c.U[y]; Q = c.Q[y]
    if c.robust(y): return 'rob'
    u1 = top_of(val, U); B = Q & U
    if B == {u1}: return 'T%d' % len(U)
    if u1 in B: return 'D'
    return 'R'


def owner_ok0(c, o):
    X = c.Q[o] | c.L
    return c.admissible_in(o, X) and not any(threatened(c.pr.vals[x], X, c.H(x)) for x in range(c.pr.n) if x != o)


def rotate(c, cyc, sigma):
    pred = {sigma[a]: a for a in cyc}
    Q2 = dict(c.Q); L2 = set(c.L); mod = False
    for b in cyc: Q2[b] = c.Q[pred[b]]
    for b in cyc:
        if kind(c, b) == 'R':
            val = c.pr.vals[b]; U = c.U[b]; a = top_of(val, U)
            s = [g for g in U if g not in c.Q[b] and g != a][0]
            if s in c.L and a in c.Q[pred[b]]:
                y = next(iter(c.Q[pred[b]] - {a}))
                Q2[b] = frozenset([a, s]); L2.discard(s); L2.add(y); mod = True
                break
    return Config(c.pr, c.NA, c.phi, Q2, frozenset(L2)), mod


def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=') for a in sys.argv[1:] if a.startswith('--'))
    rand = int(opt.get('rand', 0)); seed = int(opt.get('seed', 1)); minf = int(opt.get('minf', 0))
    only = set(map(int, opt['only'].split(','))) if 'only' in opt else None
    for fn in files:
        C = collections.Counter(); t0 = time.time(); rng = random.Random(seed)
        for ci, (n, m, sets) in enumerate(load_cores(fn)):
            if only is not None and ci not in only: continue
            for vals in profiles(sets, m, rng, rand if rand else None):
                pr = Profile(vals, m)
                f, ks = keys(pr)
                if f - (2 * n - m) <= 0 or f < minf: continue
                cfs = []
                for NA, phi in ks:
                    probe = Config(pr, NA, phi, {}, frozenset())
                    if all(probe.robust(x) for x in range(n) if phi[x] is not None):
                        cfs.extend(configs(pr, NA, phi))
                if not cfs: C['profiles without an F-configuration (not covered)'] += 1; continue
                C['profiles with an F-configuration, f = %d' % f] += 1
                keyv = []
                for c in cfs:
                    keyv.append((sum(c.robust(i) for i in range(n)), sum(c.level(i) for i in range(n))))
                    E = c.threats()
                    if any(c.phi[x] is not None or c.robust(x) for o, x in E): C['VIOLATION A: frozen or robust agent threatened'] += 1
                    if not c.pool_optimal(): continue
                    C['pool-optimal F-configurations'] += 1
                    if any(k > 1 for k in collections.Counter(x for o, x in E).values()): C['VIOLATION A: two owners'] += 1
                    if any(owner_ok0(c, o) for o in c.free): continue
                    C['pool-optimal F-configurations without valid owner'] += 1
                    sigma = {}
                    for o, x in E: sigma.setdefault(o, x)
                    if sorted(sigma) != sorted(c.free) or sorted(sigma.values()) != sorted(c.free): C['VIOLATION B: not a permutation'] += 1; continue
                    seen = set(); allT4 = True
                    for s0 in c.free:
                        if s0 in seen: continue
                        cyc = []; x = s0
                        while x not in seen: seen.add(x); cyc.append(x); x = sigma[x]
                        kinds = [kind(c, b) for b in cyc]
                        if all(k == 'T4' for k in kinds): C['cycles of kind T4 only'] += 1; continue
                        allT4 = False
                        c2, mod = rotate(c, cyc, sigma)
                        used = frozenset().union(*c2.Q.values()) if c2.Q else frozenset()
                        ok = (len(used) == 2 * len(c2.Q) and not (used & c2.L) and len(c2.L) == len(c.L)
                              and all(not (needs(pr.vals[y], c2.Q[y] & c2.U[y]) & c2.U[y]) for y in c2.free))
                        if ok and any(c2.robust(b) for b in cyc): C['rotations checked (%s)' % ('modified' if mod else 'plain')] += 1
                        else: C['VIOLATION B: rotation'] += 1
                    if allT4:
                        if f == 0: C['VIOLATION C: all T4 at f = 0'] += 1
                        else:
                            fr = [x for x in range(n) if c.phi[x] is not None]
                            succ = {x: [z for z in fr if z != x and c.phi[x] <= needs(pr.vals[z], c.phi[z])] for x in fr}
                            if all(succ[x] for x in fr): C['all T4: frozen improving cycle exists'] += 1
                            else: C['VIOLATION C: all T4, no frozen cycle'] += 1
                best = max(keyv)
                for c, kv in zip(cfs, keyv):
                    if kv != best: continue
                    C['(r, Lambda)-maximal F-configurations'] += 1
                    if not any(owner_ok0(c, o) for o in c.free): C['VIOLATION D: maximum without valid owner'] += 1
        print(f'FILE {fn} ({time.time() - t0:.0f} s)')
        for k in sorted(C): print(f'  {k}: {C[k]}')
        sys.stdout.flush()


if __name__ == '__main__':
    main()
