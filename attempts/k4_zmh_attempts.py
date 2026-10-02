#!/usr/bin/env python3
"""Replays the failed candidate statements of workstream proof/k4-zmove-hall (attempts/k4-zmh-*.md), each with two
implementations: A = k4/zmh_lib.py (states, Lemma H1 deficits, Z′-maxima through the states and fillers), B = main's
repo-free k4/rt4_n5_indep.py (raw removal-only deficit) with the configurations enumerated directly (k4/zmh_xcheck.py).

usage: python3 attempts/k4_zmh_attempts.py"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'k4'))
from zmh_lib import Prof, show, bits
import zmh_xcheck as XB


def bigtop(sets, vals, x, g):
    v = dict(zip(sets[x], vals[x]))
    if len(sets[x]) != 4: return False
    lo = sorted((v[h] for h in sets[x] if h != g), reverse=True)
    return v[g] > lo[0] + lo[1]


def s1c_plus(inst, x, g):
    """S1c+: at a Z′-maximum of the key (g, x) with x big-top and >= 2 terminals, def(P_Q) <= 0"""
    sets, vals, m = inst['sets'], inst['vals'], inst['m']
    print('instance', inst, ' key: agent %d on good %d, x big-top:' % (x, g), bigtop(sets, vals, x, g))
    # A
    pr = Prof(sets, vals, m)
    key = tuple((1 << g) if i == x else None for i in range(pr.n))
    zs, best = pr.zmax_states(key)
    for P in zs:
        T = [y for y in range(pr.n) if key[y] is None and pr.needs(y, P[y]) >> g & 1]
        print('  A: Z′-max', show(P), 'potential', best, 'terminals', T, 'def(P_Q) =', pr.D[P], 'def* =', pr.dstar[key])
    # B
    omega, out, ns, dstar = XB.zmove_indep(sets, vals, m, all_keys=True, want_ns=True)
    info, D = ns['info'], ns['D']
    for k, (ds, pot, per, t4) in out.items():
        if k[x] != frozenset([g]) or any(k[i] is not None for i in range(len(sets)) if i != x): continue
        for PQ in per:
            N = info(PQ)[0]
            T = [y for y in range(len(sets)) if y != x and g in N[y]]
            print('  B: Z′-max', '(' + ', '.join(str(sorted(b)) for b in PQ) + ')', 'potential', pot, 'terminals', T,
                  'def(P_Q) =', D[PQ], 'def* =', ds)


if __name__ == '__main__':
    print('== attempts/k4-zmh-s1c-plus.md: S1c+ (big-top x, >= 2 terminals at a Z′-maximum => def(P_Q) <= 0) ==')
    s1c_plus({"sets": [[0, 2, 5, 7], [1, 4, 6, 7], [3, 5, 6, 7]], "vals": [[6, 2, 3, 10], [4, 2, 3, 8], [3, 2, 4, 8]],
              "m": 8}, 0, 7)
