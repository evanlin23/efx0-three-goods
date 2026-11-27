"""Conjecture T' (k4/k3_oc1.md §12): at a hard perfect draft (every agent picks), some rotation -- a DE trade from an
exposed agent k of a terminal t, along a need chain into t (a DE chain if k's pair is junk, a ring with the pair arrow
t -> k otherwise) -- followed by LB's upgrades, leaves |J'| <= |T'|, so the junk fits the terminals' slots and no
owner is needed.  For |T| = 1 this is kgen-n3's T1'.  Tested on GAP lines (gap_scan.py) or on every hard perfect
draft of a source; also: does every least-omega' rotation do it?
    python3 k4/k3oc1/tprime.py gapfile:FILE... | source:SOURCE [SHARD NSHARDS]"""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts, exposed, lb2
from de_moves import de_trades

def check(rk, m, Y, C, tag):
    b = base_of(Y, m); bu = upgrade(rk, m, b); B, J, U, NA, F, T = parts(rk, m, bu)
    rot = []
    for nb, d in de_trades(rk, m, bu):
        for t in T:
            if t in d[1] and (d[0] == 'DEring' or d[1][0] in set(exposed(rk, bu, t, B, J, U))):
                rot.append(nb); break
    if not rot: C[tag + 'NO ROTATION'] += 1; return False
    om = {}
    for nb in rot:
        nu_ = upgrade(rk, m, nb); P = parts(rk, m, nu_); om[nb] = len(P[1]) - len(P[5])
    best = min(om.values())
    C[tag + 'some rotation needs no owner %s' % (best <= 0)] += 1
    if best <= 0:
        C[tag + 'every least-omega rotation needs no owner %s' % all(om[nb] <= 0 for nb in rot if om[nb] == best)] += 1
    else:
        C[tag + '  ... but some rotation repairs with an owner %s' % any(lb2(rk, m, nb) for nb in rot)] += 1
    return best <= 0

if __name__ == '__main__':
    C = collections.Counter()
    if sys.argv[1].startswith('source:'):
        from oc1_fast import drafts
        from oc1_k3 import profiles
        from oc1_max import sources
        src = sys.argv[1][7:]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
        for ci, (sets, m) in enumerate(sources(src)):
            if ci % nsh != shard: continue
            for rk in profiles(sets, 0, None):
                for Y in drafts(rk, len(sets)):
                    if any(g is None for g in Y) or lb2(rk, m, base_of(Y, m)): continue
                    T = parts(rk, m, upgrade(rk, m, base_of(Y, m)))[5]
                    if not check(rk, m, Y, C, '|T| %d: ' % len(T)):
                        print('FAIL', json.dumps([list(r) for r in rk]), m, 'picks', Y, flush=True)
    else:
        for a in sys.argv[1:]:
            for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
                mt = re.match(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
                if not mt: continue
                rk = [tuple(r) for r in json.loads(mt.group(1))]
                if not check(rk, int(mt.group(2)), ast.literal_eval(mt.group(4)), C, '|T| %s: ' % mt.group(5)):
                    print('FAIL', line.strip()[:300], flush=True)
    for k in sorted(C): print(k, C[k])
