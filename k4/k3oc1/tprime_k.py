"""Conjecture T'_k (k4/k3_oc1.md §12): at a hard perfect draft, some rotation from an exposed agent k of a terminal t
into t (as in tprime.py) has a one-absorber completion whose owner is nobody or k itself (B*'s owner).  The exact
test lb2 with the owner restricted (lbtest.lb2_owners).  Lines of drafts that need owner k are written with NEEDK,
failures with FAIL.
    python3 k4/k3oc1/tprime_k.py source:SOURCE [SHARD NSHARDS] | gapfile:FILE..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts, exposed, lb2, lb2_owners
from de_moves import de_trades

def rotations(rk, m, bu):
    B, J, U, NA, F, T = parts(rk, m, bu)
    out = []
    for nb, d in de_trades(rk, m, bu):
        for t in T:
            if t in d[1] and (d[0] == 'DEring' or d[1][0] in set(exposed(rk, bu, t, B, J, U))):
                k = d[1][0] if d[0] == 'DEchain' else d[1][(d[1].index(t) + 1) % len(d[1])]
                out.append((nb, t, k, d)); break
    return T, out

def check(rk, m, Y, C, tag):
    """'none' if some rotation needs no owner at all (|J'| <= |T'| after upgrades), 'k' if some rotation completes with
    owner nobody-or-k (exact), 'any' if only with another owner, 'fail' if no rotation completes"""
    bu = upgrade(rk, m, base_of(Y, m)); T, rot = rotations(rk, m, bu)
    res = 'fail'
    for nb, t, k, d in rot:
        P = parts(rk, m, upgrade(rk, m, nb))
        if len(P[1]) <= len(P[5]): res = 'none'; break
    if res == 'fail' and any(lb2_owners(rk, m, nb, {'none', k}) for nb, t, k, d in rot): res = 'k'
    if res == 'fail' and any(lb2(rk, m, nb) for nb, t, k, d in rot): res = 'any'
    C[tag + res] += 1
    return res

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
                    r = check(rk, m, Y, C, '|T| %d: ' % len(T))
                    if r in ('k', 'any', 'fail'):
                        print('NEEDK' if r == 'k' else 'FAIL-' + r, json.dumps([list(r_) for r_ in rk]), m, 'picks', Y, flush=True)
    else:
        for a in sys.argv[1:]:
            for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
                mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
                if not mt: continue
                rk = [tuple(r) for r in json.loads(mt.group(1))]
                r = check(rk, int(mt.group(2)), ast.literal_eval(mt.group(4)), C, '|T| %s: ' % mt.group(5))
                if r in ('any', 'fail'): print('FAIL-' + r, line.strip()[:300], flush=True)
    for k in sorted(C): print(k, C[k])
