"""T-E with any owner (kgen-n3's T1-E form, all terminals): at every hard perfect draft of a source, does every valid
Rule E rotation (t2k_e.valid_rotations; sigma = least-index topological order) complete under the exact test lb2 with
any owner?  Counts drafts and rotations; FAIL lines for rotations that do not complete.
    python3 k4/k3oc1/te_any.py SOURCE [SHARD NSHARDS]"""
import sys, os, json, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of
from lbtest import upgrade, parts, lb2
from t2k_e import valid_rotations, topo
from oc1_fast import drafts
from oc1_k3 import hypergraphs, profiles
src = sys.argv[1]; shard, nsh = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (0, 1)
C = collections.Counter(); print('$ python3 k4/k3oc1/te_any.py', *sys.argv[1:], flush=True)
for ci, (sets, m) in enumerate(hypergraphs(src, None)):
    if ci % nsh != shard: continue
    for rk in profiles(sets, 0, None):
        for Y in drafts(rk, len(sets)):
            if any(g is None for g in Y) or lb2(rk, m, base_of(Y, m)): continue
            tag = '|T| %d: ' % len(parts(rk, m, upgrade(rk, m, base_of(Y, m)))[5])
            R = valid_rotations(rk, m, topo(rk, Y), Y)
            if not R: C[tag + 'no valid rotation'] += 1; continue
            oks = []
            for k, p, nb in R:
                r = lb2(rk, m, nb); oks.append(bool(r))
                C[tag + 'rotations: ' + (('owner kind ' + ('e' if r[1] == p[-1] else 'k' if r[1] == k else 'other')) if r and r[0] == 'owner' else 'no owner' if r else 'FAIL')] += 1
                if not r: print('FAIL', json.dumps([list(x) for x in rk]), m, 'picks', Y, 'k', k, 'chain', p, flush=True)
            C[tag + 'drafts: every rotation completes %s' % all(oks)] += 1
for k in sorted(C): print(k, C[k])
