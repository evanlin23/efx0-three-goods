"""Release mechanism of Rule E rotations (k4/k3_oc1.md §12.1): for every valid Rule E rotation on GAP lines, the chain
length s (receivers), the releases r = omega - omega' (Lemma 5), and the split of r into released chain receivers,
released off-chain agents, and agents removed by upgrades; is r >= s - 1?  Also the longest chain's length vs omega.
    python3 k4/k3oc1/te_release_mech.py gapfile:FILE..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts
from t2k_e import valid_rotations
C = collections.Counter()
for a in sys.argv[1:]:
    for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
        mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        P0 = parts(rk, m, upgrade(rk, m, base_of(Y, m))); om = len(P0[1]) - len(P0[5]); F0 = set(P0[4])
        best = None
        for k, p, nb in valid_rotations(rk, m, ast.literal_eval(mt.group(3)), Y):
            P = parts(rk, m, upgrade(rk, m, nb)); r = om - (len(P[1]) - len(P[5])); s = len(p) - 1
            Fn = set(P[4]); rel = F0 - Fn - {k}
            C['r >= s - 1: %s' % (r >= s - 1)] += 1
            C['r >= s: %s' % (r >= s)] += 1
            if best is None or r > best[0]: best = (r, s)
        if best: C['draft: max r >= omega - 1 %s; max r achieved by a chain of length >= omega - 1 %s' % (best[0] >= om - 1, best[1] >= om - 1)] += 1
for k in sorted(C): print(C[k], k)
