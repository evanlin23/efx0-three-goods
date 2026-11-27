"""Distribution of omega_0 = |J| - |T| at the draft and of the least omega' over the valid Rule E rotations (after LB's
maximal upgrades), on GAP lines; with whether the least-omega' rotations complete (N/E/K with k's slot).
    python3 k4/k3oc1/te_omega.py gapfile:FILE..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts
from te_rules import results
C = collections.Counter()
for a in sys.argv[1:]:
    for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
        mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        P = parts(rk, m, upgrade(rk, m, base_of(Y, m))); om0 = len(P[1]) - len(P[5])
        R = results(rk, m, ast.literal_eval(mt.group(3)), Y)
        if not R: C['|T| %s: omega %d, no valid rotation' % (mt.group(5), om0)] += 1; continue
        mo = min(r['om'] for r in R)
        C['|T| %s: omega %d, least omega\' %d, every least-omega\' completes %s' % (mt.group(5), om0, mo, all(r['ok'] for r in R if r['om'] == mo))] += 1
for k in sorted(C): print(C[k], k)
