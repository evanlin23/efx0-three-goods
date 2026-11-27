"""Classify sampled failure lines of te_sample.py (TE-any, TE-every_least-omega, ...) by coverage: R1-compatible
(Theorem R1C), Theorem B*, or the gap; and for TE-any lines, which Rule E rotations fail (exact, any owner) and the
order sigma used (least-index topological order).
    python3 k4/k3oc1/te_classify.py FILE..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import lb2, upgrade, parts, exposed
from r1compat import r1_compatible
from thm_bstar import bstar
from t2k_e import valid_rotations, topo
from gap_scan import an_order
C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        mt = re.match(r'(TE-\S+|T\'K-\S+|NOROT) (\[\[.*?\]\]) (\d+) picks (\(.*?\))', line)
        if not mt: continue
        kind = mt.group(1); rk = [tuple(r) for r in json.loads(mt.group(2))]; m = int(mt.group(3)); Y = ast.literal_eval(mt.group(4))
        bu = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, bu)
        cov = 'R1C' if r1_compatible(rk, Y) else ('B*' if bstar(rk, m, Y)[0] == 'B* applies' else 'GAP')
        C['%s |T| %d: %s' % (kind, len(T), cov)] += 1
        if cov == 'GAP':
            print(kind, 'GAP', json.dumps([list(x) for x in rk]), m, 'order', tuple(an_order(rk, Y)), 'picks', Y, '|T|', len(T),
                  '|E_t|', [len(exposed(rk, bu, t, B, J, U)) for t in T])
            if kind == 'TE-any':
                for k, p, nb in valid_rotations(rk, m, topo(rk, Y), Y):
                    print('    sigma', topo(rk, Y), 'k', k, 'chain', p, 'completes', bool(lb2(rk, m, nb)))
for k in sorted(C): print(k, C[k])
