"""kgen-n3's twin class R1 (one terminal t, E_t = two agents with the same pair): does some twin's Rule E rotation
complete with owner nobody or t (exact test, owner restricted)?  On GAP lines, and on te_sample.py lines with picks.
    python3 k4/k3oc1/twins_check.py FILE..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts, exposed, lb2_owners
from t2k_e import valid_rotations, topo
C = collections.Counter(); seen = set()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        mt = re.search(r'(\[\[.*?\]\]) (\d+) (?:order (\(.*?\)) )?picks (\(.*?\))', line)
        if not mt: continue
        key = (mt.group(1), mt.group(4))
        if key in seen: continue
        seen.add(key)
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        if any(g is None for g in Y): continue
        order = ast.literal_eval(mt.group(3)) if mt.group(3) else topo(rk, Y)
        bu = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, bu)
        if len(T) != 1: continue
        E = exposed(rk, bu, T[0], B, J, U)
        if len(E) != 2 or {rk[E[0]][1], rk[E[0]][2]} != {rk[E[1]][1], rk[E[1]][2]}: continue
        oks = [bool(lb2_owners(rk, m, nb, {'none', T[0]})) for k, p, nb in valid_rotations(rk, m, order, Y)]
        C['twins: some rotation completes with owner none or t %s; every %s' % (any(oks), all(oks))] += 1
        if not any(oks): print('FAIL', line.strip()[:200], flush=True)
for k in sorted(C): print(C[k], k)
