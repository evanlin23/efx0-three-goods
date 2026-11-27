"""Lemma 7 of k4/k3_oc1.md §12.1 on the drafts with no valid Rule E rotation (NOROT lines of te_sample.py, or the MISS
lines of t2k.py): choose for each terminal t its sigma-first frozen exposed agent k_t, follow f(t) = end(k_t) to a
cycle, build the ring t1 -> k_t1 ~> t2 -> ... (Rule E segments), check the junk partners are distinct, apply it and
test the one-absorber completion (lb2, any owner).
    python3 k4/k3oc1/pointer_walk.py FILE..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts, exposed, lb2
from t2k import wanters_of, chain
from t2k_e import topo, valid_rotations

def walk(rk, m, Y, order):
    pos = {a: i for i, a in enumerate(order)}
    bu = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, bu)
    W = wanters_of(rk, bu, B, U)
    kt = {}
    for t in T:
        E = [x for x in exposed(rk, bu, t, B, J, U) if x in F]
        if not E: return 'Lemma 6 fails?', None
        kt[t] = min(E, key=lambda x: pos[x])
    seg = {t: chain(kt[t], W, pos) for t in T}
    f = {t: seg[t][-1] for t in T}
    t = T[0]; seen = []
    while t not in seen: seen.append(t); t = f[t]
    cyc = seen[seen.index(t):]
    partners = [({rk[kt[t]][1], rk[kt[t]][2]} - {B[t][0]}).pop() for t in cyc]
    if len(set(partners)) < len(partners): return 'partners not distinct', cyc
    nb = list(bu)
    for t in cyc:
        p = seg[t]                     # k_t = p[0] ~> p[-1] = f(t)
        for i in range(1, len(p)): nb[B[p[i - 1]][0]] = p[i]
        nb[rk[p[0]][1]] = p[0]; nb[rk[p[0]][2]] = p[0]   # k_t takes Y_t and its junk partner
    return ('ring completes %s' % bool(lb2(rk, m, tuple(nb)))), cyc

C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        mt = re.search(r'(\[\[.*?\]\]) (\d+) (?:order (\(.*?\)) )?picks (\(.*?\))', line)
        if not mt or not (line.startswith('NOROT') or line.startswith('MISS')): continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        order = ast.literal_eval(mt.group(3)) if mt.group(3) else topo(rk, Y)
        if valid_rotations(rk, m, order, Y): C['has a valid rotation (skipped)'] += 1; continue
        res, cyc = walk(rk, m, Y, order)
        C['%s; cycle length %s' % (res, len(cyc) if cyc else None)] += 1
for k in sorted(C): print(C[k], k)
