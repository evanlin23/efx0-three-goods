"""Every valid Rule E rotation (t2k.py) followed by the exact test lb2 with any owner (kgen-n3's T1-E form), on GAP
lines; reports per draft whether every / some rotation of a frozen k completes, and counts rotations
(length-zero ones, k an exposed terminal dropping its top, are counted apart: they are not improving chains).
    python3 k4/k3oc1/t2k_every.py gapfile:FILE... [T=2]"""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines
from lbtest import upgrade, parts, exposed, lb2
from t2k import wanters_of, chain, rotate

C = collections.Counter(); want_T = None
for a in sys.argv[1:]:
    if a.startswith('T='): want_T = int(a[2:])
for a in sys.argv[1:]:
    if a.startswith('T='): continue
    for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
        mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt or (want_T is not None and int(mt.group(5)) != want_T): continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2))
        order = ast.literal_eval(mt.group(3)); Y = ast.literal_eval(mt.group(4)); tag = '|T| %s: ' % mt.group(5)
        pos = {a_: i for i, a_ in enumerate(order)}
        bu = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, bu)
        W = wanters_of(rk, bu, B, U); oks = []
        ks = set()
        for t in T: ks |= set(exposed(rk, bu, t, B, J, U))
        for k in sorted(ks):
            if B[k] != [rk[k][0]]: continue
            p = chain(k, W, pos)
            if p is None or p[-1] not in T or not {rk[k][1], rk[k][2]} <= set(J) | set(B[p[-1]]): continue
            ok = bool(lb2(rk, m, rotate(rk, bu, B, p)))
            if len(p) == 1: C[tag + 'length-zero (k a terminal) completing %s' % ok] += 1; continue
            oks.append(ok)
            C[tag + 'rotations completing %s' % ok] += 1
            if not ok and C[tag + 'printed'] < 3:
                C[tag + 'printed'] += 1; print('EVERYFAIL', line.strip()[4:200], 'k', k, 'chain', p, flush=True)
        if oks:
            C[tag + 'drafts: every rotation completes %s' % all(oks)] += 1
for k in sorted(C): print(k, C[k])
