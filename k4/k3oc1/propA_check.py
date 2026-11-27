"""Independent check of kgen-n3's Proposition A (kgen/n3.md §15.17 on claude/kgen-n3), written from its statement
only: one terminal t, k in E_t with (alpha) no other x in E_t with the same pair, (beta) the sets pair_x - pair_k
(x in E_t - {k}) share a good g.  Rotate k along its Rule E chain into t (no upgrades afterwards), give g to some
terminal of the result and every other junk good to k, and test EFX0 directly (k3lib.efx0, values 4 > 3 > 2).
Also tests the variant without LB's upgrades at the draft, to see whether (UT) is needed.
    python3 k4/k3oc1/propA_check.py gapfile:FILE... [noupgrade]"""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines, bundles, efx0, vals
from lbtest import upgrade, parts, exposed
from t2k import wanters_of, chain, rotate
NOUP = 'noupgrade' in sys.argv
C = collections.Counter()
for a in sys.argv[1:]:
    if a == 'noupgrade': continue
    for line in read_lines(a[8:] if a.startswith('gapfile:') else a):
        mt = re.search(r'GAP (\[\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\)) \|T\| (\d+)', line)
        if not mt or mt.group(5) != '1': continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); n = len(rk)
        order = ast.literal_eval(mt.group(3)); Y = ast.literal_eval(mt.group(4)); pos = {x: i for i, x in enumerate(order)}
        b = base_of(Y, m); bu = b if NOUP else upgrade(rk, m, b)
        B, J, U, NA, F, T = parts(rk, m, bu)
        if len(T) != 1: C['skipped: |T| != 1 without upgrades'] += 1; continue
        t = T[0]; E = exposed(rk, bu, t, B, J, U); W = wanters_of(rk, bu, B, U)
        pair = {x: {rk[x][1], rk[x][2]} for x in E}
        found = False
        for k in E:
            others = [x for x in E if x != k]
            if any(pair[x] == pair[k] for x in others): continue                       # (alpha)
            common = set.intersection(*[pair[x] - pair[k] for x in others]) if others else set(range(m))
            if not common: continue                                                     # (beta)
            p = chain(k, W, pos)
            assert p is not None and p[-1] == t, (line, k, p)
            nb = rotate(rk, bu, B, p); B2 = bundles(nb, n); J2 = [g for g in range(m) if nb[g] < 0]
            g = min(common & set(J2)) if others else None
            P2 = parts(rk, m, nb); T2 = P2[5]
            if not T2: C['NO TERMINAL after rotation'] += 1; continue
            ok_any = False
            for t2 in T2:
                X = [list(x) for x in B2]
                for h in J2:
                    (X[t2] if h == g else X[k]).append(h)
                if efx0(vals(rk), X): ok_any = True; break
            C['(k with alpha, beta): explicit completion EFX0 %s' % ok_any] += 1
            if not ok_any: print('FAIL', line.strip()[4:200], 'k', k, 'chain', p, flush=True)
            found = True
        C['drafts: some k satisfies alpha and beta %s' % found] += 1
for k in sorted(C): print(C[k], k)
