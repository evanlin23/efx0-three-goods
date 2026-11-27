"""How the least-omega DE trade repairs one-terminal perfect drafts (after LB's upgrades T = {l}, every agent picks)
with |E_l| >= 2: for each exposed agent x' other than the rotated one, is it rotated into a pair, killed (a good of
its pair now sits in a pair or is no longer junk), released (it is a terminal afterwards and self-serves), or still
an exposed frozen agent?  And which owner works afterwards (exact test lbtest.lb2)?
    python3 k4/k3oc1/mechanism.py LOG..."""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines, bundles
from de_moves import de_trades
from lbtest import upgrade, parts, exposed, lb2
C = collections.Counter()
for fn in sys.argv[1:]:
    for line in read_lines(fn):
        mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
        if not mt: continue
        rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
        if any(g is None for g in Y): continue
        b0 = base_of(Y, m)
        if lb2(rk, m, b0): continue
        b = upgrade(rk, m, b0); B, J, U, NA, F, T = parts(rk, m, b)
        if len(T) != 1: continue
        ell = T[0]; E = exposed(rk, b, ell, B, J, U)
        if len(E) < 2: continue
        C['one-terminal perfect, |E| >= 2'] += 1
        mv = de_trades(rk, m, b)
        om = {nb: (lambda P: len(P[1]) - len(P[5]))(parts(rk, m, nb)) for nb, d in mv}; w = min(om.values())
        for nb, d in mv:
            if om[nb] != w: continue
            wit = lb2(rk, m, nb)
            B2, J2, U2, NA2, F2, T2 = parts(rk, m, nb)
            fates = []
            for x in E:
                if U2[x]: fates.append('rotated')
                elif not ({rk[x][1], rk[x][2]} <= set(J2) | set(B2[ell]) | set(g for g in J2)) and x in T2: fates.append('killed+released')
                elif x in T2: fates.append('released')
                elif not set(g for g in (rk[x][1], rk[x][2])) <= set(J2) | set(B2[ell]): fates.append('killed')
                else: fates.append('still exposed and frozen')
            C['least-omega trade %s; witness %s; other exposed: %s' % (d[0], wit[0] if wit else 'NONE', ', '.join(sorted(f for f in fates if f != 'rotated') or ['-']))] += 1
            break
for k in sorted(C): print(k, C[k])
