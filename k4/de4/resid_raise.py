"""The double clashes that no top swap resolves (k4/de4.md §10.4): for each EX line of a topswap.py log, where the
frozen agents' next goods are held, and the raises (valid states of larger level sum) changing the fewest agents.
EVIDENCE.      python3 k4/de4/resid_raise.py results/k4_de4/topswap_advt4x.log"""
import sys, json, re
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import claimd as CD
CT = CD.CT; T = CD.T; S = CD.S
from de4lib import Inst, leftover, wanted_goods
import topswap as TS
lines = [l for l in open(sys.argv[1]) if l.startswith('EX')]
for l in lines:
    tag, sets, vals, Y, st = json.loads(l[3:])
    I = Inst(sets, vals, 1 + max(max(s) for s in sets))
    All, ph, P = CT.states(I)
    p = T.phi(I, Y)
    J = set(leftover(I, Y)); W = set(wanted_goods(I, Y))
    us = TS.roles(I, Y, J, W)
    # who holds the b of each frozen top-holder
    info = []
    for u in us:
        a = I.ranked(u)[0]; t = next(x for x in range(I.n) if list(Y[x]) == [a])
        r = I.ranked(t); jn = r[r.index(a)+1]
        w = next((x for x in range(I.n) if jn in Y[x]), None)
        info.append('u%d t%d next %d held by %s (%s)' % (u, t, jn, w, Y[w] if w is not None else '-'))
    best = None; bz = []
    for Z, q in zip(All, ph):
        if q <= p: continue
        ch = [i for i in range(I.n) if set(Y[i]) != set(Z[i])]
        if best is None or len(ch) < best: best, bz = len(ch), [Z]
        elif len(ch) == best: bz.append(Z)
    print('Phi', p, 'Phi*', P, 'J', sorted(J), '|', '; '.join(info))
    for Z in bz[:2]:
        print('   raise', T.phi(I, Z), [(i, sorted(Y[i]), sorted(Z[i])) for i in range(I.n) if set(Y[i]) != set(Z[i])])
