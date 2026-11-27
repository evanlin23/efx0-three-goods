"""The hard perfect starts with one truly dangerous agent k where Corollary U2 does not apply (every improving
H0 inside J & R_k crowds a holder other than the head), k4/p3.md section 6. For each, every improving H0 inside
(J + {Y_z}) & R_k on the unique chain P(k): whether Y_z is in H0, the crowded holders other than z, the DEMAND agents
(dangerous agents other than k, frozen after P(k), threatened by J + {Y_z}), and whether B' has a one-absorber
completion (SAT, k4/p3/oc1max.Checker). Classes: 'Y_z in some clean H0' (Lemma D-red applies), 'some H0 with Y_z, no
crowd, DEMAND only', 'every H0 crowded'; and whether P(k) repairs at all. Prints the first start of each class.
    python3 k4/p3/nou2.py HARD.jsonl.gz [...]      (records of k4/p3/t1_p2.py)
"""
import sys, os, json, gzip, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import Inst
from oc1max import Checker
from keep2 import analyse, chain, state, frozen_at, threatened
from t1_p2 import u2
cnt = collections.Counter(); seen_cls = set()
for f in sys.argv[1:]:
    for line in gzip.open(f, 'rt'):
        d = json.loads(line)
        if len(d['DT']) != 1: continue
        I = Inst(d['sets'], d['vals'], d['m']); Y = d['picks']
        J, p, w, F, D, DT, EJ = analyse(I, Y); k = next(iter(DT))
        if any(True for _ in u2(I, Y, k, J, p, w)): continue
        K = Checker(I); P = chain(w, k); z = P[-1]
        res = []
        pool = [g for g in J if g in I.R[k]] + ([Y[z]] if Y[z] in I.R[k] else [])
        for r in range(1, len(pool) + 1):
            for H0 in itertools.combinations(pool, r):
                if I.val(k, H0) <= p[k]: continue
                B = state(I, Y, P, H0)
                holders = [u for u in range(I.n) if u != k and not frozen_at(I, B, u)]
                crowd = [u for u in holders if u != z and len(set(H0) & I.R[u]) >= 2 and I.val(u, set(H0) & I.R[u]) > I.val(u, B[u])]
                Pi = set(J) | {Y[z]}
                demand = [q for q in D - {k} if frozen_at(I, B, q) and threatened(I, q, Pi, I.val(q, B[q]))]
                ok = K.complete(tuple(B)) is not None
                res.append((H0, Y[z] in H0, crowd, demand, ok))
        tag = ('Y_z in some clean H0' if any(r[1] and not r[2] and not r[3] for r in res) else
               'some H0 with Y_z, no crowd, DEMAND only' if any(r[1] and not r[2] for r in res) else 'every H0 crowded')
        rep = any(r[4] for r in res)
        cnt[(f'|D|={len(D)}', tag, 'P(k) repairs' if rep else 'P(k) does not repair')] += 1
        if not rep:                                    # who moves in the repairing moves?
            base = tuple(frozenset([y]) for y in Y); movers = set(); touch_k = False
            for st in K.moves(base):
                if K.complete(st) is not None:
                    ch = {i for i in range(I.n) if st[i] != base[i]}; movers |= ch; touch_k |= k in ch
            cnt[('P(k) does not repair:', 'some repairing move changes k' if touch_k else 'no repairing move changes k',
                 'movers include a pick-dangerous agent' if movers & (D - DT) else 'no pick-dangerous mover',
                 'one move repairs' if movers else 'NO MOVE REPAIRS')] += 1
        if (tag, rep) not in seen_cls:
            seen_cls.add((tag, rep)); print('first', tag, rep, json.dumps({'sets': d['sets'], 'vals': d['vals'], 'picks': Y, 'k': k, 'P': P, 'EJ': sorted(EJ), 'D': sorted(D)}), res)
        K.close()
print("$ python3 k4/p3/nou2.py " + " ".join(sys.argv[1:]))
for k in sorted(cnt, key=str): print(k, cnt[k])
