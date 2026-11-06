"""Double clashes (k4/de4.md §10.3; ledger K4.DE4V3R). EVIDENCE, and the search that found the counterexample to the
robust candidate (refute_rob.py).

For random instances of the adversarial families (adv_t.py with FAM = NEXTRA extra goods, or adv_t3.py with FAM = t3):
every (V3)-valid (H) state with a double clash (an F2-clash cycle on which the arcs out of two lower-pair holders share
a leftover good). Does it have a raise (a valid state of larger level sum) changing only the four agents of the cycle,
or only those and the holders of the two b's? States with no such raise are written to dc_nolocal_FAM_SEED.json.

    python3 k4/de4/dc_local.py SEED FAM COUNT     (python3 k4/de4/dc_local.py 17 t3 400 finds the counterexample)"""
import sys, os, json, random, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import claimd as CD, lpout as LO, adv_t, adv_t3, nrcyc as NC
CT = CD.CT; T = CD.T; S = CD.S
from de4lib import Inst, wanted_goods, leftover
C = collections.Counter(); EX = []


def roles(I, Y, J, W):
    arcs = CD.graph(I, Y, J, W)
    for c in CD.cycles(I, arcs, I.n):
        if not CD.f2_clash_only(I, Y, J, W, c): continue
        lp = [a for a in c if not CT.frozen(Y, a[0], W) and S.types(I, a[0], list(Y[a[0]])) == 'LP']
        if len(lp) < 2: continue
        sh = set(lp[0][2]) & set(lp[1][2]) & J
        if not sh: continue
        (u1, t2, D2), (u2, t1, D1) = lp[0], lp[1]
        return c, dict(u1=u1, u2=u2, t1=t1, t2=t2), set(D1), set(D2), sh
    return None


def analyse(I, tag):
    All, ph, P = CT.states(I)
    for Y, p in zip(All, ph):
        if not T.v3ok(I, Y): continue
        J = set(leftover(I, Y))
        if not J: continue
        W = set(wanted_goods(I, Y))
        if not CD.H(I, Y, J, W): continue
        r = roles(I, Y, J, W)
        if r is None: continue
        c, R, D1, D2, sh = r
        loc = set(R.values())
        holder = {g: i for i in range(I.n) for g in Y[i]}
        ext = set(loc)
        for k in ('1','2'): ext.add(holder.get(I.ranked(R['u'+k])[1]))
        best = {}
        for Z, q in zip(All, ph):
            if q <= p: continue
            ch = {i for i in range(I.n) if set(Y[i]) != set(Z[i])}
            for name, L in (('cycle', loc), ('cycle+w', ext), ('any', None)):
                if L is None or ch <= L:
                    best[name] = min(best.get(name, 99), len(ch))
        C['double-clash (H) state'] += 1
        C['  raise within the 4 cycle agents: %s' % ('cycle' in best)] += 1
        C['  raise within cycle agents + holders of b_u: %s' % ('cycle+w' in best)] += 1
        if 'cycle' in best:
            nm = {v: k for k, v in R.items()}
            for Z, q in zip(All, ph):
                if q > p and {i for i in range(I.n) if set(Y[i]) != set(Z[i])} <= loc:
                    C['    cycle raise: ' + NC.rsig(I, Y, Z, W, nm)] += 1; break
        if 'cycle+w' not in best and len(EX) < 5: EX.append((I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], [list(a) for a in Y]))
import sys as _s
rng = random.Random(int(_s.argv[1])); n = 0
fam = _s.argv[2]
while n < int(_s.argv[3]):
    I = adv_t3.make(rng) if fam == 't3' else adv_t.make(rng, int(fam))
    if I is None: continue
    n += 1; analyse(I, fam)
for k in sorted(C, key=lambda k: (-C[k] if 'cycle raise' in k else 0, k)):
    if 'cycle raise' not in k: print('%5d %s' % (C[k], k))
print('states with no raise among the six agents:', json.dumps(EX))
