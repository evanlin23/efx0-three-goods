"""Lemma MAX (k4/oc1_hall.md §19) and OC1 on maximum-matching orders.  For an instance: the maximum matching size nu
of the agent-good relevance graph; for every order, whether its picks are a maximum matching (as many agents with a
pick as nu); Lemma MAX's conclusion at such picks (no agent reachable from a pickless agent by an alternating path
values a junk good; in particular no pickless agent wants a dangerous agent or an agent above one); and OC1
(one-absorber completion at the picks or after one chain or ring).

    python3 k4/oc1_hall/max_matching.py SRC   (SRC: 'mc2' for the TTC K4.MC2-class core, or a k4/sdc data set)
"""
import sys, os, itertools, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks
from lemma2_true_check import max_matching
from sdclib import Enc
from oc_absorb import extends_A
from min_frozen import load
import de_free as DF
DF.CHAIN_ONLY = False


def nu(I):
    return len(max_matching({i: sorted(I.R[i]) for i in range(I.n)}, list(range(I.n))))


def lemma_max(I, P):
    """agents reachable from pickless agents by alternating paths; True iff none values a junk good"""
    Y = P.Y; holder = {y: i for i, y in enumerate(Y) if y is not None}
    reach = set(); st = [i for i in range(I.n) if Y[i] is None]
    while st:
        u = st.pop()
        for g in I.R[u]:
            j = holder.get(g)
            if j is not None and j not in reach: reach.add(j); st.append(j)
    return all(not P.Jv[j] for j in reach), reach


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/oc1_hall/max_matching.py', *sys.argv[1:], flush=True)
    items = ([('mc2-core', [[0,3,6,8],[1,4,7,6],[2,5,8,7],[0,1,2],[0,1,2]], [[10,6,5,7],[10,6,5,7],[10,6,5,7],[4,3,2],[2,4,3]], 9)]
             if src == 'mc2' else load(src, sys.argv))
    for name, sets, vals, m in items:
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); N = nu(I); seen = {}
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y not in seen:
                P = Picks(I, Y); mx = sum(1 for y in Y if y is not None) == N
                ok_lemma = lemma_max(I, P)[0] if mx else None
                b = base_of_picks(I, Y)
                oc1 = extends_A(E, b, 1) or any(extends_A(E, b2, 1) for b2 in DF.moves(E, b))
                seen[Y] = (mx, ok_lemma, oc1)
            mx, ok_lemma, oc1 = seen[Y]
            C['orders, picks %s' % ('maximum' if mx else 'not maximum')] += 1
            if mx:
                C['  maximum: Lemma MAX conclusion %s' % ok_lemma] += 1
                C['  maximum: OC1 %s' % oc1] += 1
                if not oc1: print('OC1 FAILS AT A MAXIMUM-MATCHING ORDER', name, json.dumps((sets, vals)), od, Y, flush=True)
            else:
                C['  not maximum: OC1 %s' % oc1] += 1
    for k in sorted(C): print(k, C[k])
