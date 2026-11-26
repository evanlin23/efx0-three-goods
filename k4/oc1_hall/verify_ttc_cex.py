"""Independent check of the TTC session's OC1 counterexamples (claude/k4-ttc, attempts/k4-ttc-oc1-counterexample.md;
k4/oc1_hall.md §16), with this workstream's code: ohlib's raw brute force, k4/sdc/oc_absorb.extends_A (SAT), and
de_free's moves (chains and rings, |H| <= 4).  Instances inline:
  A: the first instance (n = 6, m = 10, agent 4 top-heavy, so not a core);
  B: instance 36 of their list, a connected core (agents 1 and 3 with two private goods), and its two strict
     perturbations B< and B> (agent 2's tie v(2) + v(3) = v(9) broken either way).
For each: the picks of the given order, the one-absorber test (SAT and brute force), the free completion, one chain or
ring, OC1^p (agents without a pick unrestricted), and, for B, the number of orders violating OC1.

    python3 k4/oc1_hall/verify_ttc_cex.py
"""
import sys, os, itertools, collections, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, base_of_picks, absorb_brute, efx0
from sdclib import Enc, decode
from oc_absorb import extends_A
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
import de_free as DF
DF.CHAIN_ONLY = False

A = ([[0,2,3,1],[1,4,5,9],[1,2,0,8],[1,6,7,8],[3,6,9],[1,3,6,9]], [[2,7,8,3],[3,6,4,9],[12,2,4,8],[12,6,3,4],[7,2,10],[7,8,4,1]])
B = ([[0,2,3,1],[6,4,5,9],[1,2,3,9],[1,6,7,8],[3,6,9],[1,3,6,9]], [[3,7,8,6],[2,9,6,14],[14,2,8,10],[8,7,6,3],[14,4,12],[10,15,4,2]])
Bl = (B[0], [[6,14,16,12],[4,18,12,28],[28,4,16,21],[16,14,12,6],[28,8,24],[20,30,8,4]])
Bg = (B[0], [[6,14,16,12],[4,18,12,28],[28,4,16,19],[16,14,12,6],[28,8,24],[20,30,8,4]])


def extends_p(E, base, Y):
    """one absorber among the agents holding a pick; agents without a pick unrestricted"""
    cl = list(E.cl); top = E.top; J = [g for g in range(E.m) if base[g] < 0]
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
        if base[g] >= 0: cl.append([E.x[g][base[g]]])
    bigs = []
    for i in range(E.n):
        if Y[i] is None: continue
        top += 1; b = top; bigs.append(b)
        for g, h in itertools.combinations(J, 2): cl.append([-E.x[g][i], -E.x[h][i], b])
    cl.extend(CardEnc.atmost(lits=bigs, bound=1, top_id=top, encoding=EncType.seqcounter).clauses)
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); mdl = S.get_model() if ok else None; S.delete(); return ok, mdl


if __name__ == '__main__':
    print('$ python3 k4/oc1_hall/verify_ttc_cex.py')
    for tag, (sets, vals) in [('A', A), ('B', B), ('B<', Bl), ('B>', Bg)]:
        I = Inst(sets, vals, 10); E = Enc(sets, vals, 10)
        Y = picks(I, range(6)); b = base_of_picks(I, Y)
        moves = DF.moves(E, b)
        okp, mdl = extends_p(E, b, Y)
        Xp = None
        if okp:
            asg = decode(E, mdl); Xp = [[g for g in range(10) if asg[g] == i] for i in range(6)]
        print(tag, json.dumps((sets, vals)))
        print('   order 0..5, picks', Y, '| one-absorber: SAT', extends_A(E, b, 1), 'brute', sorted(absorb_brute(I, b)),
              '| free completion', DF.extends(E, b), '| states after one chain or ring:', len(moves),
              'repaired', sum(1 for b2 in moves if extends_A(E, b2, 1)))
        print('   OC1^p at the picks:', okp, Xp, 'raw EFX0:', efx0(I, Xp) if Xp else None)
        if tag != 'A':
            C = collections.Counter()
            for od in itertools.permutations(range(6)):
                Yo = picks(I, od); bo = base_of_picks(I, Yo)
                if extends_A(E, bo, 1): C['picks complete'] += 1; continue
                C['one chain or ring repairs' if any(extends_A(E, b2, 1) for b2 in DF.moves(E, bo)) else 'OC1 fails'] += 1
            print('   orders:', dict(C))
