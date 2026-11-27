"""For the instances of SOURCE that need a move under VM1-plain (k4/vm.md section 7.8): every move from a V-M matching
after which F1 placements without rotation complete, classified as an upgrade (with |S|) or an exchange (z valued or
worthless to the taker i, with |S|), next to the instance's repair class (vm_classify).  EVIDENCE only.
    python3 k4/vm/vm1_plain_moves.py SOURCE"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
import vmx2_phases as P
from vm_test import items_for
import vm1_plain as Q
from vm_classify import classify, ORDER
from vm_extend import Enc

if __name__ == '__main__':
    src = sys.argv[1]; print('$ python3 k4/vm/vm1_plain_moves.py', src)
    C = collections.Counter()
    for name, sets, vals, m in items_for(src):
        I = V.Inst(sets, vals, m); memo = {}
        Ys = Q.vm_matchings(I)
        if any(Q.completes_norot(I, [list(b) for b in Y], memo) for Y in Ys): continue
        V.FREE_Z[0] = False; cls = ORDER[classify(I, Enc(sets, vals, m))]; V.FREE_Z[0] = True
        kinds = set()
        for Y in Ys:
            pool = set(range(m)) - set(g for b in Y for g in b)
            for mv in V.exchanges(I, Y, pool):
                Z, _ = P.apply_move(Y, pool, mv)
                if Q.completes_norot(I, Z, memo):
                    i, j, z, S = mv
                    kinds.add(('upgrade', len(S)) if j is None else
                              ('exchange', 'z valued' if z in I.v[i] else 'z worthless', len(S)))
        print(' ', name, cls, sorted(kinds, key=str), flush=True)
        for k in kinds: C[(cls,) + k] += 1
    print('(class, move, |S|): instances with such a completing move')
    for k, c in sorted(C.items(), key=str): print('  ', c, k)
