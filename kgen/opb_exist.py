"""Is "one pick per bundle" a possible target at n = 3?  For each start, by brute force over all 3^m allocations:
does an EFX0 allocation exist that is an OC1(t >= 0) completion of the picks (Lemma R) and puts exactly one pick in
each bundle?  And is there a partition satisfying AACGMM's invariants (X1, X2 EFX-feasible for agent 1, X3 for agent
2 or 3; kgen/n3.md §12) with one pick per bundle, for some assignment of the roles?  Same instances as kgen/aacgmm3.py.

    python3 kgen/opb_exist.py SEED N MMIN MMAX"""
import sys, itertools, collections, json
from lemmaT3 import reachable
from oc3lib import picks, ORD
from aacgmm3 import efx0, feasible
from aacgmm3_fail import instances

if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); C = collections.Counter(); shown = collections.Counter()
    print('$ python3 kgen/opb_exist.py', *sys.argv[1:], flush=True)
    for kind, raw, V in instances(seed, N, lo, hi):
        m = len(V[0])
        allX = [[{g for g in range(m) if q[g] == i} for i in range(3)] for q in itertools.product(range(3), repeat=m)]
        E = [X for X in allX if efx0(V, X)]
        for o in ORD:
            y = picks(V, o)
            if any(g is None for g in y): continue
            P = set(y); C[kind + ': starts'] += 1
            R = [X for X in E if reachable(V, y, X)]
            opb = [X for X in R if all(len(B & P) == 1 for B in X)]
            C[kind + ': OC1 completion exists'] += bool(R)
            C[kind + ': OC1 completion with one pick per bundle exists'] += bool(opb)
            inv = False
            for roles in ORD:
                A, B, Cc = roles
                for X in allX:
                    if all(len(Bd & P) == 1 for Bd in X):
                        for perm in itertools.permutations(range(3)):
                            Q = [X[perm[0]], X[perm[1]], X[perm[2]]]
                            if feasible(V[A], Q, 0) and feasible(V[A], Q, 1) and (feasible(V[B], Q, 2) or feasible(V[Cc], Q, 2)):
                                inv = True; break
                    if inv: break
                if inv: break
            C[kind + ': some role assignment has an OPB partition meeting the invariants'] += inv
            if R and not opb and shown[kind] < 3:
                shown[kind] += 1
                print('NO OPB OC1 COMPLETION', kind, json.dumps(raw), 'order', o, 'picks', y, 'an OC1 completion', [sorted(b) for b in R[0]], flush=True)
    for k in sorted(C): print(C[k], k)
