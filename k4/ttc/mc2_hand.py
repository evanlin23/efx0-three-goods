"""Hand-made variants of the pigeonhole inside the K4.MC2 class (k4/ttc.md §13): three frozen 4-good agents i with
picks y_i, one private good a_i and one shared good b_i (shared with the next frozen agent), two pickless 3-good agents
on {y_0, y_1, y_2}.  Each frozen agent i values {y_i, a_i, b_i, z_i}, with z_i one of b_{i-1} (the previous pair's
shared good) or a_{i+1}/a_{i-1}, under a grid of values.  Reports, for each variant that is a strict connected core
with no agent holding two private goods, the serial-dictatorship outcomes on which OC1 fails (SAT, de_free moves).

    python3 k4/ttc/mc2_hand.py"""
import itertools, collections, json, sys, os
import ttclib as T
import core_climb as CC

Y, A, B = [0, 1, 2], [3, 4, 5], [6, 7, 8]

if __name__ == '__main__':
    C = collections.Counter(); found = []
    zs = {'b_prev': lambda i: B[(i - 1) % 3]}
    for zname, zf in zs.items():
        for vy, va, vb, vz in itertools.product([10, 12], [6, 7, 8], [4, 5, 6], [2, 3, 4, 5, 6, 7]):
            if not (va < vy and vb < vy and va + vb > vy and vz < vy):
                continue
            for p3, p4 in [((4, 3, 2), (2, 4, 3)), ((4, 3, 2), (3, 2, 4)), ((5, 4, 3), (3, 5, 4))]:
                sets = [[Y[i], A[i], B[i], zf(i)] for i in range(3)] + [list(Y), list(Y)]
                vals = [[vy, va, vb, vz]] * 3 + [list(p3), list(p4)]
                vals = [list(x) for x in vals]
                if not CC.is_core(sets, vals, 9) or CC.two_private(sets):
                    C['not an MC2 core'] += 1; continue
                C['MC2 cores'] += 1
                E = T.Enc(sets, vals, 9); fails = []; seen = set()
                for pi in itertools.permutations(range(5)):
                    Yp = tuple(T.sd(E, list(pi))[0])
                    if Yp in seen:
                        continue
                    seen.add(Yp); b = T.base_of(E, Yp)
                    if T.extends_A(E, b, 1):
                        continue
                    if not any(T.extends_A(E, b2, 1) for b2 in set(T.DF.moves(E, b))):
                        fails.append(Yp)
                if fails:
                    C['MC2 cores where OC1 fails'] += 1; found.append({'sets': sets, 'vals': vals, 'm': 9, 'picks': fails})
    print(dict(C))
    for f in found[:3]:
        print('OC1 FAILS', json.dumps(f))
