"""Hand-made attempt against OC1^max (k4/ttc.md §13): the MC2-class counterexample of attempts/k4-ttc-oc-every-order.md
with the two pickless agents given a private fourth good c_j of the lowest value, so that the order (0, 1, 2, 3, 4)
matches every agent (a maximum matching) while agents 3 and 4 still want the y_i.  Values of agents 3, 4: every
strict balanced 4-good type of de4lib (TYPES[4]) with c_j ranked last.  Reports which variants are strict connected
cores in the K4.MC2 class, and on them: OC1 and OC (free completion) for every maximum-matching order, and for every
R1-priority order.

    python3 k4/ttc/max_hand.py"""
import itertools, collections, json, os
import ttclib as T
import core_climb as CC
_cwd = os.getcwd(); os.chdir(T._paths.DE4)
from de4lib import TYPES
os.chdir(_cwd)

if __name__ == '__main__':
    Y, A, B, Cg = [0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10]
    base_sets = [[Y[i], A[i], B[i], B[(i - 1) % 3]] for i in range(3)]
    base_vals = [[10, 6, 5, 7]] * 3
    C = collections.Counter(); found = []
    types = [sorted(t, reverse=True) for t in TYPES[4]]
    for t3, t4 in itertools.product(types, repeat=2):
        for perm3 in itertools.permutations([0, 1, 2]):
            for perm4 in [(1, 2, 0), (2, 0, 1)]:
                # agent j ranks y's by the permutation, c_j last
                v3 = [0, 0, 0]; v4 = [0, 0, 0]
                for r, i in enumerate(perm3): v3[i] = t3[r]
                for r, i in enumerate(perm4): v4[i] = t4[r]
                sets = [list(s) for s in base_sets] + [Y + [Cg[0]], Y + [Cg[1]]]
                vals = [list(v) for v in base_vals] + [v3 + [t3[3]], v4 + [t4[3]]]
                m = 11
                if not CC.is_core(sets, vals, m) or CC.two_private(sets):
                    C['not an MC2 core'] += 1; continue
                C['MC2 cores'] += 1
                E = T.Enc(sets, vals, m); nu = CC.nu(sets); res = {}
                for pi in itertools.permutations(range(5)):
                    for r1 in (False, True):
                        Yp = tuple(T.sd(E, list(pi), r1)[0])
                        key = (Yp, r1)
                        if key in res: continue
                        is_max = sum(1 for y in Yp if y is not None) == nu
                        b = T.base_of(E, Yp)
                        if T.extends_A(E, b, 1): res[key] = (is_max, True, True); continue
                        mv = set(T.DF.moves(E, b))
                        res[key] = (is_max, any(T.extends_A(E, x, 1) for x in mv),
                                    T.DF.extends(E, b) or any(T.DF.extends(E, x) for x in mv))
                fmax = [k for k, v in res.items() if not k[1] and v[0] and not v[1]]
                fmaxoc = [k for k, v in res.items() if not k[1] and v[0] and not v[2]]
                fr1 = [k for k, v in res.items() if k[1] and not v[1]]
                C['OC1^max fails'] += bool(fmax); C['OC^max fails'] += bool(fmaxoc); C['OC1 fails for an R1 order'] += bool(fr1)
                if (fmax or fr1) and len(found) < 4:
                    found.append({'sets': sets, 'vals': vals, 'm': m, 'OC1^max fails at': [k[0] for k in fmax],
                                  'OC^max fails at': [k[0] for k in fmaxoc], 'R1 fails at': [k[0] for k in fr1]})
            if C['MC2 cores'] >= 60: break
        if C['MC2 cores'] >= 60: break
    print(dict(C))
    for f in found:
        print('FOUND', json.dumps(f))
