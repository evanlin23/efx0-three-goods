"""For instances with few extendable SD outcomes: which simple rule selects an extendable one?"""
import sys, json, itertools, collections
from sdclib import Enc
from sdc_orders import sd, completable
def outcomes(E, r1):
    res = {}
    for order in itertools.permutations(range(E.n)):
        Y, J = sd(E, order, r1)
        res.setdefault(tuple(Y), order)
    return res
def feats(E, Y):
    n = E.n
    def rank(i, g):
        if g is None: return 9
        return sorted(E.R[i], key=lambda h: (-E.v[i][h], h)).index(g)
    held = set(g for g in Y if g is not None)
    wanted = set()
    for i in range(n):
        vy = E.v[i][Y[i]] if Y[i] is not None else 0
        for g in E.R[i]:
            if g != Y[i] and E.v[i][g] > vy: wanted.add(g)
    unw = sum(1 for i in range(n) if Y[i] is not None and Y[i] not in wanted)
    tops = sum(1 for i in range(n) if rank(i, Y[i]) == 0)
    return dict(matched=len(held), unwanted=unw, tops=tops, rksum=sum(rank(i, Y[i]) for i in range(n)),
                valsum=sum(E.v[i].get(Y[i], 0) for i in range(n) if Y[i] is not None),
                leximin=tuple(sorted(-rank(i, Y[i]) for i in range(n))))
if __name__ == '__main__':
    C = collections.Counter(); N = 0
    for line in open(sys.argv[1]):
        if 'inst' not in line: continue
        sets, vals = json.loads(line.split('inst ', 1)[1].rsplit(' time', 1)[0])
        m = 1 + max(max(s) for s in sets); E = Enc(sets, vals, m)
        outs = outcomes(E, sys.argv[2] == 'r1')
        ext = {Y for Y in outs if completable(E, list(Y))}
        if len(outs) < 2: continue
        N += 1
        F = {Y: feats(E, list(Y)) for Y in outs}
        for key, sign in [('matched', 1), ('matched', -1), ('unwanted', 1), ('unwanted', -1), ('tops', 1), ('tops', -1),
                          ('rksum', -1), ('rksum', 1), ('valsum', 1), ('valsum', -1)]:
            best = max(sign * F[Y][key] for Y in outs)
            sel = [Y for Y in outs if sign * F[Y][key] == best]
            C[(key, sign, 'all-selected-extend')] += all(Y in ext for Y in sel)
            C[(key, sign, 'some-selected-extends')] += any(Y in ext for Y in sel)
        C['frac_ext'] += len(ext) / len(outs)
    print('instances with >= 2 SD outcomes', N)
    for k in sorted(C, key=str): print(k, C[k])
