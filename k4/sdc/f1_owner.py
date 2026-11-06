"""The swap of the one-frozen-agent case, in detail (k4/sdc.md §30).  For every order whose picks have exactly one
frozen agent x and no one-absorber completion: for every wanter w, the full swap (w takes Y_x; x takes every good of
J + {Y_w} it values) and, for every owner o, whether a completion exists in which o is the only agent receiving two or
more junk goods (A = 1 with the absorber fixed to o; or no absorber).  Classified by |W| and |H_0|.

    python3 k4/sdc/f1_owner.py screen|suite|logs|cores:FILES N SEED"""
import sys, os, json, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_orders import sd
from oc_absorb import extends_A
from min_frozen import load, nfrozen
from pysat.solvers import Cadical153


def absorber_ok(E, base, o):
    J = [g for g in range(E.m) if base[g] < 0]
    cl = list(E.cl)
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
        if base[g] >= 0: cl.append([E.x[g][base[g]]])
    for i in range(E.n):
        if i == o: continue
        for g, h in itertools.combinations(J, 2): cl.append([-E.x[g][i], -E.x[h][i]])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/f1_owner.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 6: continue
        E = Enc(sets, vals, m); seen = set()
        for od in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(od))[0])
            if Y in seen: continue
            seen.add(Y)
            F = nfrozen(E, Y)
            if len(F) != 1: continue
            x = F[0]
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            if extends_A(E, tuple(base), 1): continue
            J = [g for g in range(m) if base[g] < 0]
            W = [w for w in range(n) if w != x and Y[w] is not None and E.v[w].get(Y[x], 0) > E.v[w][Y[w]]]
            for w in W:
                H0 = [g for g in J if E.v[x].get(g, 0) > 0] + ([Y[w]] if E.v[x].get(Y[w], 0) > 0 else [])
                key = '|W|=%d |H0|=%d' % (len(W), len(H0))
                C[key + ': swaps'] += 1
                nb = list(base); nb[Y[x]] = w; nb[Y[w]] = -1
                for g in H0: nb[g] = x
                nb = tuple(nb)
                if sum(E.v[x][g] for g in H0) <= E.v[x][Y[x]]: C[key + ': x does not gain'] += 1; continue
                good = [o for o in range(n) if absorber_ok(E, nb, o)]
                others = [o for o in range(n) if o != x and o not in W]
                C[key + ': some owner works'] += bool(good)
                C[key + ': every owner outside {x} + W works'] += bool(others) and all(o in good for o in others)
                C[key + ': x can own'] += x in good
                C[key + ': w can own'] += w in good
                if not good: print('SWAP FAILS', name, json.dumps((sets, vals)), 'picks', Y, 'x', x, 'w', w, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
