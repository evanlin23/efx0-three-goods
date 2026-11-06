"""Exactly one frozen agent (k4/sdc.md §30).  For every order whose picks Y have exactly one frozen agent x (some agents
W want Y_x; nobody wants any other pick), test:
  (A) a one-absorber completion of Y exists;
  (B) for some w in W and some H_0 subset of J + {Y_w} relevant to x with v_x(H_0) > v_x(Y_x), the swap
      (w takes Y_x, x takes H_0, Y_w minus H_0 becomes junk) has a one-absorber completion.
Also records |W| and whether every w in W works with x's best H_0.

    python3 k4/sdc/f1_swap.py screen|suite|special|logs|cores:FILES N SEED"""
import sys, os, json, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_orders import sd
from oc_absorb import extends_A
from min_frozen import load, nfrozen

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/f1_swap.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 6: continue
        E = Enc(sets, vals, m); seen = set()
        val = lambda i, S: sum(E.v[i].get(g, 0) for g in S)
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(o))[0])
            if Y in seen: continue
            seen.add(Y)
            F = nfrozen(E, Y)
            if len(F) != 1: continue
            x = F[0]; C['outcomes with one frozen agent'] += 1
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            if extends_A(E, tuple(base), 1): C['  (A) completion without a chain'] += 1; continue
            J = [g for g in range(m) if base[g] < 0]
            W = [w for w in range(n) if w != x and Y[w] is not None and E.v[w].get(Y[x], 0) > E.v[w][Y[w]]] + \
                [w for w in range(n) if w != x and Y[w] is None and E.v[w].get(Y[x], 0) > 0]
            C['  needs a chain'] += 1; C['  needs a chain, |W| = %d' % len(W)] += 1
            okw = {}
            for w in W:
                pool = [g for g in J if E.v[x].get(g, 0) > 0] + ([Y[w]] if Y[w] is not None and E.v[x].get(Y[w], 0) > 0 else [])
                res = []
                for r in range(1, len(pool) + 1):
                    for H0 in itertools.combinations(pool, r):
                        if val(x, H0) <= E.v[x][Y[x]]: continue
                        nb = list(base); nb[Y[x]] = w
                        if Y[w] is not None: nb[Y[w]] = -1
                        for g in H0: nb[g] = x
                        res.append((val(x, H0), extends_A(E, tuple(nb), 1)))
                okw[w] = res
            some = any(ok for w in W for _, ok in okw[w])
            C['  (B) some swap repairs'] += some
            C['  (B) every wanter has a repairing swap'] += all(any(ok for _, ok in okw[w]) for w in W if okw[w])
            bestall = all(max(okw[w])[1] for w in W if okw[w])
            C["  (B) every wanter repairs with x's best H_0"] += bestall
            if not some: print('F1 SWAP FAILS', name, json.dumps((sets, vals)), 'picks', Y, 'x', x, 'W', W, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
