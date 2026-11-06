"""Collect the hard one-frozen-agent starts (k4/sdc.md §30): orders whose picks have exactly one frozen agent x and
no one-absorber completion.  For each: |W|, x's type (3 or 4 goods; which pairs of its lower goods beat its top),
where x's lower goods are (junk / a wanter's pick / another pick), and for every wanter w and every minimal improving
H_0 within J + {Y_w}: which owners complete the swap (A = 1, absorber fixed).

    python3 k4/sdc/f1_collect.py cores:FILES N SEED"""
import sys, os, json, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_orders import sd
from oc_absorb import extends_A
from min_frozen import load, nfrozen
from f1_owner import absorber_ok

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/f1_collect.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 6: continue
        E = Enc(sets, vals, m); seen = set()
        val = lambda i, S: sum(E.v[i].get(g, 0) for g in S)
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
            R = sorted(E.R[x], key=lambda g: -E.v[x][g]); a = R[0]; low = R[1:]
            pairs = ''.join('1' if E.v[x][p] + E.v[x][q] > E.v[x][a] else '0' for p, q in itertools.combinations(low, 2))
            where = ''.join('J' if base[g] < 0 else ('w' if base[g] in W else 'p') for g in low)
            C['hard one-frozen starts'] += 1
            C['  |W|=%d, x has %d goods, pairs beating the top %s, lower goods %s' % (len(W), len(R), pairs, where)] += 1
            allw = True
            for w in W:
                pool = [g for g in J if E.v[x].get(g, 0) > 0] + ([Y[w]] if E.v[x].get(Y[w], 0) > 0 else [])
                imp = [H for r in range(1, len(pool) + 1) for H in itertools.combinations(pool, r) if val(x, H) > E.v[x][a]]
                mins = [H for H in imp if not any(set(K) < set(H) for K in imp)]
                okw = False
                for H0 in mins:
                    nb = list(base); nb[Y[x]] = w; nb[Y[w]] = -1
                    for g in H0: nb[g] = x
                    owners = [o for o in range(n) if absorber_ok(E, tuple(nb), o)]
                    others = [o for o in range(n) if o != x and o not in W]
                    if owners: okw = True
                    C['    swap (|W|=%d, |H0|=%d): some owner' % (len(W), len(H0))] += bool(owners)
                    C['    swap (|W|=%d, |H0|=%d): x owns' % (len(W), len(H0))] += x in owners
                    C['    swap (|W|=%d, |H0|=%d): every owner outside x+W' % (len(W), len(H0))] += bool(others) and all(o in owners for o in others)
                    C['    swap (|W|=%d, |H0|=%d): tried' % (len(W), len(H0))] += 1
                allw &= okw
            C['  every wanter has a repairing minimal swap'] += allw
            if not allw: print('NOT EVERY WANTER', name, json.dumps((sets, vals)), 'picks', Y, 'x', x, 'W', W, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
