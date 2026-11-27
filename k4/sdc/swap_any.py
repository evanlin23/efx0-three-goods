"""One swap from a dangerous frozen agent (k4/sdc.md §30).  For every order whose picks have no one-absorber
completion: is there a frozen agent x valuing junk, an agent w that wants Y_x, and a set H_0 of goods of J + {Y_w}
valued by x with v_x(H_0) > v_x(Y_x), such that the swap (w takes Y_x, x takes H_0, the rest of Y_w becomes junk)
has a one-absorber completion?  Also: with H_0 restricted to minimal improving sets; with w's pick unwanted.

    python3 k4/sdc/swap_any.py screen|suite|special|logs|cores:FILES N SEED"""
import sys, os, json, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_orders import sd
from oc_absorb import extends_A
from min_frozen import load, nfrozen

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/swap_any.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 5: continue
        E = Enc(sets, vals, m); seen = set()
        val = lambda i, S: sum(E.v[i].get(g, 0) for g in S)
        for od in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(od))[0])
            if Y in seen: continue
            seen.add(Y)
            base = [-1] * m
            for i, g in enumerate(Y):
                if g is not None: base[g] = i
            if extends_A(E, tuple(base), 1): continue
            C['hard starts'] += 1
            F = nfrozen(E, Y); J = [g for g in range(m) if base[g] < 0]
            def wants(i, j):
                if Y[j] is None or i == j: return False
                if Y[i] is None: return E.v[i].get(Y[j], 0) > 0
                return E.v[i].get(Y[j], 0) > E.v[i][Y[i]]
            found = found_min = found_unw = False
            for x in F:
                if not any(E.v[x].get(g, 0) > 0 for g in J): continue
                for w in range(n):
                    if not wants(w, x): continue
                    pool = [g for g in J if E.v[x].get(g, 0) > 0] + ([Y[w]] if Y[w] is not None and E.v[x].get(Y[w], 0) > 0 else [])
                    imp = [H for r in range(1, len(pool) + 1) for H in itertools.combinations(pool, r) if val(x, H) > E.v[x][Y[x]]]
                    mins = [H for H in imp if not any(set(K) < set(H) for K in imp)]
                    for H0 in imp:
                        nb = list(base); nb[Y[x]] = w
                        if Y[w] is not None: nb[Y[w]] = -1
                        for g in H0: nb[g] = x
                        if extends_A(E, tuple(nb), 1):
                            found = True
                            if H0 in mins: found_min = True
                            if w not in F: found_unw = True
                if found_min and found_unw: break
            C['  some swap repairs'] += found
            C['  some swap with a minimal improving set repairs'] += found_min
            C["  some swap to a wanter whose pick is unwanted repairs"] += found_unw
            if not found and C['shown'] < 4:
                C['shown'] += 1; print('NO SWAP', name, json.dumps((sets, vals)), 'picks', Y, 'frozen', F, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
