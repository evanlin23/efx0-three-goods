"""OC2^max at k = 4 fails at n = 10: two copies of the n = 5 OC1'-failure 5_pure idx 164 (k4/sdc/oc1prime_n5_cex.py)
glued at good 0 (in each copy valued only by agent 0, at 1, its lowest good).  The glued instance G is a strict
connected k = 4 core with MC2; the union of the copies' picks is the serial-dictatorship outcome of the concatenated
order and is a perfect matching.  Claim: no state reachable by at most two sequential official moves (k4/sdc.md §29)
has a one-absorber EFX0 completion, and three moves suffice.
Reason (checked here directly on G, not assumed): no move crosses copies (every base handed on is valued only inside
its copy; good 0 is worth 1 to the two agents 0 and less than any base), cross-copy EFX0 constraints are vacuous, and
copy A needs two moves (with good 0) while copy A minus good 0 needs one (k4/sdc/oc1prime_n5_cex.py's instance).
Direct check: every state within two moves of the picks (own move generator: Inst.moves's additions and chains, rings by
DFS), each tested for a one-absorber completion by exhaustive numpy enumeration of the junk assignments (raw EFX0,
zero-valued goods included in the removal test).  Then a three-move witness is built and checked.
    python3 k4/sdc/oc2max_glue_cex.py"""
import itertools, json, sys, time
import numpy as np
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
import oc1max_climb as C
from oc1_max_orders import nu

SETS = [[0, 2, 3, 7], [1, 2, 6, 7], [3, 4, 5, 6], [3, 4, 5, 7], [4, 5, 6, 7]]
VALS = [[1, 8, 6, 4], [4, 8, 2, 7], [6, 7, 3, 5], [7, 10, 2, 6], [7, 5, 3, 6]]
ORDER = (1, 4, 2, 0, 3)
# copy B: goods 1..7 -> 8..14, good 0 shared
mapB = {0: 0, **{g: g + 7 for g in range(1, 8)}}
GS = SETS + [[mapB[g] for g in s] for s in SETS]; GV = VALS + [list(v) for v in VALS]
G = Inst(GS, GV); n, m = G.n, G.m
GORDER = ORDER + tuple(5 + i for i in ORDER)
picks = G.sd(GORDER)
print('G sets', json.dumps(GS)); print('G vals', json.dumps(GV))
print('strict connected core:', C.is_core(GS, GV, False), '| MC2:', C.is_core(GS, GV, True), '| n, m =', n, m)
print('order', GORDER, 'picks', picks, '| perfect:', None not in picks, '| nu =', nu(G))
Vm = np.zeros((n, m), dtype=np.int64)
for i, (s, x) in enumerate(zip(GS, GV)):
    for g, y in zip(s, x): Vm[i, g] = y
BIG = 10 ** 9


def complete(base, absorbers=1):
    """exists an assignment of the junk with <= absorbers agents taking >= 2 junk goods, giving an EFX0 allocation"""
    J = [g for g in range(m) if all(g not in b for b in base)]
    r = len(J)
    if r == 0: return G.efx0(base)
    A = np.array(list(itertools.product(range(n), repeat=r)), dtype=np.int64)          # rows: agent of each junk good
    cnt = np.zeros((len(A), n), dtype=np.int64)
    for k in range(r): cnt[np.arange(len(A)), A[:, k]] += 1
    A = A[(cnt >= 2).sum(1) <= absorbers]
    # W[a, i, j] = v_i(bundle j), M[a, i, j] = min_{h in bundle j} v_i(h) (BIG for an empty bundle)
    W0 = np.array([[Vm[i, base[j]].sum() if base[j] else 0 for j in range(n)] for i in range(n)])
    M0 = np.array([[Vm[i, base[j]].min() if base[j] else BIG for j in range(n)] for i in range(n)])
    W = np.repeat(W0[None], len(A), 0); M = np.repeat(M0[None], len(A), 0); nonempty = np.array([bool(b) for b in base])
    NE = np.repeat(nonempty[None], len(A), 0)
    rows = np.arange(len(A))
    for k, g in enumerate(J):
        j = A[:, k]
        W[rows, :, j] += Vm[:, g][None, :]
        M[rows, :, j] = np.minimum(M[rows, :, j], Vm[:, g][None, :])
        NE[rows, j] = True
    own = W[:, np.arange(n), np.arange(n)]                                               # [a, i]
    viol = (W - M > own[:, :, None]) & NE[:, None, :]
    viol[:, np.arange(n), np.arange(n)] = False
    return bool((~viol.any(axis=(1, 2))).any())


def moves(base):
    """Inst.moves with rings by DFS (same move set: every cycle with every predecessor base nonempty and each agent
    gaining with its predecessor's base plus junk it values)"""
    R, V = G.R, G.V
    J = [g for g in range(m) if all(g not in b for b in base)]
    sub = lambda xs: itertools.chain.from_iterable(itertools.combinations(xs, r) for r in range(len(xs) + 1))
    res = set(); key = lambda nb: tuple(tuple(sorted(b)) for b in nb)
    saved = G.n
    out = set()
    # additions and chains: reuse Inst.moves's code path minus rings, by calling it on a copy whose ring loop is empty
    for x in range(n):
        for H in sub([g for g in J if g in R[x]]):
            if H:
                nb = [list(b) for b in base]; nb[x] = list(base[x]) + list(H); out.add(key(nb))

    def ext(path, used, assign):
        xt = path[-1]
        if len(path) >= 2:
            pool = [g for g in J if g not in used and g in R[path[0]]] + [g for g in base[xt] if g in R[path[0]]]
            for H0 in sub(pool):
                if H0 and V(path[0], H0) > V(path[0], base[path[0]]):
                    nb = [list(b) for b in base]; nb[path[0]] = list(H0)
                    for i in range(1, len(path)): nb[path[i]] = list(base[path[i - 1]]) + list(assign[i])
                    out.add(key(nb))
        if len(path) >= n or not base[xt]: return
        for y in range(n):
            if y in path: continue
            for H in sub([g for g in J if g not in used and g in R[y]]):
                if V(y, list(base[xt]) + list(H)) > V(y, base[y]):
                    ext(path + [y], used | set(H), {**assign, len(path): H})
    for x in range(n): ext([x], frozenset(), {})

    def ring(cyc, used, assign):
        # cyc[0] = min; extend by w receiving base[cyc[-1]]; close when cyc[0] receives base[cyc[-1]]
        last = cyc[-1]
        if not base[last]: return
        s = cyc[0]
        if len(cyc) >= 2:     # close: s receives base[last] + junk
            for H in sub([g for g in J if g not in used and g in R[s]]):
                if V(s, list(base[last]) + list(H)) > V(s, base[s]):
                    nb = [list(b) for b in base]
                    nb[s] = list(base[last]) + list(H)
                    for t in range(1, len(cyc)): nb[cyc[t]] = list(base[cyc[t - 1]]) + list(assign[t])
                    out.add(key(nb))
        for w in range(s + 1, n):
            if w in cyc: continue
            for H in sub([g for g in J if g not in used and g in R[w]]):
                if V(w, list(base[last]) + list(H)) > V(w, base[w]):
                    ring(cyc + [w], used | set(H), {**assign, len(cyc): H})
    for s in range(n): ring([s], frozenset(), {})
    return out


if __name__ == '__main__':
    t0 = time.time()
    # sanity: the DFS move generator equals Inst.moves on the n = 5 instance at its picks and at its one-move states
    I5 = Inst(SETS, VALS); p5 = I5.sd(ORDER)
    G_saved = G
    globals()['G'] = I5; globals()['n'], globals()['m'] = I5.n, I5.m
    b5 = [[g] for g in p5]; ok = moves(b5) == I5.moves(b5)
    for st in list(I5.moves(b5))[:10]: ok &= moves([list(b) for b in st]) == I5.moves([list(b) for b in st])
    globals()['G'] = G_saved; globals()['n'], globals()['m'] = G_saved.n, G_saved.m
    print('DFS move generator equals Inst.moves on the n = 5 instance (picks and 10 one-move states):', ok, flush=True)
    base = [[g] for g in picks]
    key = lambda s: tuple(tuple(sorted(b)) for b in s)
    L0 = {key(base)}; L1 = set(); L2 = set()
    for s in L0: L1 |= moves([list(b) for b in s])
    L1 -= L0
    for s in L1: L2 |= moves([list(b) for b in s])
    L2 -= L1 | L0
    print('states: picks 1, after one move', len(L1), ', new after two moves', len(L2), '%.0f s' % (time.time() - t0), flush=True)
    bad = 0
    for d, L in ((0, L0), (1, L1), (2, L2)):
        c = sum(complete([list(b) for b in s]) for s in L)
        print('depth', d, ': states with a one-absorber completion:', c, 'of', len(L), '%.0f s' % (time.time() - t0), flush=True)
        bad += c
    print('OC2^max at this start:', 'HOLDS' if bad else 'FAILS (no state within two moves completes)')
    # three-move witness: copy A by two moves to the MD allocation's bases, copy B (good 0 given to copy A) by one
    found = None
    for s in L2:
        for t in moves([list(b) for b in s]):
            if complete([list(b) for b in t]): found = (s, t); break
        if found: break
    print('three moves suffice:', found is not None, json.dumps(found) if found else '', '%.0f s' % (time.time() - t0))
