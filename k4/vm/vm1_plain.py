"""Conjecture VM1-plain (k4/vm.md section 7.8): from some V-M matching Y, at most ONE trade, then F1 placements with NO
rotation, give a complete EFX0 allocation.  A trade is
  - a chain move: a pool upgrade or an unrestricted two-agent exchange applied to Y (vmlib.exchanges, FREE_Z), or
  - a ring trade: an envy cycle of an F1 state X reached from Y without rotation, in which every agent off the cycle
    still holds its pick (only the ring's pool goods were placed), rotated.
Per instance, the first level that works: 'plain' (no trade), 'move', 'ring', or FAIL.  EVIDENCE only.
    python3 k4/vm/vm1_plain.py SOURCE"""
import sys, os, time, collections, multiprocessing as mp
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
import vmx2_phases as P
from vm_test import items_for
from vm_ring_first import key, valued_pool


V.FREE_Z[0] = True


def completes_norot(I, X0, memo):
    """F1 placements without rotation complete X0 (memoized).  At the end the junk (goods nobody values) must go to
    an agent nobody envies (L3 without rotation), and the final allocation is re-checked with the raw EFX0 test."""
    stack = [X0]; seen = set()
    while stack:
        X = stack.pop(); k = key(X)
        if k in seen: continue
        seen.add(k)
        if k in memo:
            if memo[k]: return True
            continue
        Pv = valued_pool(I, X)
        if not Pv:
            held = set(g for b in X for g in b); J = [g for g in range(I.m) if g not in held]
            Eg = V.envy_graph(I, X); envied = set(j for i in range(I.n) for j in Eg[i])
            src = [s for s in range(I.n) if s not in envied]
            if src:
                F = [list(b) for b in X]; F[src[0]] += J
                assert V.is_efx0(I, F) and sorted(g for b in F for g in b) == list(range(I.m)), F
                memo[k] = True
                return True
            continue
        for g in Pv:
            for s in range(I.n):
                if V.safe_add(I, X, s, g):
                    Z = [list(b) for b in X]; Z[s].append(g); stack.append(Z)
    for k in seen: memo[k] = False
    return False


def vm_matchings(I):
    Ys = []
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if not isinstance(r, V.Stuck):
            Y = [list(b) for b in r[0]]
            if Y not in Ys: Ys.append(Y)
    return Ys


def ring_trades(I, Y):
    """states after one ring trade from Y (strict ring-first form)"""
    stack = [[list(b) for b in Y]]; seen = set()
    while stack:
        X = stack.pop(); k = key(X)
        if k in seen: continue
        seen.add(k)
        G = nx.DiGraph(); G.add_nodes_from(range(I.n)); Eg = V.envy_graph(I, X)
        for i in range(I.n):
            for j in Eg[i]: G.add_edge(i, j)
        for cyc in nx.simple_cycles(G):
            if all(sorted(X[j]) == sorted(Y[j]) for j in range(I.n) if j not in cyc):
                Z = [list(b) for b in X]; L = len(cyc)
                for t, c in enumerate(cyc): Z[c] = list(X[cyc[(t + 1) % L]])
                yield Z, cyc, X
        # only grow bundles of agents that could lie on a ring: any agent (the cycle is checked at the end)
        for g in valued_pool(I, X):
            for s in range(I.n):
                if V.safe_add(I, X, s, g):
                    Z = [list(b) for b in X]; Z[s].append(g); stack.append(Z)


def one(args):
    name, sets, vals, m = args
    I = V.Inst(sets, vals, m); memo = {}
    Ys = vm_matchings(I)
    for Y in Ys:
        if completes_norot(I, [list(b) for b in Y], memo): return name, I.n, I.m, 'plain', None
    for Y in Ys:
        pool = set(range(m)) - set(g for b in Y for g in b)
        for mv in V.exchanges(I, Y, pool):
            Z, _ = P.apply_move(Y, pool, mv)
            if completes_norot(I, Z, memo): return name, I.n, I.m, 'move', (Y, mv)
    for Y in Ys:
        for Z, cyc, X in ring_trades(I, Y):
            if completes_norot(I, Z, memo): return name, I.n, I.m, 'ring', (Y, X, cyc)
    return name, I.n, I.m, 'FAIL', Ys


if __name__ == '__main__':
    src = sys.argv[1]; print('$ python3 k4/vm/vm1_plain.py', ' '.join(sys.argv[1:])); t0 = time.time()
    C = collections.Counter()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, lev, info in pool.imap_unordered(one, items_for(src), chunksize=4):
            C[lev] += 1
            if lev in ('ring', 'FAIL'):
                print('  %s %s n=%d m=%d %s' % (lev, name, n, m, info), flush=True)
    print('levels:', dict(C), '; time %d s' % (time.time() - t0))
