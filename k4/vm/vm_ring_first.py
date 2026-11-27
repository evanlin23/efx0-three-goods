"""Ring-first normal form for the rotation class (k4/vm.md section 7.8).  For every rotation-class instance and every
V-M matching Y, search the F1 states X reachable from Y without rotation; for each envy cycle c_0 -> c_1 -> ... of X
(c_t envies c_{t+1} and takes its bundle), rotate it and ask whether F1 placements WITHOUT further rotation complete.
Reports, per instance:
  strict  - some such success where X differs from Y only on the cycle (off-cycle agents still hold their picks,
            i.e. only the ring's pool goods were placed before the rotation);
  any     - some success at all (one rotation, then plain placement);
  wants   - the least number of want arrows over the successful cycles (strict ones if any).
An arrow c_t -> c_{t+1} is a WANT arrow if c_{t+1} still holds its single pick, else a PAIR arrow.  EVIDENCE only.
    python3 k4/vm/vm_ring_first.py SOURCE"""
import sys, os, time, multiprocessing as mp
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm_extend import Enc
from vm_classify import classify, ORDER


def key(X):
    return tuple(tuple(sorted(b)) for b in X)


def valued_pool(I, X):
    held = set(g for b in X for g in b)
    return sorted(g for g in range(I.m) if g not in held and I.valued_by(g))


def completes_norot(I, X0, memo):
    """F1 placements without rotation complete X0 (memoized on the state)"""
    stack = [X0]; seen = set()
    while stack:
        X = stack.pop(); k = key(X)
        if k in seen: continue
        seen.add(k)
        if k in memo:
            if memo[k]: return True
            continue
        P = valued_pool(I, X)
        if not P:
            memo[k] = True
            return True
        for g in P:
            for s in range(I.n):
                if V.safe_add(I, X, s, g):
                    Z = [list(b) for b in X]; Z[s].append(g); stack.append(Z)
    for k in seen: memo[k] = False
    return False


def one(args):
    name, sets, vals, m = args
    I = V.Inst(sets, vals, m); E = Enc(sets, vals, m)
    if ORDER[classify(I, E)] != 'rotation': return None
    Ys = []
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if not isinstance(r, V.Stuck):
            Y = [list(b) for b in r[0]]
            if Y not in Ys: Ys.append(Y)
    memo = {}; best = {'strict': None, 'any': None}; nY = 0
    for Y in Ys:
        stack = [[list(b) for b in Y]]; seen = set(); okY = False
        while stack:
            X = stack.pop(); k = key(X)
            if k in seen: continue
            seen.add(k)
            G = nx.DiGraph(); G.add_nodes_from(range(I.n))
            Eg = V.envy_graph(I, X)
            for i in range(I.n):
                for j in Eg[i]: G.add_edge(i, j)
            for cyc in nx.simple_cycles(G):
                L = len(cyc)
                kinds = ['want' if sorted(X[cyc[(t + 1) % L]]) == sorted(Y[cyc[(t + 1) % L]]) else 'pair'
                         for t in range(L)]
                Z = [list(b) for b in X]
                for t, c in enumerate(cyc): Z[c] = list(X[cyc[(t + 1) % L]])
                if completes_norot(I, Z, memo):
                    okY = True
                    strict = all(sorted(X[j]) == sorted(Y[j]) for j in range(I.n) if j not in cyc)
                    shape = (kinds.count('want'), L, tuple(sorted(len(X[c]) - 1 for c in cyc)))
                    for tag in (['strict', 'any'] if strict else ['any']):
                        if best[tag] is None or shape < best[tag][0]:
                            best[tag] = (shape, [list(b) for b in X], cyc)
            for g in valued_pool(I, X):
                for s in range(I.n):
                    if V.safe_add(I, X, s, g):
                        Z = [list(b) for b in X]; Z[s].append(g); stack.append(Z)
        nY += okY
    return name, I.n, I.m, len(Ys), nY, best


if __name__ == '__main__':
    src = sys.argv[1]; print('$ python3 k4/vm/vm_ring_first.py', ' '.join(sys.argv[1:])); t0 = time.time()
    tot = strict = anyok = 0
    with mp.Pool(os.cpu_count()) as pool:
        for res in pool.imap_unordered(one, items_for(src), chunksize=2):
            if res is None: continue
            name, n, m, nYs, nY, best = res; tot += 1
            strict += best['strict'] is not None; anyok += best['any'] is not None
            fmt = lambda b: 'none' if b is None else 'wants=%d len=%d pool goods per holder %s; X=%s cycle=%s' % (
                b[0][0], b[0][1], b[0][2], b[1], b[2])
            print('  %s n=%d m=%d: V-M matchings %d, with a ring-first success %d' % (name, n, m, nYs, nY))
            print('      strict: %s' % fmt(best['strict']))
            print('      any:    %s' % fmt(best['any']))
    print('rotation-class instances %d; strict ring-first %d; one rotation then plain placement %d; time %d s'
          % (tot, strict, anyok, time.time() - t0))
