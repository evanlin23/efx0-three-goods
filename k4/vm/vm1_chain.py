"""Conjecture VM1-chain (k4/vm.md section 7.7): VM1 with DE's chains (paper/k3-simple, Lemma chain) as moves.  From
some V-M matching Y, at most ONE trade, then F1 placements with rotation (vm1_fast.complete).  A trade is a VM1 move
(a pool upgrade or an unrestricted two-agent exchange) or a chain:
  an agent x holding a single good upgrades to a pool set S (v_x(S) > v_x(y_x)), releasing y_x; then, as long as one
  wishes, an agent j holding a single good y_j that it values below the released good g takes g, releasing y_j.
Only the state after the whole chain must be EFX0 (as in DE, where a chain is applied at once).
Reports per instance: 'VM1' (no trade or one VM1 move suffices), 'chain', or FAIL.  EVIDENCE only.
    python3 k4/vm/vm1_chain.py SOURCE        (a vm_test source, or json:FILE with one JSON instance per line)"""
import sys, os, json, time, itertools, collections, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
import vm1_fast as F
from vm_test import items_for

CAP = 2000


def matchings(I):
    Ys = []
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if not isinstance(r, V.Stuck):
            Y = [list(b) for b in r[0]]
            if Y not in Ys: Ys.append(Y)
    return Ys


def chains(I, Y):
    """every state reached from the one-good matching Y by one chain (final state EFX0)"""
    n = I.n; out = []; seen = set()
    pool0 = set(range(I.m)) - set(g for b in Y for g in b)
    for x in range(n):
        if len(Y[x]) != 1: continue
        y = Y[x][0]; vy = I.v[x].get(y, 0)
        mine = sorted(g for g in pool0 if g in I.v[x])
        for r in range(1, len(mine) + 1):
            for S in itertools.combinations(mine, r):
                if I.val(x, S) <= vy: continue
                X = [list(b) for b in Y]; X[x] = list(S); pool = (pool0 - set(S)) | {y}
                stack = [(X, pool, y, {x})]
                while stack:
                    X, pool, g, used = stack.pop()
                    k = (tuple(tuple(sorted(b)) for b in X), g)
                    if k in seen: continue
                    seen.add(k)
                    if V.is_efx0(I, X): out.append((X, pool))
                    for j in range(n):
                        if j in used or len(X[j]) != 1: continue
                        yj = X[j][0]
                        if I.v[j].get(g, 0) > I.v[j].get(yj, 0):
                            Z = [list(b) for b in X]; Z[j] = [g]
                            stack.append((Z, (pool - {g}) | {yj}, yj, used | {j}))
    return out


def one(args):
    name, sets, vals, m = args
    I = V.Inst(sets, vals, m); t = time.time()
    if F.vm1(I, CAP) is not None or F.vm1(I, 50 * CAP) is not None:
        return name, I.n, I.m, 'VM1', None, time.time() - t
    for Y in matchings(I):
        for X, pool in chains(I, Y):
            Z = F.complete(I, X, pool, 50 * CAP)
            if Z is not None:
                assert V.is_efx0(I, Z) and sorted(g for b in Z for g in b) == list(range(I.m))
                return name, I.n, I.m, 'chain', Z, time.time() - t
    return name, I.n, I.m, 'FAIL', json.dumps({'sets': sets, 'vals': vals, 'm': m}), time.time() - t


def items(src):
    if src.startswith('json:'):
        out = []
        for k, line in enumerate(open(src[5:])):
            line = line.strip()
            if not line: continue
            nm, _, js = line.partition('\t') if '\t' in line else ('json#%d' % k, '', line)
            J = json.loads(js); out.append((nm, J['sets'], J['vals'], J['m']))
        return out
    return items_for(src)


if __name__ == '__main__':
    src = sys.argv[1]; print('$ python3 k4/vm/vm1_chain.py', src); t0 = time.time()
    C = collections.Counter()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, lev, info, dt in pool.imap_unordered(one, items(src), chunksize=1):
            C[lev] += 1
            if lev != 'VM1':
                print('  %s %s n=%d m=%d %s' % (lev, name, n, m, info), flush=True)
    print('levels:', dict(C), '; time %d s' % (time.time() - t0))
