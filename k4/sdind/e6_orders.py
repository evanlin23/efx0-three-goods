"""E6: which orders pi producing Y admit a reverse-SD insertion path with steps <= 1 (k4/sd_induct.md §3)?
Order rules tested (each picks one order among those producing Y):
  frozen-first : frozen agents (pick wanted by someone) as early in pi as possible (lexicographically by
                 (not frozen, index) among the available agents of a topological sort)
  frozen-last  : frozen agents as late as possible
  index        : the lexicographically first order
  most-wanted-first : agents with the most wanters first
  dangerous-first   : frozen agents that value some junk good first, then other frozen, then the rest
Also: is every order with frozen agents first (as a block) ok?

    python3 k4/sdind/e6_orders.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by
from e1_delete import load
from e2_paths import sub_completions, bottleneck


def topo(n, W, key):
    """a topological order of 'j before i whenever i wants Y_j' (W[j] = wanters of j), choosing by key"""
    need = {i: set(j for j in range(n) if i in W[j]) for i in range(n)}
    out = []
    while len(out) < n:
        av = [i for i in range(n) if i not in out and need[i] <= set(out)]
        i = min(av, key=key); out.append(i)
    return tuple(out)


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e6_orders.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); C['instances'] += 1
        byY = collections.defaultdict(list)
        for o in itertools.permutations(range(I.n)):
            byY[tuple(sd(I, o)[0])].append(o)
        for Y, orders in byY.items():
            Y = list(Y); cache = {}
            try:
                full = sub_completions(I, Y, range(I.n), cache)
            except ValueError:
                continue
            if len(full) == 0: continue
            C['starts'] += 1
            W = wanted_by(I, Y)
            J = set(range(I.m)) - set(g for g in Y if g is not None)
            fr = [bool(W[i]) for i in range(I.n)]
            dang = [fr[i] and any(I.V[i, g] > 0 for g in J) for i in range(I.n)]
            def ok(pi):
                seq = list(pi)[::-1]
                return bottleneck([sub_completions(I, Y, seq[:k], cache) for k in range(1, I.n + 1)]) is not None and \
                    bottleneck([sub_completions(I, Y, seq[:k], cache) for k in range(1, I.n + 1)]) <= 1
            rules = {
                'frozen-first': topo(I.n, W, lambda i: (not fr[i], i)),
                'frozen-last': topo(I.n, W, lambda i: (fr[i], i)),
                'index': topo(I.n, W, lambda i: i),
                'most-wanted-first': topo(I.n, W, lambda i: (-len(W[i]), i)),
                'dangerous-first': topo(I.n, W, lambda i: (not dang[i], not fr[i], i)),
            }
            for r, pi in rules.items():
                assert list(sd(I, pi)[0]) == Y, (r, pi, Y)
                res = ok(pi); C[r + ' ok'] += res
                if not res and shown[r] < 2 and r in ('frozen-first', 'dangerous-first'):
                    shown[r] += 1; print('ORDER RULE FAILS', r, name, json.dumps((sets, vals)), 'picks', Y, 'pi', pi, flush=True)
            # frozen block first, every arrangement
            okl = [pi for pi in orders if ok(pi)]
            C['some order ok'] += bool(okl)
            blk = [pi for pi in orders if all(fr[pi[t]] or not any(fr[pi[s]] for s in range(t + 1, I.n)) for t in range(I.n))]
            if blk: C['orders with frozen block first exist'] += 1; C['every frozen-block-first order ok'] += all(ok(pi) for pi in blk)
            C['some frozen-block-first order ok'] += any(ok(pi) for pi in blk)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
