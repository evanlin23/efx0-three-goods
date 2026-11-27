"""E3: the reverse-SD insertion (k4/sd_induct.md §2-§3) in detail.

For an SD outcome Y with junk J and an order pi producing Y, insert the agents in the order pi_n, pi_{n-1}, ..., pi_1;
each new agent f is first in the sub-instance's order.  Level k holds A_k = one-absorber completions of
I^k = (pi_k..pi_n, their picks, J); A_n = {all junk to pi_n}.  Steps move at most one junk good (Hamming <= 1).

Per start (Y) and per order pi producing Y:
  ok(pi)       : a path with steps <= 1 exists;
  greedy(pi)   : every element reachable by steps <= 1 has a successor at every level (no dead end: ANY greedy choice
                 of the one move works);
and over the successful paths, the kinds of steps: 'stay' (distance 0), 'f takes' (a junk good moves to the new agent
f), 'helper' (a good moves from the absorber to an agent other than f), 'other'.  Also: does the final absorber equal
pi_n on some successful path?  Which pi work: the reverse of an R1-priority order? the last agent pi_n unfrozen with
the most ... (features printed for the orders that fail).

    python3 k4/sdind/e3_suffix.py special|screen|suite|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by
from e1_delete import load
from e2_paths import sub_completions


def levels_for(I, Y, pi, cache):
    seq = list(pi)[::-1]
    return seq, [sub_completions(I, Y, seq[:k], cache) for k in range(1, I.n + 1)]


def reach(levels):
    """forward reachable sets R_k (index arrays into levels[k]) with steps <= 1, and dead-end info"""
    R = [np.arange(len(levels[0]))]
    dead = False
    for k in range(1, len(levels)):
        P = levels[k - 1][R[-1]]; Q = levels[k]
        if len(Q) == 0 or len(P) == 0:
            R.append(np.array([], dtype=np.int64)); dead = True; continue
        D = (P[:, None, :] != Q[None, :, :]).sum(axis=2) <= 1 if P.shape[1] else np.ones((len(P), len(Q)), bool)
        if not D.any(axis=1).all(): dead = True
        R.append(np.nonzero(D.any(axis=0))[0])
    return R, dead


def absorber(x, n):
    c = np.bincount(x, minlength=n) if len(x) else np.zeros(n, int)
    a = [i for i in range(n) if c[i] >= 2]
    return a[0] if a else None


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e3_suffix.py', *sys.argv[1:], flush=True)
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
            res = []
            for pi in orders:
                seq, levels = levels_for(I, Y, pi, cache)
                R, dead = reach(levels)
                ok = len(R[-1]) > 0
                res.append((pi, ok, ok and not dead))
            C['starts: some order ok'] += any(r[1] for r in res)
            C['starts: some order dead-end free'] += any(r[2] for r in res)
            C['starts: every order ok'] += all(r[1] for r in res)
            C['starts: every order dead-end free'] += all(r[2] for r in res)
            C['orders'] += len(res); C['orders ok'] += sum(r[1] for r in res); C['orders dead-end free'] += sum(r[2] for r in res)
            # which last agent pi_n works
            lasts_ok = set(r[0][-1] for r in res if r[1]); lasts = set(r[0][-1] for r in res)
            C['starts: every possible last agent has an ok order'] += (lasts_ok == lasts)
            # is ok determined by the last agent?
            bylast = collections.defaultdict(set)
            for pi, ok, _ in res: bylast[pi[-1]].add(ok)
            C['starts: ok depends only on the last agent'] += all(len(s) == 1 for s in bylast.values())
            # step kinds along one successful path (first ok order), via backtracking
            okp = [r[0] for r in res if r[1]]
            if okp:
                pi = okp[0]; seq, levels = levels_for(I, Y, pi, cache)
                R, _ = reach(levels)
                # backtrack a path
                cur = levels[-1][R[-1][0]]; path = [cur]
                for k in range(len(levels) - 2, -1, -1):
                    P = levels[k][R[k]]
                    d = (P != cur[None, :]).sum(axis=1) if P.shape[1] else np.zeros(len(P), int)
                    cur = P[np.nonzero(d <= 1)[0][0]]; path.append(cur)
                path = path[::-1]
                for k in range(1, len(path)):
                    f = seq[k]; a, b = path[k - 1], path[k]
                    diff = np.nonzero(a != b)[0] if len(a) else []
                    if len(diff) == 0: kind = 'stay'
                    else:
                        t = diff[0]; o = absorber(a, I.n)
                        if b[t] == f: kind = 'f takes (from absorber)' if a[t] == o else 'f takes (from non-absorber)'
                        elif a[t] == o: kind = 'helper takes from absorber'
                        else: kind = 'other'
                    C['step kind: %s' % kind] += 1
                C['final absorber is pi_n'] += (absorber(path[-1], I.n) == seq[0])
                C['final: no absorber'] += (absorber(path[-1], I.n) is None)
            if not all(r[1] for r in res) and shown['bad'] < 3:
                shown['bad'] += 1
                print('ORDERS DIFFER', name, json.dumps((sets, vals)), 'picks', Y,
                      'ok', [r[0] for r in res if r[1]][:4], 'not ok', [r[0] for r in res if not r[1]][:4], flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
