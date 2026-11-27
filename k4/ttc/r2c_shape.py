"""Shapes of the R2-C repairs (k4/ttc.md §14.6): at every hard perfect start with >= 2 receivers, the repairing
canonical chains (x_0 dangerous, x_1 wants y_{x_0}, ending at a receiver), classified by
  - short: the chain ends at the first receiver on its path (no earlier x_i, 1 <= i < t, is a receiver);
  - middle junk: some x_i with 1 <= i <= t takes junk besides x_{i-1}'s pick;
  - middle danger: some x_i, 1 <= i < t, that is dangerous at the start takes junk it values.
Per start: is there a short chain with no middle junk (the E(k)-like shape, any wanter)?  If not, which shapes occur?

    python3 k4/ttc/r2c_shape.py sweep N4[,N4..] STRIDE R SEED | walk FILE.json STEPS SEED"""
import sys, collections, time
import ttclib as T
import oc1max_n6 as O
import oc1max_cex_n4 as X
import core_climb as CC
import r2_shape as R


def test_start(E, b, C, out, info):
    F = T.frozen_set(E, b); U = [i for i in range(E.n) if i not in F]
    if len(U) < 2:
        return
    D = T.dangerous_set(E, b); B = T.bundles(E, b); J = set(g for g in range(E.m) if b[g] < 0)
    C['hard starts with >= 2 receivers'] += 1
    shapes = set()
    for b2, path in T.iter_chains_path(E, b):
        if not (len(path) >= 2 and path[0] in D and path[-1] in U and
                E.v[path[1]].get(B[path[0]][0], 0) > T.val(E, path[1], B[path[1]])):
            continue
        if not T.extends_A(E, b2, 1):
            continue
        short = not any(x in U for x in path[1:-1])
        mj = any(set(g for g in range(E.m) if b2[g] == path[i]) - set(B[path[i - 1]]) for i in range(1, len(path)))
        md = any(path[i] in D and any(b2[g] == path[i] and g in J and E.v[path[i]].get(g, 0) > 0
                                       for g in range(E.m)) for i in range(1, len(path) - 1))
        shapes.add((short, mj, md))
    if not shapes:
        C['NO R2-C CHAIN'] += 1; out.append(('NO R2-C CHAIN', info)); return
    if (True, False, False) in shapes:
        C['  a short chain without middle junk repairs'] += 1
    else:
        C['  NO short chain without middle junk: shapes %s' % sorted(
            ('short' if s else 'passes a receiver') + (', middle junk' if j else '') + (', middle danger' if d else '')
            for s, j, d in shapes)] += 1
        out.append(('needs a long or middle-junk chain', info))


R.test_start = test_start

if __name__ == '__main__':
    print('$ python3 k4/ttc/r2c_shape.py', *sys.argv[1:], flush=True)
    t0 = time.time(); a = sys.argv[1:]
    if a[0] == 'sweep':
        n4s = [int(x) for x in a[1].split(',')]; stride = int(a[2]); Rr = int(a[3]); seed = int(a[4]); tasks = []
        for n4 in n4s:
            k = 0
            for m in range(4, 3 * O.N + 1):
                for sets in O.S4.cores(O.N, m, n4 == O.N, None if n4 == O.N else n4):
                    k += 1
                    if k % stride == 0 and CC.nu(sets) == O.N:
                        tasks.append((m, sets, Rr, seed * 1000003 + len(tasks)))
        Ctot = R.run(tasks, R.job)
    else:
        ds = X.load(a[1]); steps = int(a[2]); seed = int(a[3])
        Ctot = R.run([(d, steps, seed * 7919 + k) for k, d in enumerate(ds)], R.walk_one)
    for k in sorted(Ctot):
        print(k, Ctot[k])
    print('time %.0f s' % (time.time() - t0), flush=True)
