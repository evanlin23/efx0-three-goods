"""R2 and REC-S (k4/ttc.md §14.6; proof/k4-oc1max-multi §12): is R2-C realized by an earliest-wanter chain?

For a serial-dictatorship order sigma with outcome Y and a frozen k, E(k) = (k = x_0, x_1, ..., x_t = z): x_l is the
sigma-earliest wanter of Y_{x_{l-1}}, stopping at the first agent z whose pick nobody wants.  At the picks z is a
receiver by definition.  In the state after E(k) with set T, each x_l holds Y_{x_{l-1}} and k holds T ⊆ (J ∪ {Y_z}) ∩
R_k with v_k(T) > p_k; Y_z becomes junk unless it is in T.

R2-E: at every hard perfect start with >= 2 receivers, for some order sigma giving the start, some k in D and some
improving T, the state after E(k) has a one-absorber completion.  Also recorded: whether a pair T suffices (REC-S uses
pairs), and whether the completion can be owned by a receiver of Y.

    python3 k4/ttc/r2_ek.py sweep N4[,N4..] STRIDE R SEED | walk FILE.json STEPS SEED"""
import sys, os, json, itertools, collections, time, random, multiprocessing as mp
import ttclib as T
import oc1max_n6 as O
import oc1max_cex_n4 as X
import core_climb as CC


def ek(E, Y, sigma, k):
    pos = {a: i for i, a in enumerate(sigma)}; path = [k]
    while True:
        y = Y[path[-1]]
        w = [i for i in range(E.n) if i not in path and E.v[i].get(y, 0) > E.v[i].get(Y[i], 0)]
        if not w:
            return path
        path.append(min(w, key=lambda i: pos[i]))


def state(E, Y, path, Tset):
    nb = [-1] * E.m
    for i, y in enumerate(Y):
        nb[y] = i
    for l in range(1, len(path)):
        nb[Y[path[l - 1]]] = path[l]
    nb[Y[path[-1]]] = -1
    for g in Tset:
        nb[g] = path[0]
    return tuple(nb)


def test_start(E, Y, orders, C, out, info):
    b = T.base_of(E, Y); F = T.frozen_set(E, b); U = [i for i in range(E.n) if i not in F]
    if len(U) < 2:
        return
    D = T.dangerous_set(E, b); J = [g for g in range(E.m) if b[g] < 0]
    C['hard starts with >= 2 receivers'] += 1
    any_ok = pair_ok = recv_owner = False; ends = set()
    for sigma in orders:
        for k in D:
            path = ek(E, Y, sigma, k); z = path[-1]
            if len(path) < 2:
                continue
            ends.add(z in U)
            pool = [g for g in J + [Y[z]] if E.v[k].get(g, 0) > 0]
            for r in range(1, len(pool) + 1):
                for Tset in itertools.combinations(pool, r):
                    if T.val(E, k, Tset) <= E.v[k][Y[k]]:
                        continue
                    b2 = state(E, Y, path, Tset)
                    if T.extends_A(E, b2, 1):
                        any_ok = True; pair_ok |= (r == 2)
                        if not recv_owner and any(T.extends_owner(E, b2, u) for u in U):
                            recv_owner = True
            if any_ok and pair_ok and recv_owner:
                break
        if any_ok and pair_ok and recv_owner:
            break
    C['  E(k) ends at a receiver: always' if ends == {True} else '  E(k) ends at a receiver: NOT always'] += 1
    C['  R2-E: some E(k) with an improving T repairs' if any_ok else '  R2-E FAILS'] += 1
    C['  some E(k) with a PAIR T repairs' if pair_ok else '  no E(k) with a pair T repairs'] += 1
    C['  some repairing E(k) has a receiver of Y as owner' if recv_owner else '  no repairing E(k) has a receiver owner'] += 1
    if not any_ok:
        out.append(('R2-E FAILS', info))


def starts_with_orders(E, n):
    by = collections.defaultdict(list)
    for pi in itertools.permutations(range(n)):
        Y = tuple(T.sd(E, list(pi))[0])
        if any(y is None for y in Y):
            continue
        by[Y].append(list(pi))
    for Y, orders in by.items():
        if not T.extends_A(E, T.base_of(E, Y), 1):
            yield Y, orders


def job(args):
    m, sets, R, seed = args
    rng = random.Random(seed); C = collections.Counter(); found = []
    for _ in range(R):
        vals = O.profile(sets, rng); E = T.Enc(sets, vals, m)
        for Y, orders in starts_with_orders(E, len(sets)):
            test_start(E, Y, orders, C, found, {'sets': sets, 'vals': vals, 'm': m, 'picks': Y, 'order': orders[0]})
    return C, found


def walk_one(args):
    d, steps, seed = args
    rng = random.Random(seed); sets = d['sets']; vals = [list(v) for v in d['vals']]
    m = 1 + max(max(s) for s in sets); n = len(sets)
    deg = [sum(g in S for S in sets) for g in range(m)]
    doms = [O.S4.domain(S, deg) for S in sets]
    C = collections.Counter(); found = []; seen = set()
    for step in range(steps + 1):
        v2 = [list(v) for v in vals]
        if step:
            i = rng.randrange(n); v2[i] = list(rng.choice(doms[i]))
        key = tuple(map(tuple, v2))
        if key in seen or CC.is_core4(CC.vmatrix(sets, v2, m)):
            continue
        seen.add(key); vals = v2
        E = T.Enc(sets, v2, m)
        for Y, orders in starts_with_orders(E, n):
            test_start(E, Y, orders, C, found, {'sets': sets, 'vals': v2, 'm': m, 'picks': Y, 'order': orders[0]})
    return C, found


def run(tasks, fn):
    Ctot = collections.Counter()
    with mp.Pool(max(1, (os.cpu_count() or 2))) as pool:
        for C, found in pool.imap_unordered(fn, tasks, chunksize=2):
            Ctot.update(C)
            for tag, d in found:
                print(tag, json.dumps(d), flush=True)
    return Ctot


if __name__ == '__main__':
    print('$ python3 k4/ttc/r2_ek.py', *sys.argv[1:], flush=True)
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
        Ctot = run(tasks, job)
    else:
        ds = X.load(a[1]); steps = int(a[2]); seed = int(a[3])
        Ctot = run([(d, steps, seed * 7919 + k) for k, d in enumerate(ds)], walk_one)
    for k in sorted(Ctot):
        print(k, Ctot[k])
    print('time %.0f s' % (time.time() - t0), flush=True)
