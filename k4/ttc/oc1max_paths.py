"""How long must the repairing move be?  A companion to k4/ttc/oc1max_n6.py (k4/ttc.md §13), on the same hypergraphs,
profiles (same seeds) and orders.

For every distinct maximum-matching start with no one-absorber completion (oc_absorb.extends_A), every improving move
of de_free (k4/ttc/ttclib.iter_chains_path: an addition is a path (x_0); a chain (x_0, ..., x_t) is a trading cycle in
which x_i takes x_{i-1}'s base plus junk and x_0 takes junk and part of x_t's base) is grouped by path length, and the
shortest repairing length is recorded: 1 = addition, 2 = a two-agent swap, and so on.  For the shortest repair the
roles are recorded too: whether x_0 is dangerous (frozen and valuing junk), whether x_1 (or x_t) is unfrozen, and
whether x_1 is an agent that freezes x_0 (values x_0's pick above its own base).  Also tested: whether some repair has
the canonical form (an addition, or a chain whose x_0 is dangerous and whose x_1 freezes x_0); starts with none are
printed (NON-CANONICAL).  And the pointer fixed point of §11: a chain from a dangerous x_0 along a pure want path
(every x_i, i >= 1, takes exactly x_{i-1}'s pick) to an unfrozen x_t, with x_0 taking junk and part of x_t's base;
does one repair (any absorber; absorber x_t)?  Starts where none repairs are printed (NO-FIXED-POINT).

    python3 k4/ttc/oc1max_paths.py N4[,N4..] STRIDE R SEED [mc2]   (arguments as for oc1max_n6.py)"""
import sys, os, json, itertools, collections, time, random, multiprocessing as mp
import ttclib as T
import oc1max_n6 as O

N = O.N


def roles(E, base, path):
    F = T.frozen_set(E, base); D = T.dangerous_set(E, base); B = T.bundles(E, base)
    x0 = path[0]
    if len(path) == 1:
        return 'addition by %s' % ('dangerous' if x0 in D else 'frozen' if x0 in F else 'unfrozen')
    x1 = path[1]
    frz = len(B[x0]) == 1 and E.v[x1].get(B[x0][0], 0) > T.val(E, x1, B[x1])
    return 'x0 %s, x1 %s%s, x_t %s' % ('dangerous' if x0 in D else 'frozen' if x0 in F else 'unfrozen',
                                      'frozen' if x1 in F else 'unfrozen', ' (freezes x0)' if frz else '',
                                      'frozen' if path[-1] in F else 'unfrozen')


def job(args):
    m, sets, R, seed = args
    rng = random.Random(seed); C = collections.Counter(); worst = None; bad = []; bad_c = []; bad_fp = []; Ctr_fp = [0]
    for _ in range(R):
        vals = O.profile(sets, rng); E = T.Enc(sets, vals, m); seen = set()
        for pi in itertools.permutations(range(N)):
            Y = tuple(T.sd(E, list(pi))[0])
            if Y in seen:
                continue
            seen.add(Y)
            if any(y is None for y in Y):
                continue
            b = T.base_of(E, Y)
            if T.extends_A(E, b, 1):
                continue
            C['maximum starts needing a move'] += 1
            by = collections.defaultdict(dict)
            for b2, path in T.iter_chains_path(E, b):
                by[len(path)].setdefault(b2, path)
            L = None
            for k in sorted(by):
                for b2, path in by[k].items():
                    if T.extends_A(E, b2, 1):
                        L = k; C['shortest repair length %d' % k] += 1
                        C['  length %d: %s' % (k, roles(E, b, path))] += 1
                        break
                if L is not None:
                    break
            # canonical form: an addition, or a chain whose x_0 is dangerous and whose x_1 freezes x_0
            D = T.dangerous_set(E, b); B = T.bundles(E, b)
            canon = next((k for k in sorted(by) for b2, path in by[k].items()
                          if (k == 1 or (path[0] in D and E.v[path[1]].get(B[path[0]][0], 0) > T.val(E, path[1], B[path[1]])))
                          and T.extends_A(E, b2, 1)), None) if L is not None else None
            # the fixed point of the pointer map of k4/ttc.md §11: x_0 dangerous, a pure want path (each x_i, i >= 1,
            # takes exactly x_{i-1}'s pick and no junk), ending at an unfrozen x_t, x_0 taking junk and part of x_t's
            # base; 'head' means the completion has x_t as its absorber (§11's column (c-head))
            F = T.frozen_set(E, b); fp = fph = False
            for k in sorted(by):
                if k == 1:
                    continue
                for b2, path in by[k].items():
                    if path[0] not in D or path[-1] in F:
                        continue
                    if any(sorted(g for g in range(E.m) if b2[g] == path[i]) != sorted(B[path[i - 1]])
                           for i in range(1, k)):
                        continue
                    if not fp and T.extends_A(E, b2, 1):
                        fp = True
                    if not fph and T.extends_owner(E, b2, path[-1]):
                        fph = True
                    if fp and fph:
                        break
                if fp and fph:
                    break
            C['pointer fixed point repairs' if fp else 'NO REPAIRING POINTER FIXED POINT'] += 1
            C['pointer fixed point repairs, absorber x_t' if fph else 'no fixed point repairs with absorber x_t'] += 1
            if not fp and Ctr_fp[0] < 2:
                Ctr_fp[0] += 1; bad_fp.append((vals, Y))
            C['canonical repair exists' if canon is not None else 'NO CANONICAL REPAIR'] += 1
            if canon is not None:
                C['shortest canonical repair %d' % canon] += 1
            if L is not None and canon is None:
                bad_c.append((vals, Y))
            if L is None:
                C['NO REPAIRING MOVE'] += 1; bad.append((vals, Y))
            elif worst is None or L > worst[0]:
                worst = (L, vals, Y, O.structure(E, b))
    return m, sets, C, worst, bad, bad_c[:2], bad_fp


def main(argv):
    n4s = [int(x) for x in argv[0].split(',')]; stride = int(argv[1]); R = int(argv[2]); seed = int(argv[3])
    mc2 = 'mc2' in argv[4:]
    print('$ python3 k4/ttc/oc1max_paths.py', *argv, flush=True)
    t0 = time.time(); tasks = []
    for n4 in n4s:
        k = 0
        for m in range(4, 3 * N + 1):
            for sets in O.S4.cores(N, m, n4 == N, None if n4 == N else n4):
                k += 1
                if k % stride:
                    continue
                if O.CC.nu(sets) < N or (mc2 and O.CC.two_private(sets)):
                    continue
                tasks.append((m, sets, R, seed * 1000003 + len(tasks)))
        print('n4 = %d: %d hypergraphs enumerated, %d sampled so far, %.0f s' % (n4, k, len(tasks), time.time() - t0),
              flush=True)
    Ctot = collections.Counter(); worst = []; done = 0
    with mp.Pool(max(1, (os.cpu_count() or 2))) as pool:
        for m, sets, C, w, bad, bad_c, bad_fp in pool.imap_unordered(job, tasks, chunksize=4):
            done += 1; Ctot.update(C)
            for vals, Y in bad_fp:
                if Ctot['printed without a repairing fixed point'] < 8:
                    Ctot['printed without a repairing fixed point'] += 1
                    print('NO-FIXED-POINT', json.dumps({'sets': sets, 'vals': vals, 'm': m, 'picks': Y}), flush=True)
            for vals, Y in bad_c:
                if Ctot['printed non-canonical'] < 8:
                    Ctot['printed non-canonical'] += 1
                    print('NON-CANONICAL', json.dumps({'sets': sets, 'vals': vals, 'm': m, 'picks': Y}), flush=True)
            for vals, Y in bad:
                print('OC1max FAILS', json.dumps({'sets': sets, 'vals': vals, 'm': m, 'picks': Y}), flush=True)
            if w is not None:
                worst.append((w[0], m, sets, w[1], w[2], w[3]))
            if done % 5000 == 0:
                print('...', done, 'of', len(tasks), 'hypergraphs, %.0f s' % (time.time() - t0), flush=True)
    print('hypergraphs tested', len(tasks), 'profiles each', R)
    for k in sorted(Ctot):
        print(k, Ctot[k])
    worst.sort(key=lambda h: -h[0])
    print('longest shortest repairs:')
    for L, m, sets, vals, Y, st in worst[:8]:
        print('  length %d' % L, json.dumps({'sets': sets, 'vals': vals, 'm': m, 'picks': Y}), st)
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
