"""OC2^max and the pointer rule FP+1 (k4/ttc.md §14), on the n = 6 sweep of k4/ttc/oc1max_n6.py (same hypergraphs,
profiles, seeds and orders) or near the n = 4 counterexamples to OC1^max (walk mode).

For every distinct maximum-matching serial-dictatorship start with no one-absorber completion (oc_absorb.extends_A):
  - OC1^max: does one improving move (de_free chains and additions, ttclib.iter_chains_path) give one?
  - minimal fixed points (k4/ttc/oc1max_cex_n4.fixed_point_min, the pointer fixed point of §11): a dangerous x_0
    takes an inclusion-minimal improving set of junk as its new base, its pick travels along a pure want path
    x_1, ..., x_t (each takes exactly its predecessor's base) and x_t is a receiver (unfrozen);
  - FP+1 (some / every): after the fixed point, the bases have a one-absorber completion or one more move gives one;
  - OC2^max: two moves (any) give one; and the good first moves (those after which at most one more move gives a
    completion) are classified: does a good first move absorb danger (some agent dangerous at the start takes, into
    its new base, junk it values: as x_0, as an internal member of the chain, or by an addition)?  Is every good first
    move danger-absorbing, and is every danger-absorbing first move good?
The rule FP+1^max: one move suffices, or some minimal fixed point is followed by at most one more move.  Printed:
every OC1^max failure where no minimal fixed point is so finished ('FP+1 FAILS', with OC2^max's verdict), the first
few where some but not every fixed point is ('FP+1 every fails'), and every OC2^max failure ('OC2max FAILS').

    python3 k4/ttc/oc2max_fp.py sweep N4[,N4..] STRIDE R SEED     (n = 6, as oc1max_n6.py)
    python3 k4/ttc/oc2max_fp.py walk FILE.json STEPS SEED          (mutate one agent's type at a time, from each instance
        of FILE.json, keeping strict cores with an OC1^max failure; every visited instance is tested)
    python3 k4/ttc/oc2max_fp.py grow FILE.json STEPS SEED EXTRA [REPS] [mc2]  (mc2: no agent with two private goods;
        add EXTRA agents to each instance, then walk
        over types and incidences; a step is kept if the score (100 x OC1^max failures + 10 - fewest repairing moves +
        starts without a completion) does not drop; strict cores with nu = n only)"""
import sys, os, json, itertools, collections, time, random, multiprocessing as mp
import ttclib as T
import oc1max_n6 as O
import oc1max_cex_n4 as X
import core_climb as CC


def moves(E, b):
    return X.moves(E, b)


def finished(E, b):
    """a one-absorber completion now or after one more move"""
    if T.extends_A(E, b, 1):
        return True
    return any(T.extends_A(E, b2, 1) for b2 in moves(E, b))


def absorbs(E, b, b1):
    """the move b -> b1 absorbs danger: some agent dangerous at b holds, at b1, a new base containing a junk good (of
    b) that it values (as x_0 of a chain, as an internal member, or by an addition)"""
    for d in T.dangerous_set(E, b):
        if any(b[g] < 0 and b1[g] == d and E.v[d].get(g, 0) > 0 for g in range(E.m)):
            return True
    return False


def test_start(E, b, C, out):
    """b: a maximum start without a one-absorber completion; updates C, appends (tag, info) to out"""
    C['maximum starts without a completion'] += 1
    M1 = moves(E, b)
    nrep = 0
    for b2 in M1:
        if T.extends_A(E, b2, 1):
            nrep += 1
            if nrep >= 10:
                break
    one = nrep > 0
    C['OC1^max holds' if one else 'OC1^max fails'] += 1
    fps = [b1 for b1, p1 in M1.items() if X.fixed_point_min(E, b, b1, p1)]
    C['minimal fixed point exists' if fps else 'NO MINIMAL FIXED POINT'] += 1
    ok = [finished(E, b1) for b1 in fps]
    some, every = any(ok), bool(ok) and all(ok)
    C['FP+1 some holds' if some else 'FP+1 some FAILS'] += 1
    C['FP+1 every holds' if every else 'FP+1 every fails'] += 1
    if not one:
        C['  among OC1^max failures: FP+1 some holds' if some else '  among OC1^max failures: FP+1 some FAILS'] += 1
    if one:
        return nrep
    C['  among OC1^max failures: minimal fixed point exists' if fps else
      '  among OC1^max failures: NO MINIMAL FIXED POINT'] += 1
    C['  among OC1^max failures: FP+1 every holds' if every else '  among OC1^max failures: FP+1 every fails'] += 1
    good = [b1 for b1 in M1 if finished(E, b1)]
    oc2 = bool(good)
    C['  among OC1^max failures: OC2^max holds' if oc2 else 'OC2^max FAILS'] += 1
    da = [b1 for b1 in good if absorbs(E, b, b1)]
    C['  among OC1^max failures: some good first move absorbs danger' if da else
      '  among OC1^max failures: NO GOOD FIRST MOVE ABSORBS DANGER'] += 1
    C['  among OC1^max failures: every good first move absorbs danger' if len(da) == len(good) and good else
      '  among OC1^max failures: some good first move absorbs no danger'] += 1
    C['  among OC1^max failures: every danger-absorbing first move is good' if all(
        finished(E, b1) for b1 in M1 if absorbs(E, b, b1)) else
      '  among OC1^max failures: some danger-absorbing first move is bad'] += 1
    if not some:
        out.append(('FP+1 FAILS', {'OC2max': oc2, 'fixed points': len(fps)}))
    elif not every:
        out.append(('FP+1 every fails', {'fixed points': len(fps), 'good': sum(ok)}))
    if not oc2:
        out.append(('OC2max FAILS', {}))
    return 0


def starts(E, n):
    seen = set()
    for pi in itertools.permutations(range(n)):
        Y = tuple(T.sd(E, list(pi))[0])
        if Y in seen:
            continue
        seen.add(Y)
        if any(y is None for y in Y):
            continue
        b = T.base_of(E, Y)
        if not T.extends_A(E, b, 1):
            yield list(pi), Y, b


def job(args):
    m, sets, R, seed = args
    rng = random.Random(seed); C = collections.Counter(); found = []
    for _ in range(R):
        vals = O.profile(sets, rng); E = T.Enc(sets, vals, m)
        for pi, Y, b in starts(E, len(sets)):
            out = []
            test_start(E, b, C, out)
            for tag, info in out:
                found.append((tag, {'sets': sets, 'vals': vals, 'm': m, 'order': pi, 'picks': Y, **info}))
    return C, found


def sweep(argv):
    n4s = [int(x) for x in argv[0].split(',')]; stride = int(argv[1]); R = int(argv[2]); seed = int(argv[3])
    t0 = time.time(); tasks = []; N = O.N
    for n4 in n4s:
        k = 0
        for m in range(4, 3 * N + 1):
            for sets in O.S4.cores(N, m, n4 == N, None if n4 == N else n4):
                k += 1
                if k % stride:
                    continue
                if CC.nu(sets) < N:
                    continue
                tasks.append((m, sets, R, seed * 1000003 + len(tasks)))
        print('n4 = %d: %d hypergraphs enumerated, %d sampled so far, %.0f s' % (n4, k, len(tasks), time.time() - t0),
              flush=True)
    Ctot = collections.Counter(); printed = collections.Counter(); done = 0
    with mp.Pool(max(1, (os.cpu_count() or 2))) as pool:
        for C, found in pool.imap_unordered(job, tasks, chunksize=4):
            done += 1; Ctot.update(C)
            for tag, d in found:
                printed[tag] += 1
                if tag != 'FP+1 every fails' or printed[tag] <= 8:
                    print(tag, json.dumps(d), flush=True)
            if done % 5000 == 0:
                print('...', done, 'of', len(tasks), 'hypergraphs, %.0f s' % (time.time() - t0), flush=True)
    print('hypergraphs tested', len(tasks), 'profiles each', R)
    return Ctot


def walk_one(args):
    d, steps, seed = args
    rng = random.Random(seed); sets = d['sets']; vals = [list(v) for v in d['vals']]
    m = 1 + max(max(s) for s in sets); n = len(sets)
    deg = [sum(g in S for S in sets) for g in range(m)]
    doms = [O.S4.domain(S, deg) for S in sets]
    C = collections.Counter(); found = []; seen = set(); cur = None
    for step in range(steps + 1):
        if step:
            v2 = [list(v) for v in vals]; i = rng.randrange(n); v2[i] = list(rng.choice(doms[i]))
        else:
            v2 = vals
        key = tuple(map(tuple, v2))
        if CC.is_core4(CC.vmatrix(sets, v2, m)):
            continue
        E = T.Enc(sets, v2, m); fails = 0; Cl = collections.Counter(); out_all = []
        for pi, Y, b in starts(E, n):
            out = []
            test_start(E, b, Cl, out)
            for tag, info in out:
                out_all.append((tag, {'sets': sets, 'vals': v2, 'm': m, 'order': pi, 'picks': Y, **info}))
        fails = Cl['OC1^max fails']
        if key not in seen:
            seen.add(key); C.update(Cl); found.extend(out_all); C['distinct profiles visited'] += 1
            C['visited profiles with an OC1^max failure'] += fails > 0
        if step == 0 or fails >= (cur or 0):
            vals = v2; cur = fails
    return C, found


def grow_one(args):
    """lift an instance to n + extra agents: each new agent takes 3 or 4 goods among the old ones and up to two new
    goods; then walk as walk_one, also moving one good of one agent now and then; only strict connected cores with
    nu = n are visited"""
    d, steps, seed, extra, mc2 = args
    rng = random.Random(seed)
    for _ in range(2000):
        sets = [list(s) for s in d['sets']]; m = 1 + max(max(s) for s in sets)
        for _ in range(extra):
            new = list(range(m, m + rng.choice([0, 1, 1, 2])))
            k = rng.choice([3, 4, 4]) - len(new)
            sets.append(sorted(new + rng.sample(range(m), k))); m += len(new)
        vals = [list(v) for v in d['vals']]
        deg = [sum(g in S for S in sets) for g in range(m)]
        doms = [O.S4.domain(S, deg) for S in sets]
        if not all(doms):
            continue
        vals = [list(rng.choice(dm)) for dm in doms]
        if CC.nu(sets) == len(sets) and not CC.is_core4(CC.vmatrix(sets, vals, m)) and \
                not (mc2 and CC.two_private(sets)):
            break
    else:
        return collections.Counter(), []
    n = len(sets); C = collections.Counter(); found = []; seen = set(); cur = None
    for step in range(steps + 1):
        s2 = [list(x) for x in sets]; v2 = [list(v) for v in vals]
        if step:
            i = rng.randrange(n)
            if rng.random() < 0.2:
                j = rng.randrange(len(s2[i])); g = rng.randrange(m)
                if g in s2[i]:
                    continue
                s2[i][j] = g; s2[i].sort()
                if len(set().union(*map(set, s2))) < m or CC.nu(s2) < n or (mc2 and CC.two_private(s2)):
                    continue
            deg = [sum(g in S for S in s2) for g in range(m)]
            dm = O.S4.domain(s2[i], deg)
            if not dm:
                continue
            v2[i] = list(rng.choice(dm))
        key = (tuple(map(tuple, s2)), tuple(map(tuple, v2)))
        if CC.is_core4(CC.vmatrix(s2, v2, m)):
            continue
        E = T.Enc(s2, v2, m); Cl = collections.Counter(); out_all = []; least = 10
        for pi, Y, b in starts(E, n):
            out = []
            least = min(least, test_start(E, b, Cl, out))
            for tag, info in out:
                out_all.append((tag, {'sets': s2, 'vals': v2, 'm': m, 'order': pi, 'picks': Y, **info}))
        fails = Cl['OC1^max fails']; score = 100 * fails + 10 - least + Cl['maximum starts without a completion']
        if key not in seen:
            seen.add(key); C.update(Cl); found.extend(out_all); C['distinct instances visited'] += 1
            C['visited instances with an OC1^max failure'] += fails > 0
        if step == 0 or score >= cur:
            sets, vals, cur = s2, v2, score
    return C, found


def grow(argv):
    ds = json.load(open(argv[0]))['instances']; steps = int(argv[1]); seed = int(argv[2]); extra = int(argv[3])
    reps = int(argv[4]) if len(argv) > 4 and argv[4].isdigit() else 1; mc2 = 'mc2' in argv[4:]
    tasks = [(d, steps, seed * 7919 + 31 * k + r, extra, mc2) for k, d in enumerate(ds) for r in range(reps)]
    Ctot = collections.Counter(); printed = collections.Counter()
    with mp.Pool(max(1, (os.cpu_count() or 2))) as pool:
        for C, found in pool.imap_unordered(grow_one, tasks):
            Ctot.update(C)
            for tag, d in found:
                printed[tag] += 1
                if tag != 'FP+1 every fails' or printed[tag] <= 8:
                    print(tag, json.dumps(d), flush=True)
    print('grown walks', len(tasks), 'steps each', steps, 'extra agents', extra, 'MC2 class' if mc2 else '')
    return Ctot


def walk(argv):
    ds = json.load(open(argv[0]))['instances']; steps = int(argv[1]); seed = int(argv[2])
    tasks = [(d, steps, seed * 7919 + k) for k, d in enumerate(ds)]
    Ctot = collections.Counter(); printed = collections.Counter()
    with mp.Pool(max(1, (os.cpu_count() or 2))) as pool:
        for C, found in pool.imap_unordered(walk_one, tasks):
            Ctot.update(C)
            for tag, d in found:
                printed[tag] += 1
                if tag != 'FP+1 every fails' or printed[tag] <= 8:
                    print(tag, json.dumps(d), flush=True)
    print('walks', len(tasks), 'steps each', steps)
    return Ctot


if __name__ == '__main__':
    print('$ python3 k4/ttc/oc2max_fp.py', *sys.argv[1:], flush=True)
    t0 = time.time()
    Ctot = {'sweep': sweep, 'walk': walk, 'grow': grow}[sys.argv[1]](sys.argv[2:])
    for k in sorted(Ctot):
        print(k, Ctot[k])
    print('time %.0f s' % (time.time() - t0), flush=True)
