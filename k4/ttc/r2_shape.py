"""Conjecture R2 (k4/ttc.md §14.6): at a perfect serial-dictatorship start (every agent holds exactly one pick) with at
least two receivers, one official move gives a one-absorber completion.  This script measures R2 and the shape of the
repairing moves at the hard starts (no one-absorber completion at the picks) with two or more receivers.

Definitions at a perfect start Y with junk J: an agent j is frozen if some other agent i values Y_j above Y_i; a
receiver is an agent that is not frozen; D = the dangerous agents (frozen and valuing some junk good).

For each repairing move (de_free chain or addition, ttclib.iter_chains_path) a one-absorber completion is extracted
from the SAT model, and the move is classified:
  - canonical: x_0 in D and x_1 values Y_{x_0} above Y_{x_1};
  - where it ends: x_t a receiver at Y or frozen;
  - the absorber (the agent receiving two or more junk goods of the new junk, if any): a receiver of Y off the path,
    x_0, x_t, another path agent, or none;
  - the coordinator's shape "OS": a canonical chain whose absorber is a receiver of Y and which ends at a different
    receiver of Y (one receiver owns, the other is a slot), or ends anywhere with the absorber a receiver off the path.
Printed: every hard start with >= 2 receivers and no repairing move (an R2 failure), and the counts.

    python3 k4/ttc/r2_shape.py sweep N4[,N4..] STRIDE R SEED     (n = 6 hypergraphs as oc1max_n6.py)
    python3 k4/ttc/r2_shape.py walk FILE.json STEPS SEED          (types around FILE's instances, as oc2max_fp.py)"""
import sys, os, json, itertools, collections, time, random, multiprocessing as mp
import ttclib as T
import oc1max_n6 as O
import oc1max_cex_n4 as X
import core_climb as CC
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType


def model_A(E, base, A=1):
    """a one-absorber completion keeping base (as oc_absorb.extends_A), returned as bundles, or None"""
    cl = list(E.cl); top = E.top
    J = [g for g in range(E.m) if base[g] < 0]
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
        if base[g] >= 0:
            cl.append([E.x[g][base[g]]])
    bigs = []
    for i in range(E.n):
        top += 1; b = top; bigs.append(b)
        for g, h in itertools.combinations(J, 2):
            cl.append([-E.x[g][i], -E.x[h][i], b])
    cl.extend(CardEnc.atmost(lits=bigs, bound=A, top_id=top, encoding=EncType.seqcounter).clauses)
    S = Cadical153(bootstrap_with=cl)
    if not S.solve():
        S.delete(); return None
    mod = set(l for l in S.get_model() if l > 0); S.delete()
    return [[g for g in range(E.m) if E.x[g][i] in mod] for i in range(E.n)]


def classify(E, b, b2, path, Xc):
    F = T.frozen_set(E, b); D = T.dangerous_set(E, b); B = T.bundles(E, b)
    U = set(range(E.n)) - F
    J2 = set(g for g in range(E.m) if b2[g] < 0)
    absorb = [i for i in range(E.n) if sum(1 for g in Xc[i] if g in J2) >= 2]
    a = absorb[0] if absorb else None
    if len(path) == 1:
        kind = 'addition by %s' % ('receiver' if path[0] in U else 'frozen')
        canon = False
    else:
        canon = path[0] in D and E.v[path[1]].get(B[path[0]][0], 0) > T.val(E, path[1], B[path[1]])
        kind = 'chain, %s, ends at %s' % ('canonical' if canon else 'non-canonical',
                                          'a receiver' if path[-1] in U else 'a frozen agent')
    if a is None:
        ab = 'no absorber'
    elif a in path:
        ab = 'absorber x_0' if a == path[0] else ('absorber x_t' if a == path[-1] else 'absorber inside the path')
    else:
        ab = 'absorber a receiver off the path' if a in U else 'absorber a frozen agent off the path'
    os_shape = canon and a is not None and a in U and a not in path
    os_shape2 = canon and a is not None and a in U and path[-1] in U and a != path[-1]
    return kind, ab, os_shape or os_shape2


def test_start(E, b, C, out, info):
    F = T.frozen_set(E, b); U = [i for i in range(E.n) if i not in F]
    C['hard perfect starts with %d receivers' % len(U)] += 1
    if len(U) < 2:
        return
    reps = []; owners = collections.Counter(); fp = False; cz = False
    B = T.bundles(E, b); D = T.dangerous_set(E, b)
    for b2, path in T.iter_chains_path(E, b):
        Xc = model_A(E, b2)
        if Xc is not None:
            reps.append(classify(E, b, b2, path, Xc))
            fp |= X.fixed_point_min(E, b, b2, path)
            if len(path) >= 2 and path[0] in D and path[-1] in U and \
                    E.v[path[1]].get(B[path[0]][0], 0) > T.val(E, path[1], B[path[1]]):
                cz = True   # a canonical chain ending at a receiver z repairs; which owners work for it?
                z = path[-1]
                for o, tag in [(z, 'z = x_t'), (path[0], 'x_0')] + [(u, 'another receiver off the path')
                                                                    for u in U if u not in path]:
                    if T.extends_owner(E, b2, o):
                        owners[tag] = 1
                if T.extends_owner(E, b2, None):
                    owners['no absorber needed'] = 1
    if cz:
        for tag in ['z = x_t', 'x_0', 'another receiver off the path', 'no absorber needed']:
            C['  canonical chain to a receiver z repairs with owner %s: %s' % (tag, 'some' if owners[tag] else 'none')] += 1
    C['  some minimal fixed point (§11) repairs' if fp else '  no minimal fixed point repairs'] += 1
    if not reps:
        C['R2 FAILS'] += 1; out.append(('R2 FAILS', info)); return
    C['R2 holds'] += 1
    kinds = set(r[0] for r in reps); abs_ = set(r[1] for r in reps)
    for k in kinds:
        C['  some repair: %s' % k] += 1
    for a in abs_:
        C['  some repair: %s' % a] += 1
    C['  some repair has the shape OS (canonical; a receiver absorbs, the chain avoids it or ends at the other)'
      if any(r[2] for r in reps) else '  NO repair has the shape OS'] += 1
    if not any(r[2] for r in reps):
        out.append(('no OS repair', dict(info, repairs=sorted(set(map(str, reps)))[:6])))
    C['  some canonical chain repairs' if any('canonical,' in r[0] and 'non-' not in r[0] for r in reps)
      else '  no canonical chain repairs'] += 1


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
            test_start(E, b, C, found, {'sets': sets, 'vals': vals, 'm': m, 'order': pi, 'picks': Y})
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
        seen.add(key); vals = v2; C['distinct profiles'] += 1
        E = T.Enc(sets, v2, m)
        for pi, Y, b in starts(E, n):
            test_start(E, b, C, found, {'sets': sets, 'vals': v2, 'm': m, 'order': pi, 'picks': Y})
    return C, found


def run(tasks, fn):
    Ctot = collections.Counter(); printed = collections.Counter()
    with mp.Pool(max(1, (os.cpu_count() or 2))) as pool:
        for C, found in pool.imap_unordered(fn, tasks, chunksize=2):
            Ctot.update(C)
            for tag, d in found:
                printed[tag] += 1
                if tag == 'R2 FAILS' or printed[tag] <= 10:
                    print(tag, json.dumps(d), flush=True)
    return Ctot


if __name__ == '__main__':
    print('$ python3 k4/ttc/r2_shape.py', *sys.argv[1:], flush=True)
    t0 = time.time(); a = sys.argv[1:]
    if a[0] == 'sweep':
        n4s = [int(x) for x in a[1].split(',')]; stride = int(a[2]); R = int(a[3]); seed = int(a[4]); tasks = []
        for n4 in n4s:
            k = 0
            for m in range(4, 3 * O.N + 1):
                for sets in O.S4.cores(O.N, m, n4 == O.N, None if n4 == O.N else n4):
                    k += 1
                    if k % stride == 0 and CC.nu(sets) == O.N:
                        tasks.append((m, sets, R, seed * 1000003 + len(tasks)))
        print('hypergraphs', len(tasks), flush=True)
        Ctot = run(tasks, job)
    else:
        ds = X.load(a[1]); steps = int(a[2]); seed = int(a[3])
        Ctot = run([(d, steps, seed * 7919 + k) for k, d in enumerate(ds)], walk_one)
    for k in sorted(Ctot):
        print(k, Ctot[k])
    print('time %.0f s' % (time.time() - t0), flush=True)
