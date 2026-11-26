"""Two-phase structure of VMX2 (k4/vm.md section 7.3).  Phase A: from a V-M matching (Phases I-II, every resolution),
apply moves only (rotation, pool upgrades, two-agent exchanges; vmlib.exchanges); Phase B: place the pool by F1 with
rotation, no moves.  For every state Z reachable in Phase A (BFS, capped), compute over all Phase-B runs from Z
(DFS, capped): some run completes EFX0 ("B-some") / every run completes ("B-every").  Reports per instance whether
some Z is B-some (= two-phase VMX2) and whether some Z is B-every, and features of the B-every states.
EVIDENCE only.
    python3 k4/vm/vmx2_phases.py SOURCE [--zcap=N] [--bcap=N] [--maxdepth=D]   (D = 1: Conjecture VM1)
    --freez=1: exchanges may hand the taker a good it values at 0"""
import sys, os, json, collections, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for


def key(X):
    return tuple(tuple(sorted(b)) for b in X)


def apply_move(X, pool, mv):
    X = [list(b) for b in X]; pool = set(pool)
    i, j, z, S = mv[:4]; y = X[i][0]
    if j is None:
        X[i] = list(S); pool.add(y)
    else:
        X[j] = [h for h in X[j] if h != z] + [y]; X[i] = [z] + list(S)
    pool -= set(S)
    return X, pool


def phase_b(I, X0, pool0, cap):
    """DFS over F1 placements with rotation from (X0, pool0): (some, every, runs)"""
    some = False; every = True; runs = 0
    stack = [([list(b) for b in X0], set(pool0))]
    while stack and runs < cap:
        X, pool = stack.pop()
        V.l3_source(I, X)
        valued = sorted(g for g in pool if I.valued_by(g))
        if not valued:
            runs += 1; some = True; continue
        branched = False
        for g in valued:
            for s in range(I.n):
                if V.safe_add(I, X, s, g):
                    Y = [list(b) for b in X]; Y[s].append(g); stack.append((Y, pool - {g})); branched = True
        if not branched:
            runs += 1; every = False
    return some, every and runs < cap, runs


def one(args):
    name, sets, vals, m, zcap, bcap, maxd, fz = args
    V.FREE_Z[0] = fz
    I = V.Inst(sets, vals, m)
    starts = []
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if not isinstance(r, V.Stuck):
            starts.append([list(b) for b in r[0]])
    seen = {}; queue = []
    for X in starts:
        held = set(g for b in X for g in b); pool = set(range(m)) - held
        if key(X) not in seen:
            seen[key(X)] = None; queue.append((X, pool, 0))
    k = 0; bsome = bevery = False; feats = collections.Counter(); depth_every = None; depth_some = None
    while k < len(queue) and k < zcap:
        X, pool, d = queue[k]; k += 1
        Y = [list(b) for b in X]; V.l3_source(I, Y)
        s_, e_, r_ = phase_b(I, Y, pool, bcap)
        bsome |= s_
        if s_ and (depth_some is None or d < depth_some): depth_some = d
        if e_:
            bevery = True
            if depth_every is None or d < depth_every: depth_every = d
            # features of a B-every state
            want = [g for g in pool if any(I.v[i].get(g, 0) > I.val(i, Y[i]) for i in range(I.n))]
            feats['pool good wanted by someone' if want else 'no pool good wanted'] += 1
        if d >= maxd:
            continue
        for mv in V.exchanges(I, Y, pool):
            Z, P = apply_move(Y, pool, mv)
            if key(Z) not in seen:
                seen[key(Z)] = None; queue.append((Z, P, d + 1))
    return name, I.n, I.m, bsome, bevery, depth_every, k, dict(feats), depth_some


if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    zcap = int(opt.get('zcap', 400)); bcap = int(opt.get('bcap', 3000)); maxd = int(opt.get('maxdepth', 99))
    if opt.get('freez') == '1': V.FREE_Z[0] = True
    print('$ python3 k4/vm/vmx2_phases.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); F = collections.Counter(); D = collections.Counter(); DS = collections.Counter(); bad = []; t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, bs, be, de, k, feats, ds in pool.imap_unordered(one, [(a, b, c, d, zcap, bcap, maxd, V.FREE_Z[0]) for a, b, c, d in items_for(src)], chunksize=2):
            C['instances'] += 1; C['some Z is B-some (two-phase VMX2)'] += bs; C['some Z is B-every'] += be
            C['Phase-A states explored'] += k
            if be: D[de] += 1
            if bs: DS[ds] += 1
            F.update(feats)
            if not be: bad.append((n, m, name, bs))
    for k in sorted(C): print('%-45s %d' % (k, C[k]))
    print('fewest moves to a B-some state:', dict(sorted(DS.items())))
    print('fewest moves to a B-every state:', dict(sorted(D.items())))
    print('B-every states by feature:', dict(F))
    for n, m, name, bs in sorted(bad)[:12]:
        print('  no B-every state: %s n=%d m=%d (B-some: %s)' % (name, n, m, bs))
    print('time %.0f s' % (time.time() - t0))
