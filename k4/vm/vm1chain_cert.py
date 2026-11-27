"""Exhaustive check of Conjecture VM1-chain-plain (k4/vm.md sections 7.7-7.8) on EVERY strict profile of a k = 4 core
hypergraph, by ordinal CEGAR (the method of k4/oc1cert/cegar.py on compute/k4-oc1max-cert, re-implemented here for
V-M; only k4/order_types.json is shared).

The statement, for a profile: some V-M matching Y (Phases I-II, main reading, some tie resolution), then at most one
trade applied to Y (a pool upgrade, an unrestricted two-agent exchange, or a DE chain whose first step keeps EFX0,
Lemma CH), then F1 placements WITHOUT rotation give a complete EFX0 allocation.  It implies VM1-chain (with rotation).

Every comparison involved is between disjoint sets of one agent's goods (ranks: single goods; Phase I: a vs b + c;
moves: new set vs old good, y vs z; EFX0 / safety: X_b - h vs X_a), so the statement depends on a profile only
through the agents' strict balanced order types (K4.OT: 6 for 3 goods, 288 for 4; (C4) for two-private agents).

Witness of a success.  The run gives, for each agent a, a list of conditions on a's own valuation:
  - V-M: a's Phase-I strong bit; if a won Phase I, Y_a is a's top; if a is strong and lost, a's top is a Phase-I
    winner's pick; otherwise (Lemma S) Y_a has rank st(a), and the j-th good a ranks above Y_a is held by an agent of
    st <= j (with no pick: every relevant good of a, at rank j, is held by an agent of st <= j).  These are exactly the
    conditions under which the same tie resolution of Phases I-II produces Y.
  - the trade's improving comparisons for the agents it moves;
  - EFX0 of the state after the trade (after the first step, for a chain) for every observer a;
  - for every placement of g on s: v_a(X_s + g - h) <= v_a(X_a) for every observer a != s and every h.
Under any profile whose types satisfy every agent's conditions, the same Y, trade and placement sequence is legal and
ends in the same complete allocation, which is then EFX0.  So the witness covers the product of the per-agent sets
T_a = {types of a satisfying a's conditions}: a "box".
Outer: a SAT solver over one-hot types finds a profile outside every box found so far; inner: the run above on its
integer representative.  UNSAT = the statement holds for every strict profile of the hypergraph.  A profile with no
run is a counterexample candidate: it is blocked singly, re-checked for VM1-chain WITH rotation (vm1_chain.one) and
reported.  EVIDENCE only (single implementation; with --verify every box is re-checked on 20 random profiles of it by
replaying the run from the raw definitions).
--level=none|move|chain: the trades allowed (default chain); 'none' and 'move' certify the stronger VM1-plain forms.
Profile spaces up to 1.5e8 use a numpy bitmap (certify_dense); larger ones (pure n = 4) are sliced by agent 0's type,
one slice per symmetry orbit (certify_sliced).  Both add every box with all its hypergraph-automorphism images.  The
SAT outer loop (certify) is kept for cross-checks.  Hypergraphs run in parallel.
    python3 k4/vm/vm1chain_cert.py N [FILE_KEY] [--limit=K] [--verify] [--idx=I,J] [--level=L] [--procs=P]
    (N = 2, 3 or 4; FILE_KEY e.g. 4_n4_3)"""
import sys, os, json, gzip, time, itertools, collections, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
OT = json.load(open(os.path.join(ROOT, 'k4', 'order_types.json')))
STRICT_BAL = {k: [tuple(t['rep']) for t in OT[str(k)]['types'] if t['strict'] and t['balanced']] for k in (3, 4)}
V.FREE_Z[0] = True


def domain(S, deg):
    priv = [p for p, g in enumerate(S) if deg[g] == 1]
    dom = STRICT_BAL[len(S)]
    if len(priv) == 2:
        dom = [v for v in dom if v[priv[0]] + v[priv[1]] < sum(v) - v[priv[0]] - v[priv[1]]]
    return dom


# ---------------------------------------------------------------- conditions on one agent's valuation
def val(vd, B):
    return sum(vd.get(g, 0) for g in B)


def rank_of(vd):
    return sorted(vd, key=lambda g: (-vd[g], g))


def vm_cond(a, Y, A, MA, st, holder, sets):
    """the V-M derivation conditions for agent a (see the docstring), as a predicate on a's value dict"""
    strong_a = a in A; ya = Y[a][0] if Y[a] else None; picksMA = set(Y[h][0] for h in MA)

    def ok(vd):
        r = rank_of(vd)
        x, y_, z = vd[r[0]], (vd[r[1]] if len(r) > 1 else 0), (vd[r[2]] if len(r) > 2 else 0)
        if (x > y_ + z) != strong_a: return False
        if a in MA: return r[0] == ya
        if strong_a and r[0] not in picksMA: return False
        if ya is not None:
            k = st[a]
            if r.index(ya) != k - 1: return False
            return all(r[j] in holder and st[holder[r[j]]] <= j + 1 for j in range(k - 1))
        return all(r[j] in holder and st[holder[r[j]]] <= j + 1 for j in range(len(r)))
    return ok


def gt(P, Q):
    P, Q = tuple(P), tuple(Q)
    return lambda vd: val(vd, P) > val(vd, Q)


def le(P, Q):
    P, Q = tuple(P), tuple(Q)
    return lambda vd: val(vd, P) <= val(vd, Q)


def efx0_conds(X, n, conds, skip=None):
    """for every observer a and every bundle X_b (b != a, |X_b| >= 2, b != skip... all): v_a(X_b - h) <= v_a(X_a)"""
    for b in range(n):
        if len(X[b]) < 2: continue
        for a in range(n):
            if a == b: continue
            for h in X[b]:
                conds[a].append(le([g for g in X[b] if g != h], X[a]))


# ---------------------------------------------------------------- the inner search
def vm_data(I, Y):
    """A (strong agents), MA (Phase-I winners), st, holder for a V-M matching Y of I"""
    n = I.n; A = set(); MA = set(); st = {}; holder = {}
    for i in range(n):
        r = I.rank[i]; x = I.v[i][r[0]]; y_ = I.v[i][r[1]] if len(r) > 1 else 0; z = I.v[i][r[2]] if len(r) > 2 else 0
        if x > y_ + z: A.add(i)
    for i in range(n):
        if Y[i]:
            holder[Y[i][0]] = i
            if i in A and Y[i][0] == I.rank[i][0]: MA.add(i); st[i] = 0
            else: st[i] = I.rank[i].index(Y[i][0]) + 1
        else:
            st[i] = 10 ** 6
    return A, MA, st, holder


def place_plain(I, X0, memo):
    """F1 placements without rotation: a list of (g, s) completing X0, or None (memoized failures)"""
    def key(X): return tuple(tuple(sorted(b)) for b in X)
    stack = [([list(b) for b in X0], [])]; seen = set()
    while stack:
        X, path = stack.pop(); k = key(X)
        if k in seen or k in memo: continue
        seen.add(k)
        held = set(g for b in X for g in b); pool = [g for g in range(I.m) if g not in held]
        if not pool:
            return path
        for g in pool:
            for s in range(I.n):
                if V.safe_add(I, X, s, g):
                    Z = [list(b) for b in X]; Z[s].append(g); stack.append((Z, path + [(g, s)]))
    memo.update(seen)
    return None


def chains_seq(I, Y):
    """chains from Y whose first step (the upgrade) keeps EFX0: (x, S, [(j, g taken)], final state)"""
    n = I.n; out = []
    pool0 = set(range(I.m)) - set(g for b in Y for g in b)
    for x in range(n):
        if len(Y[x]) != 1: continue
        y = Y[x][0]; vy = I.v[x].get(y, 0)
        mine = sorted(g for g in pool0 if g in I.v[x])
        for r in range(1, len(mine) + 1):
            for S in itertools.combinations(mine, r):
                if I.val(x, S) <= vy: continue
                X = [list(b) for b in Y]; X[x] = list(S)
                if not V.is_efx0(I, X): continue
                stack = [(X, y, {x}, [])]
                while stack:
                    X, g, used, steps = stack.pop()
                    if steps: out.append((x, S, steps, X))
                    for j in range(n):
                        if j in used or len(X[j]) != 1: continue
                        yj = X[j][0]
                        if I.v[j].get(g, 0) > I.v[j].get(yj, 0):
                            Z = [list(b) for b in X]; Z[j] = [g]
                            stack.append((Z, yj, used | {j}, steps + [(j, g, yj)]))
    return out


LEVEL = ['chain']                    # 'none': no trade (VM1-plain at zero moves); 'move': VM1-plain; 'chain': VM1-chain-plain


def inner(I):
    """a successful run as per-agent condition lists, or None"""
    n = I.n; memo = set(); Ys = []
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if not isinstance(r, V.Stuck):
            Y = [list(b) for b in r[0]]
            if Y not in Ys: Ys.append(Y)

    def base(Y):
        A, MA, st, holder = vm_data(I, Y)
        return [[vm_cond(a, Y, A, MA, st, holder, I.sets)] for a in range(n)]

    def add_path(conds, X0, path):
        X = [list(b) for b in X0]
        for g, s in path:
            B = X[s] + [g]
            if len(B) >= 2:
                for a in range(n):
                    if a == s: continue
                    for h in B:
                        conds[a].append(le([u for u in B if u != h], X[a]))
            X[s] = B
        return X

    for Y in Ys:                                          # no trade
        p = place_plain(I, Y, memo)
        if p is not None:
            c = base(Y); add_path(c, Y, p); return c, ('none', Y, None, p)
    if LEVEL[0] == 'none': return None
    for Y in Ys:                                          # one VM1 move
        pool = set(range(I.m)) - set(g for b in Y for g in b)
        for mv in V.exchanges(I, Y, pool):
            i, j, z, S = mv; X = [list(b) for b in Y]; y = Y[i][0]
            if j is None: X[i] = list(S)
            else: X[j] = [h for h in X[j] if h != z] + [y]; X[i] = [z] + list(S)
            p = place_plain(I, X, memo)
            if p is not None:
                c = base(Y)
                if j is None: c[i].append(gt(S, [y]))
                else: c[i].append(gt([z] + list(S), [y])); c[j].append(gt([y], [z]))
                efx0_conds(X, n, c); add_path(c, X, p); return c, ('move', Y, mv, p)
    if LEVEL[0] == 'move': return None
    for Y in Ys:                                          # one DE chain (sequentially valid)
        for x, S, steps, X in chains_seq(I, Y):
            p = place_plain(I, X, memo)
            if p is not None:
                c = base(Y); c[x].append(gt(S, Y[x]))
                X1 = [list(b) for b in Y]; X1[x] = list(S); efx0_conds(X1, n, c)
                for j, g, yj in steps: c[j].append(gt([g], [yj]))
                efx0_conds(X, n, c); add_path(c, X, p); return c, ('chain', Y, (x, S, steps), p)
    return None


# ---------------------------------------------------------------- CEGAR over one hypergraph
def certify(sets, limit=None, verify=False):
    n = len(sets); m = 1 + max(max(S) for S in sets)
    deg = collections.Counter(g for S in sets for g in S)
    D = [domain(S, deg) for S in sets]
    pool = IDPool(); x = [[pool.id(('x', a, t)) for t in range(len(D[a]))] for a in range(n)]
    sol = Solver(name='cd15')
    for a in range(n):
        for cl in CardEnc.equals(lits=x[a], bound=1, vpool=pool, encoding=EncType.seqcounter).clauses:
            sol.add_clause(cl)
    boxes = 0; fails = []; kinds = collections.Counter(); t0 = time.time()
    while sol.solve():
        if limit and boxes + len(fails) >= limit: return 'LIMIT', boxes, fails, kinds, time.time() - t0
        mod = set(l for l in sol.get_model() if l > 0)
        prof = [next(t for t in range(len(D[a])) if x[a][t] in mod) for a in range(n)]
        vals = [list(D[a][prof[a]]) for a in range(n)]
        I = V.Inst(sets, vals, m)
        res = inner(I)
        if res is None:
            fails.append(vals); sol.add_clause([-x[a][prof[a]] for a in range(n)]); continue
        conds, how = res; kinds[how[0]] += 1
        T = []
        for a in range(n):
            ok = []
            for t, rep in enumerate(D[a]):
                vd = dict(zip(sets[a], rep))
                if all(f(vd) for f in conds[a]): ok.append(t)
            assert prof[a] in ok, (sets, vals, a)
            T.append(set(ok))
        if verify:                                          # replay the run on random profiles of the box
            import random
            rng = random.Random(boxes)
            for _ in range(20):
                combo = [rng.choice(sorted(Ta)) for Ta in T]
                J = V.Inst(sets, [list(D[a][combo[a]]) for a in range(n)], m)
                assert replay(J, how), (sets, combo, how)
        cl = [x[a][t] for a in range(n) for t in range(len(D[a])) if t not in T[a]]
        boxes += 1
        if not cl: break                                    # the box is the whole profile space
        sol.add_clause(cl)
    return 'DONE', boxes, fails, kinds, time.time() - t0


def replay(I, how):
    """re-run the witness's run on another profile from the raw definitions: Y a V-M matching, the trade legal, every
    placement safe, final allocation complete and EFX0"""
    kind, Y, tr, path = how
    Ys = []
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if not isinstance(r, V.Stuck): Ys.append([list(b) for b in r[0]])
    if Y not in Ys: return False
    X = [list(b) for b in Y]
    if kind == 'move':
        i, j, z, S = tr; y = Y[i][0]
        if j is None:
            if not I.val(i, S) > I.val(i, [y]): return False
            X[i] = list(S)
        else:
            Bj = [h for h in X[j] if h != z] + [y]
            if not (I.val(i, [z] + list(S)) > I.val(i, [y]) and I.val(j, Bj) > I.val(j, X[j])): return False
            X[j] = Bj; X[i] = [z] + list(S)
        if not V.is_efx0(I, X): return False
    elif kind == 'chain':
        x, S, steps = tr
        if not I.val(x, S) > I.val(x, Y[x]): return False
        X[x] = list(S)
        if not V.is_efx0(I, X): return False
        for j, g, yj in steps:
            if not I.val(j, [g]) > I.val(j, [yj]): return False
            X[j] = [g]
    for g, s in path:
        if not V.safe_add(I, X, s, g): return False
        X[s] = X[s] + [g]
    return V.is_efx0(I, X) and sorted(g for b in X for g in b) == list(range(I.m))


# ---------------------------------------------------------------- symmetry and the dense (bitmap) mode
def signature(w):
    """the order type of a strict valuation w (a vector): the order of all subset sums (all distinct for strict w)"""
    k = len(w)
    return tuple(sorted(range(1 << k), key=lambda mask: sum(w[t] for t in range(k) if mask >> t & 1)))


def automorphisms(sets, D, cap=5000):
    """hypergraph automorphisms (sigma on agents, pi on goods, pi(S_a) = S_sigma(a)) as type maps: for each automorphism
    a list tmap with tmap[a][t] = the index in D[sigma(a)] of the image of type t of agent a, and sigma"""
    n = len(sets); m = 1 + max(max(S) for S in sets)
    ags = [frozenset(a for a in range(n) if g in sets[a]) for g in range(m)]
    classes = collections.defaultdict(list)
    for g in range(m): classes[ags[g]].append(g)
    sig = [{signature(rep): t for t, rep in enumerate(D[a])} for a in range(n)]
    out = []
    for sigma in itertools.permutations(range(n)):
        if any(len(sets[sigma[a]]) != len(sets[a]) for a in range(n)): continue
        tgt = {}; ok = True
        for C, gs in classes.items():
            C2 = frozenset(sigma[a] for a in C)
            if len(classes.get(C2, [])) != len(gs): ok = False; break
            tgt[C] = classes[C2]
        if not ok: continue
        keys = list(classes)
        for perms in itertools.product(*[itertools.permutations(tgt[C]) for C in keys]):
            pi = {}
            for C, perm in zip(keys, perms):
                for g, h in zip(classes[C], perm): pi[g] = h
            inv = {h: g for g, h in pi.items()}
            tmap = []
            for a in range(n):
                b = sigma[a]; pos = {g: k for k, g in enumerate(sets[a])}
                row = []
                for rep in D[a]:
                    w = [rep[pos[inv[h]]] for h in sets[b]]
                    row.append(sig[b][signature(w)])
                tmap.append(np.array(row))
            out.append((sigma, tmap))
            if len(out) >= cap: return out
    return out


def box_of(sets, D, conds):
    n = len(sets); T = []
    for a in range(n):
        ok = []
        for t, rep in enumerate(D[a]):
            vd = dict(zip(sets[a], rep))
            if all(f(vd) for f in conds[a]): ok.append(t)
        T.append(ok)
    return T


def certify_dense(sets, limit=None, verify=False):
    """the same loop as certify(), with the covered profiles in a numpy bitmap and every box added with all its
    automorphism images"""
    n = len(sets); m = 1 + max(max(S) for S in sets)
    deg = collections.Counter(g for S in sets for g in S)
    D = [domain(S, deg) for S in sets]
    shape = tuple(len(Da) for Da in D); N = math.prod(shape)
    cov = np.zeros(shape, dtype=bool); flat = cov.reshape(-1)
    auts = automorphisms(sets, D)
    boxes = 0; fails = []; kinds = collections.Counter(); t0 = time.time(); pos = 0; CH = 1 << 20
    while True:
        while pos < N:
            chunk = flat[pos:pos + CH]; k = int(np.argmin(chunk))
            if not chunk[k]: pos += k; break
            pos += len(chunk)
        if pos >= N: break
        if limit and boxes + len(fails) >= limit: return 'LIMIT', boxes, fails, kinds, time.time() - t0
        prof = np.unravel_index(pos, shape)
        vals = [list(D[a][prof[a]]) for a in range(n)]
        res = inner(V.Inst(sets, vals, m))
        if res is None:
            fails.append(vals); flat[pos] = True; continue
        conds, how = res; kinds[how[0]] += 1
        T = box_of(sets, D, conds)
        for a in range(n): assert prof[a] in T[a], (sets, vals, a)
        if verify:
            import random
            rng = random.Random(boxes)
            for _ in range(20):
                combo = [rng.choice(Ta) for Ta in T]
                assert replay(V.Inst(sets, [list(D[a][combo[a]]) for a in range(n)], m), how), (sets, combo, how)
        for sigma, tmap in auts:
            T2 = [None] * n
            for a in range(n): T2[sigma[a]] = np.sort(tmap[a][T[a]])
            cov[np.ix_(*T2)] = True
        boxes += 1
    return 'DONE', boxes, fails, kinds, time.time() - t0


def certify_sliced(sets, limit=None, verify=False):
    """for profile spaces too large for one bitmap (pure n = 4): slice by agent 0's type, one slice per orbit of agent 0's
    types under the automorphisms that fix agent 0 (sound: the statement is invariant), a dense loop inside each slice;
    every box and its automorphism images are kept and projected into later slices"""
    n = len(sets); m = 1 + max(max(S) for S in sets)
    deg = collections.Counter(g for S in sets for g in S)
    D = [domain(S, deg) for S in sets]
    shape = tuple(len(Da) for Da in D); sub = shape[1:]; N = math.prod(sub)
    auts = automorphisms(sets, D, cap=2000)
    stab = [tmap[0] for sigma, tmap in auts if sigma[0] == 0]
    seen0 = set(); reps = []
    for t in range(shape[0]):
        if t in seen0: continue
        reps.append(t); seen0.update(int(tm[t]) for tm in stab); seen0.add(t)
    stored = []                                            # (mask over agent 0's types, [index arrays of agents 1..])
    boxes = 0; fails = []; kinds = collections.Counter(); t0 = time.time(); CH = 1 << 20
    for t_0 in reps:
        cov = np.zeros(sub, dtype=bool); flat = cov.reshape(-1)
        for mask, Ts in stored:
            if mask[t_0]: cov[np.ix_(*Ts)] = True
        pos = 0
        while True:
            while pos < N:
                chunk = flat[pos:pos + CH]; k = int(np.argmin(chunk))
                if not chunk[k]: pos += k; break
                pos += len(chunk)
            if pos >= N: break
            if limit and boxes + len(fails) >= limit: return 'LIMIT', boxes, fails, kinds, time.time() - t0
            prof = (t_0,) + tuple(int(u) for u in np.unravel_index(pos, sub))
            vals = [list(D[a][prof[a]]) for a in range(n)]
            res = inner(V.Inst(sets, vals, m))
            if res is None:
                fails.append(vals); flat[pos] = True; continue
            conds, how = res; kinds[how[0]] += 1
            T = box_of(sets, D, conds)
            for a in range(n): assert prof[a] in T[a], (sets, vals, a)
            if verify:
                import random
                rng = random.Random(boxes)
                for _ in range(20):
                    combo = [rng.choice(Ta) for Ta in T]
                    assert replay(V.Inst(sets, [list(D[a][combo[a]]) for a in range(n)], m), how), (sets, combo, how)
            for sigma, tmap in auts:
                T2 = [None] * n
                for a in range(n): T2[sigma[a]] = np.sort(tmap[a][T[a]])
                mask = np.zeros(shape[0], dtype=bool); mask[T2[0]] = True
                stored.append((mask, T2[1:]))
                if mask[t_0]: cov[np.ix_(*T2[1:])] = True
            boxes += 1
    return 'DONE', boxes, fails, kinds, time.time() - t0


def job(args):
    fn, c, limit, verify, level = args
    LEVEL[0] = level; V.FREE_Z[0] = True
    sets = c['sets']; n = len(sets); m = 1 + max(max(S) for S in sets)
    size = math.prod(288 if len(S) == 4 else 6 for S in sets)
    f = certify_dense if size <= 1.5e8 else certify_sliced
    status, boxes, fails, kinds, dt = f(sets, limit, verify)
    import vm1_chain as Ch
    fk = collections.Counter(); bad = []
    for vals in fails:
        r = Ch.one(('f', sets, vals, m)); V.FREE_Z[0] = True
        fk[r[3]] += 1
        if r[3] != 'VM1': bad.append((r[3], vals))
    return fn, c['idx'], n, m, status, boxes, dict(kinds), len(fails), dict(fk), bad[:3], dt, f.__name__


FILES = {2: ['k4_certs_2.json.gz'], 3: ['k4_certs_3.json.gz'],
         4: ['k4_certs_4_n4_1.json.gz', 'k4_certs_4_n4_2.json.gz', 'k4_certs_4_n4_3.json.gz', 'k4_certs_4_pure.json.gz']}

if __name__ == '__main__':
    import multiprocessing as mp
    N = int(sys.argv[1]); key = sys.argv[2] if len(sys.argv) > 2 and not sys.argv[2].startswith('--') else None
    opt = dict((a[2:].split('=') + ['1'])[:2] for a in sys.argv[2:] if a.startswith('--'))
    limit = int(opt['limit']) if 'limit' in opt else None; verify = 'verify' in opt
    only = [int(s) for s in opt['idx'].split(',')] if 'idx' in opt else None
    level = opt.get('level', 'chain'); procs = int(opt.get('procs', os.cpu_count()))
    print('$ python3 k4/vm/vm1chain_cert.py', ' '.join(sys.argv[1:]), flush=True)
    jobs = []
    for fn in FILES[N]:
        if key and key not in fn: continue
        for c in json.load(gzip.open(os.path.join(ROOT, 'results', fn)))['cores']:
            if only is not None and c['idx'] not in only: continue
            jobs.append((fn, c, limit, verify, level))
    tot = collections.Counter(); T0 = time.time()
    with mp.Pool(procs) as pool:
        for fn, idx, n, m, status, boxes, kinds, nf, fk, bad, dt, mode in pool.imap_unordered(job, jobs):
            tot[status] += 1; tot['boxes'] += boxes; tot['fail profiles'] += nf
            for k2, v2 in fk.items(): tot['fail ' + k2] += v2
            print('  %s idx %d n=%d m=%d: %s, %d boxes %s, %d failing profiles %s, %.1f s (%s)' % (
                fn, idx, n, m, status, boxes, kinds, nf, fk, dt, mode), flush=True)
            for lev, vals in bad:
                print('    VM1 with rotation fails (%s): %s' % (lev, json.dumps({'vals': vals})), flush=True)
    print('total', dict(tot), '; time %.0f s' % (time.time() - T0))
