"""PS at k = 3 through LB⁺'s pre-allocations (k4/induct.md Proposition 6(b)): an exhaustive test.

Setting of proofs/lb_last_step.md §0: every agent values exactly three goods and is balanced (a k = 3 core). By
Proposition 6(a) of k4/induct.md, PS(J, w) holds iff J plus a good z valued by nobody has an EFX0 allocation giving
z to w. A completion (Theorem 1') of a valid pre-allocation P gives z to w when
  (O) w is a valid owner of P (Lemma 1 for o = w; with enough padding junk the owner's bundle has >= 4 goods), or
  (S) w is a terminal with a slot, some o != w is a valid owner, and the minimum hitting set H leaves a slot free
      (|H| <= S - cap(o) - 1), so z can sit in w's slot.
This script enumerates every run of Phase 1 (every choice at R1 steps and insertion steps), every order of LB's
upgrades, and optionally LB⁺'s rotation (Theorem B, every need chain from k* to r), and reports, per (profile, w),
whether some state gives (O) or (S). It never builds allocations; it only tests Lemma 1's exact condition, which
Theorem 1' turns into an EFX0 allocation. A few witnesses are rebuilt and checked by the raw definition
(k4/induct_bf.py) as a sanity check.

Usage: python3 k4/induct_lbo.py CERTS_K3.json.gz [--n=N] [--samples=S] [--all] [--seed=K] [--jobs=J] [--rot] [--partial]
         [--log=OUT]
  --partial: also the states where LB's upgrade loop stops early (still valid pre-allocations).
  --only-o: count only witnesses (O) (w a valid owner).
  --every-run: (implies --last) every run of Phase 1 with w last must give a witness on its own.
  --from-k4: the files are k = 4 certificates; for every profile of every core whose only 4-good agent w is P4 (one
          private good p), test J = I - p with target w (the input Theorem 4(a) needs at j = 0); w is never upgraded
          when it is top-heavy in J. Options --all / --max-all=N / --samples=S as above.
  --last: for the target w, only the runs of Phase 1 in which w is postponed to the very end (the other agents keep
          R1 priority and every choice).
"""
import gzip, json, itertools, os, random, sys, time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def runs(R, n, last=None):
    """Every run of Phase 1: yields (order, picks). R[i] = (a_i, b_i, c_i) in i's order. With last = w, agent w is
    postponed to the end (it is skipped by the R1 and insertion rules while any other agent is unprocessed)."""
    out = []
    def rec(G, done, order, Y):
        if len(done) == n:
            out.append((tuple(order), tuple(Y))); return
        und = [i for i in range(n) if i not in done and (i != last or len(done) == n - 1)]
        r1 = [i for i in und if sum(g in G for g in R[i]) <= 2]
        cands = r1 if r1 else und
        for i in cands:
            pick = next((g for g in R[i] if g in G), None)
            Y2 = list(Y); Y2[i] = pick
            rec(G - {pick} if pick is not None else G, done | {i}, order + [i], Y2)
    rec(frozenset(g for S in R for g in S), frozenset(), [], [None] * n)
    return out


def needs(R, Y, U, i):
    if i in U: return set()
    if Y[i] is None: return set(R[i])
    return set(R[i][:R[i].index(Y[i])])


def state(R, n, m, Y, U):
    NA = set().union(*[needs(R, Y, U, i) for i in range(n)])
    picks = {Y[i] for i in range(n) if Y[i] is not None}
    cs = {R[u][2] for u in U}
    J = set(range(m)) - picks - cs
    F = {i for i in range(n) if i not in U and Y[i] is not None and Y[i] in NA}
    T = [i for i in range(n) if i not in U and i not in F]
    cap = {i: (0 if i in U or i in F else (1 if Y[i] is not None else 2)) for i in range(n)}
    return NA, J, F, T, cap


NO_UPGRADE = None      # an agent that may not be upgraded (a top-heavy target: Theorem 1' needs balance for U)


def upgrades(R, n, m, Y, partial=False):
    """Every fixpoint of LB's upgrade loop, over every order (partial: every state the loop passes through; each is a
    valid pre-allocation, which is all Theorem 1' needs)."""
    res = set()
    def rec(U):
        NA, J, F, T, cap = state(R, n, m, Y, U)
        cand = [k for k in range(n) if k not in U and k != NO_UPGRADE and Y[k] == R[k][1] and R[k][2] in J
                and R[k][1] not in NA]
        if partial: res.add(frozenset(U))
        if not cand: res.add(frozenset(U)); return
        for k in cand: rec(U | {k})
    rec(frozenset())
    return res


def valid(R, n, m, Y, U):
    """(Y, U) is a pre-allocation (picks distinct, c_u distinct and not picks, Y_u = b_u) satisfying (V1), (V2)."""
    picks = [Y[i] for i in range(n) if Y[i] is not None]
    if len(set(picks)) != len(picks): return False
    for i in range(n):
        if Y[i] is not None and Y[i] not in R[i]: return False
    cs = [R[u][2] for u in U]
    if len(set(cs)) != len(cs) or set(cs) & set(picks): return False
    if any(Y[u] != R[u][1] for u in U): return False
    NA, J, F, T, cap = state(R, n, m, Y, U)
    if NA & J: return False
    if any(R[u][1] in NA or R[u][2] in NA for u in U): return False
    return True


def min_hit(pairs, J):
    pairs = [p & J for p in pairs]
    if any(not p for p in pairs): return None
    univ = sorted(set().union(*pairs)) if pairs else []
    for size in range(len(pairs) + 1):
        for H in itertools.combinations(univ, size):
            Hs = set(H)
            if all(p & Hs for p in pairs): return size
    return None


def valid_owner(R, n, Y, U, J, cap, S, o, F):
    """Lemma 1 (exact): returns the minimum hitting-set size if o is a valid owner, else None."""
    if o in F: return None
    base = ({Y[o]} if Y[o] is not None else set()) if o not in U else {R[o][1], R[o][2]}
    pairs = []
    for x in range(n):
        if x == o or x in U or Y[x] != R[x][0]: continue
        bc = {R[x][1], R[x][2]}
        if bc <= (J | base):
            if bc <= base: return None
            pairs.append(bc)
    h = min_hit(pairs, J)
    if h is None or h > S - cap[o]: return None
    return h


def rotations(R, n, m, order, Y, U):
    """LB⁺'s rotation (Theorem B) along every need chain from k* (leader of the last block) to r; returns states."""
    out = []
    notU = [i for i in order if i not in U]
    if not notU: return out
    r = notU[-1]
    # the last block's leader: the last insertion agent (R_k ⊆ G at its turn); recompute along the order
    G = set(g for S in R for g in S); leader = None
    for i in order:
        if all(g in G for g in R[i]): leader = i
        if Y[i] is not None: G.discard(Y[i])
    k = leader
    if k is None or k == r or k in U or Y[k] != R[k][0]: return out
    NA, J, F, T, cap = state(R, n, m, Y, U)
    W = set(J) | ({Y[r]} if Y[r] is not None else set())
    if not {R[k][1], R[k][2]} <= W: return out          # Theorem B needs k exposed w.r.t. r: b_k, c_k free
    def chains(x, path):
        if x == r: yield path; return
        for j in range(n):
            if j in path or j in U: continue
            if Y[x] is not None and Y[x] in needs(R, Y, U, j): yield from chains(j, path + [j])
    for path in chains(k, [k]):
        Y2 = list(Y)
        for t in range(len(path) - 1, 0, -1): Y2[path[t]] = Y[path[t - 1]]
        Y2[k] = R[k][1]
        out.append((tuple(Y2), frozenset(U | {k})))
    return out


PARTIAL = False


LAST = False
ONLY_O = False


def ps_witness(R, n, m, rot):
    """Set of agents w with a witness (O) or (S) in some state."""
    if LAST:
        good = set()
        for w in range(n):
            if w in ps_witness_runs(R, n, m, rot, runs(R, n, last=w), stop=w): good.add(w)
        return good
    return ps_witness_runs(R, n, m, rot, runs(R, n))


EVERY = False


def ps_witness_runs(R, n, m, rot, allruns, stop=None):
    if EVERY and stop is not None:
        # every run must give a witness for the target 'stop' on its own
        for run in allruns:
            if stop not in ps_witness_runs_one(R, n, m, rot, [run], stop): return set()
        return {stop}
    return ps_witness_runs_one(R, n, m, rot, allruns, stop)


def ps_witness_runs_one(R, n, m, rot, allruns, stop=None):
    good = set()
    for order, Y in allruns:
        for U in upgrades(R, n, m, Y, PARTIAL):
            sts = [(Y, U)] + (rotations(R, n, m, order, Y, U) if rot else [])
            for Ys, Us in sts:
                if not valid(R, n, m, Ys, Us): continue       # every state tested is a valid pre-allocation
                NA, J, F, T, cap = state(R, n, m, Ys, Us)
                S = sum(cap.values())
                owners = {}
                for o in list(T) + list(Us):
                    h = valid_owner(R, n, Ys, Us, J, cap, S, o, F)
                    if h is not None: owners[o] = h
                good |= set(owners)
                if ONLY_O: continue
                for w in T:
                    if cap[w] >= 1 and any(o != w and h <= S - cap[o] - 1 for o, h in owners.items()): good.add(w)
            if len(good) == n or (stop is not None and stop in good): return good
    return good


def work(args):
    global PARTIAL, LAST, ONLY_O, EVERY
    sets, prof, rot, PARTIAL, LAST, ONLY_O, EVERY = args
    n = len(sets); m = 1 + max(g for S in sets for g in S)
    R = [tuple(g for _, g in sorted(zip(t, S), reverse=True)) for S, t in zip(sets, prof)]
    return sets, prof, ps_witness(R, n, m, rot)


def work_k4(args):
    """J = I - p for a k = 4 core profile whose only 4-good agent w is P4; target w (not upgraded if top-heavy)."""
    global PARTIAL, LAST, ONLY_O, NO_UPGRADE
    sets, prof, w, p, rot, PARTIAL, LAST, ONLY_O = args
    n = len(sets)
    vals = [dict(zip(S, t)) for S, t in zip(sets, prof)]
    sets2 = [[g for g in S if g != p] for S in sets]
    goods = sorted({g for S in sets2 for g in S})
    ren = {g: k for k, g in enumerate(goods)}
    m = len(goods)
    R = [tuple(ren[g] for g in sorted(S, key=lambda g: -vals[i][g])) for i, S in enumerate(sets2)]
    vw = sorted((vals[w][g] for g in sets2[w]), reverse=True)
    NO_UPGRADE = w if vw[0] >= vw[1] + vw[2] else None
    if LAST:
        good = w in ps_witness_runs(R, n, m, rot, runs(R, n, last=w), stop=w)
    else:
        good = w in ps_witness_runs(R, n, m, rot, runs(R, n), stop=w)
    return sets, prof, w, good, NO_UPGRADE is not None


def main_k4(files, opt, log):
    sys.path.insert(0, HERE)
    from induct_run import domain
    rng = random.Random(int(opt.get('seed', 1)))
    tasks = []
    for fn in files:
        for c in json.load(gzip.open(fn))['cores']:
            sets, m = c['sets'], c['m']
            deg = [sum(g in S for S in sets) for g in range(m)]
            four = [i for i, S in enumerate(sets) if len(S) == 4]
            if len(four) != 1: continue
            w = four[0]; priv = [g for g in sets[w] if deg[g] == 1]
            if len(priv) != 1: continue
            doms = [domain(S, deg) for S in sets]
            tot = 1
            for D in doms: tot *= len(D)
            profs = list(itertools.product(*doms)) if (opt.get('all') or tot <= int(opt.get('max-all', 0))) else \
                [tuple(rng.choice(D) for D in doms) for _ in range(int(opt.get('samples', 20)))]
            for pr in profs:
                tasks.append((sets, pr, w, priv[0], bool(opt.get('rot')), bool(opt.get('partial')), bool(opt.get('last')),
                              bool(opt.get('only-o'))))
    log(f'{len(tasks)} (k = 4 core, profile) pairs with one 4-good agent, a P4 agent w; test J = I - p with target w')
    t0 = time.time(); miss = 0; th = 0; ex = []
    with Pool(int(opt.get('jobs', 4))) as pool:
        for sets, prof, w, good, topheavy in pool.imap_unordered(work_k4, tasks, chunksize=8):
            th += topheavy
            if not good:
                miss += 1
                if len(ex) < 5: ex.append((sets, [list(t) for t in prof], w))
    log(f'time {time.time() - t0:.1f}s; tests: {len(tasks)} (w top-heavy in J: {th}); without a witness: {miss}')
    for e in ex: log(f'  no witness: sets={e[0]} values={e[1]} w={e[2]}')


def main():
    argv = sys.argv[1:]
    if '--from-k4' in argv:
        files = [a for a in argv if not a.startswith('--')]
        opt = {a.split('=')[0][2:]: (a.split('=', 1)[1] if '=' in a else True) for a in argv if a.startswith('--')}
        logf = open(opt['log'], 'w') if 'log' in opt else None
        def log(s):
            print(s, flush=True)
            if logf: logf.write(s + '\n'); logf.flush()
        log('command: python3 k4/induct_lbo.py ' + ' '.join(argv))
        return main_k4(files, opt, log)
    files = [a for a in argv if not a.startswith('--')]
    opt = {a.split('=')[0][2:]: (a.split('=', 1)[1] if '=' in a else True) for a in argv if a.startswith('--')}
    rng = random.Random(int(opt.get('seed', 1)))
    logf = open(opt['log'], 'w') if 'log' in opt else None
    def log(s):
        print(s, flush=True)
        if logf: logf.write(s + '\n'); logf.flush()
    log('command: python3 k4/induct_lbo.py ' + ' '.join(argv))
    rot = bool(opt.get('rot')); partial = bool(opt.get('partial')); last = bool(opt.get('last')); only_o = bool(opt.get('only-o')); every = bool(opt.get('every-run'))
    if every: last = True
    tasks = []
    for fn in files:
        data = json.load(gzip.open(fn)); cores = data if isinstance(data, list) else data['cores']
        for c in cores:
            if 'n' in opt and len(c['sets']) != int(opt['n']): continue
            sets = c['sets']
            if any(len(S) != 3 for S in sets): continue
            perms = list(itertools.permutations(range(3)))
            if opt.get('all'):
                for pr in itertools.product(perms, repeat=len(sets)):
                    tasks.append((sets, [[p[0] + 2, p[1] + 2, p[2] + 2] for p in pr], rot, partial, last, only_o, every))
            else:
                for _ in range(int(opt.get('samples', 50))):
                    tasks.append((sets, [[x + 2 for x in rng.choice(perms)] for _ in sets], rot, partial, last, only_o, every))
    log(f'{len(tasks)} (core, ranking profile) pairs; rotation states {"included" if rot else "not included"}; '
        f'upgrade loop {"stopped anywhere" if partial else "run to a fixpoint"}; '
        f'{"the target w is processed last in Phase 1" if last else "every run of Phase 1"}; '
        f'witness {"(O) only" if only_o else "(O) or (S)"}{"; EVERY run with w last must work" if every else ""}')
    t0 = time.time(); tot = 0; miss = 0; ex = []
    with Pool(int(opt.get('jobs', 4))) as pool:
        for sets, prof, good in pool.imap_unordered(work, tasks, chunksize=8):
            tot += len(sets); miss += len(sets) - len(good)
            if len(good) < len(sets) and len(ex) < 5: ex.append((sets, prof, sorted(set(range(len(sets))) - good)))
    log(f'time {time.time() - t0:.1f}s; (profile, w) pairs: {tot}; without an LB⁺ witness (O) or (S): {miss}')
    for e in ex: log(f'  no witness: sets={e[0]} values={e[1]} agents={e[2]}')


if __name__ == '__main__':
    main()
