"""Adversarial climb against OC1^max (K4.SDC.OC1MAX) inside the (4, 3) cell, with the independent checker
k4/p3/oc1max.py. State: a (4, 3) core (k4/check4.is_core: connected, degrees 3 or 4, at most d - 2 private goods; every
good valued by at most 3 agents, or 2 with --p=2) with one strict balanced type per agent from k4/check4.core_domains
(which also enforces (C4) for two private goods). Score over the distinct maximum-matching pick vectors of all orders:
    1000 * (vectors with no one-absorber completion even after one move) + 10 * (vectors that need a move)
    + sum over vectors needing a move of (CAP - repairing moves found, capped at CAP)
Mutations: a new type for one agent (70%), or one relevant good of one agent replaced by another good or a fresh one
(30%), kept only if the result is again a (4, 3) core. Accept if the score does not drop; restart every --steps steps.
Prints every state whose score reaches a new maximum, and every failing pick vector (FAIL lines, JSON).
    python3 k4/p3/oc1max_climb.py --n=6 --runs=4 --steps=150 [--p=3] [--seed=1] [--procs=1]
    python3 k4/p3/oc1max_climb.py --start='{"sets": ..., "vals": ...}' --runs=4 --steps=150   (climb from a given core)
"""
import sys, os, json, random, itertools, collections, time, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
from p3lib import Inst, sd, random_core43
from oc1max import Checker, nu
import check4

CAP = 6


def score(sets, vals, m):
    I = Inst(sets, vals, m); K = Checker(I); N = nu(I)
    pks = set(tuple(sd(I, o)) for o in itertools.permutations(range(I.n)))
    s = 0; fails = []; need = 0
    for pk in pks:
        if sum(x is not None for x in pk) != N: continue
        base = tuple(frozenset([p]) if p is not None else frozenset() for p in pk)
        if K.complete(base) is not None: continue
        rep = 0
        for st in K.moves(base):
            if K.complete(st) is not None:
                rep += 1
                if rep >= CAP: break
        if rep == 0: fails.append(pk); s += 1000
        else: need += 1; s += 10 + (CAP - rep)
    K.close()
    return s, fails, need


def valid(sets, m, P):
    if max(sum(g in S for S in sets) for g in range(m)) > P: return False
    if sorted(set().union(*map(set, sets))) != list(range(m)): return False
    return check4.is_core(len(sets), m, sets, False)[0]


def run(args):
    n, steps, seed, P, start = args
    rng = random.Random(seed); out = []
    if start:                                   # a given (4, 3) core; its own values are replaced by the nearest
        sets = [sorted(S) for S in start['sets']]; m = 1 + max(max(S) for S in sets)   # type of the same ranking
        assert valid(sets, m, P), 'seed is not a (4, 3) core'
        doms = check4.core_domains(sets, m, False)
        def rank_of(d, S): return tuple(sorted(S, key=lambda g: -d[g]))
        ty = []
        for i, D in enumerate(doms):
            want = rank_of(dict(zip(start['sets'][i], start['vals'][i])), sets[i])
            cand = [k for k, d in enumerate(D) if rank_of(d, sets[i]) == want] or list(range(len(D)))
            ty.append(rng.choice(cand))
    else:
        rc = None
        while rc is None:
            rc = random_core43(rng, n)
            if rc and not valid(rc[1], rc[0], P): rc = None
        m, sets = rc
        doms = check4.core_domains(sets, m, False)
        ty = [rng.randrange(len(D)) for D in doms]
    vals_of = lambda sets, doms, ty: [[doms[i][ty[i]][g] for g in sets[i]] for i in range(len(sets))]
    cur, fails, need = score(sets, vals_of(sets, doms, ty), m); best = cur
    for st in range(steps):
        if rng.random() < 0.7:
            i = rng.randrange(n); nt = list(ty); nt[i] = rng.randrange(len(doms[i])); ns, nm, nd = sets, m, doms
        else:
            i = rng.randrange(n); k = rng.randrange(len(sets[i]))
            g = rng.choice([h for h in range(m + 1) if h not in sets[i]])
            ns = [list(S) for S in sets]; ns[i][k] = g
            used = sorted(set().union(*map(set, ns))); ren = {h: j for j, h in enumerate(used)}
            ns = [sorted(ren[h] for h in S) for S in ns]; nm = len(used)
            if not valid(ns, nm, P): continue
            nd = check4.core_domains(ns, nm, False)
            if any(not D for D in nd): continue
            nt = [rng.randrange(len(D)) for D in nd]
        s, f, nd_ = score(ns, vals_of(ns, nd, nt), nm)
        if f:
            out.append(('FAIL', ns, vals_of(ns, nd, nt), f))
        if s >= cur:
            sets, m, doms, ty, cur = ns, nm, nd, nt, s
            if s > best:
                best = s; out.append(('BEST', s, sets, vals_of(sets, doms, ty)))
    return n, seed, best, out


if __name__ == '__main__':
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--'))
    n, runs, steps = int(opt.get('n', 6)), int(opt.get('runs', 4)), int(opt.get('steps', 150))
    P, seed = int(opt.get('p', 3)), int(opt.get('seed', 1))
    print('$ python3 k4/p3/oc1max_climb.py ' + ' '.join(sys.argv[1:]), flush=True)
    start = json.loads(opt['start']) if opt.get('start') else None
    if start: n = len(start['sets'])
    t0 = time.time(); tasks = [(n, steps, seed * 1000 + r, P, start) for r in range(runs)]
    with mp.Pool(int(opt.get('procs', 1))) as pool:
        for n_, sd_, best, out in pool.imap_unordered(run, tasks):
            for o in out:
                if o[0] == 'FAIL': print('FAIL', json.dumps({'sets': o[1], 'vals': o[2], 'picks': o[3]}), flush=True)
            last = [o for o in out if o[0] == 'BEST']
            print(f'run seed {sd_}: n = {n_}, best score {best}' + (f'; best state {json.dumps({"sets": last[-1][2], "vals": last[-1][3]})}' if last else '')
                  + f'  [{time.time()-t0:.0f}s]', flush=True)
    print(f'done in {time.time()-t0:.0f}s')
