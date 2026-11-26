"""Shared model for the Haxell-type searches (k4/haxell.md §2).

State: a complete allocation together with a base/junk label on every good.
  own[g]  the agent holding good g (every good is held: the allocation is complete);
  isb[g]  True if g belongs to its holder's base, False if it is junk.
The base of agent i is {g : own[g] = i, isb[g]}; the start is the serial-dictatorship picks as bases, every unpicked
good junk, all junk with one agent (the absorber).

An agent is *happy* (matched, in Haxell's language) if it strongly envies nobody, by the raw EFX0 definition:
v_i(X_i) >= v_i(X_j minus h) for every j != i and every h in X_j.  A state with every agent happy is an EFX0
allocation (no SAT, no L5 model).

Model G (pool=True in start_state): the unpicked goods start unallocated (own = -1, "the pool"); a state is
admissible when every agent is happy with respect to the allocated bundles (a partial EFX0 allocation), and the
unmatched units of the tree are the pool goods.  Nothing ever returns to the pool.

Moves (each returns a new state):
  ('T', g, b)              junk good g moves to agent b (any agent);
  ('C', path, H, dest)     an improving chain of k4/sdc.md §29 on the bases: x_0 takes H_0 (junk goods, from wherever
                           they lie, or goods of B_{x_t}); each x_i (i >= 1) takes B_{x_{i-1}} plus junk H_i; for t >= 1
                           the rest of B_{x_t} becomes junk and goes to agent dest; t = 0 adds junk to x_0's base.
                           Every chain agent's base value strictly rises (as in de_free.py).
  ('D', a, H, dest)        (optional) a re-base without the value condition: agent a's base becomes H (junk goods of
                           R_a, |H| >= 1), its old base becomes junk at dest.  This is Haxell's "a matched player may
                           switch to any configuration"; it can lower a's value.
"""
import sys, os, itertools, random
HERE = os.path.dirname(os.path.abspath(__file__))
SDC = os.path.join(os.path.dirname(HERE), 'sdc')
if SDC not in sys.path:
    sys.path.insert(0, SDC)
import _paths  # noqa: F401  (adds k4/sdc, k4/de4, k3)
from sdc_orders import sd  # noqa: E402

HMAX = int(os.environ.get('HT_HMAX', '3'))
BMAX = int(os.environ.get('HT_BMAX', '4'))


class Inst:
    def __init__(self, sets, vals, m, name=''):
        self.n = len(sets); self.m = m; self.name = name
        self.R = [list(s) for s in sets]
        self.v = [dict(zip(s, vv)) for s, vv in zip(sets, vals)]
        self.sets = sets; self.vals = vals

    def val(self, i, S):
        vi = self.v[i]
        return sum(vi.get(g, 0) for g in S)


def bundles(I, own):
    """bundles of the agents; own[g] = -1 means g is in the pool (unallocated, Model G)"""
    X = [[] for _ in range(I.n)]
    for g, a in enumerate(own):
        if a >= 0:
            X[a].append(g)
    return X


def happy_vec(I, own, X=None):
    """happy[i] for every agent, raw EFX0"""
    if X is None:
        X = bundles(I, own)
    out = []
    for i in range(I.n):
        vi = I.v[i]; mine = sum(vi.get(g, 0) for g in X[i]); ok = True
        for j in range(I.n):
            if j == i or len(X[j]) < 2:
                continue
            vals = [vi.get(g, 0) for g in X[j]]
            if sum(vals) - min(vals) > mine:
                ok = False; break
        out.append(ok)
    return out


def start_state(I, order, absorber=None, pool=False):
    """the serial-dictatorship start; junk with the absorber (Model A) or in the pool (pool=True, Model G)"""
    Y = sd(I, list(order))[0]
    own = [None] * I.m; isb = [False] * I.m
    for i, g in enumerate(Y):
        if g is not None:
            own[g] = i; isb[g] = True
    o = -1 if pool else (order[-1] if absorber is None else absorber)
    for g in range(I.m):
        if own[g] is None:
            own[g] = o
    return (tuple(own), tuple(isb)), tuple(Y)


def bases(I, st):
    own, isb = st
    B = [[] for _ in range(I.n)]
    for g in range(I.m):
        if isb[g]:
            B[own[g]].append(g)
    return B


def apply(I, st, mv):
    own, isb = list(st[0]), list(st[1])
    if mv[0] == 'T':
        _, g, b = mv
        own[g] = b
    elif mv[0] == 'C':
        _, path, H, dest = mv
        B = bases(I, st)
        t = len(path) - 1
        if t >= 1:
            xt = path[-1]
            for g in B[xt]:
                isb[g] = False; own[g] = dest
            for i in range(t, 0, -1):
                for g in B[path[i - 1]]:
                    own[g] = path[i]; isb[g] = True
                for g in H.get(i, ()):
                    own[g] = path[i]; isb[g] = True
        for g in H.get(0, ()):
            own[g] = path[0]; isb[g] = True
    elif mv[0] == 'D':
        _, a, H, dest = mv
        B = bases(I, st)
        for g in B[a]:
            isb[g] = False; own[g] = dest
        for g in H:
            own[g] = a; isb[g] = True
    return (tuple(own), tuple(isb))


def subsets_upto(xs, k, lo=1):
    for r in range(lo, min(k, len(xs)) + 1):
        yield from itertools.combinations(xs, r)


def chain_moves(I, st, start=None, dests=None):
    """improving chains (k4/sdc.md §29); start: restrict x_0; dests: destinations of the released goods"""
    own, isb = st
    n = I.n; B = bases(I, st)
    J = [g for g in range(I.m) if not isb[g]]
    val = I.val
    dests = list(range(n)) if dests is None else dests

    def ext(path, used, assign):
        xt = path[-1]
        pool0 = [g for g in J if g not in used and I.v[path[0]].get(g, 0) > 0]
        if len(path) > 1:
            pool0 += [g for g in B[xt] if I.v[path[0]].get(g, 0) > 0]
        for H0 in subsets_upto(pool0, HMAX):
            nb0 = (list(B[path[0]]) if len(path) == 1 else []) + list(H0)
            if len(nb0) > BMAX or val(path[0], nb0) <= val(path[0], B[path[0]]):
                continue
            H = dict(assign); H[0] = H0
            if len(path) == 1:
                yield ('C', tuple(path), H, None)
            else:
                rest = [g for g in B[xt] if g not in H0]
                for d in (dests if rest else [path[-1]]):
                    yield ('C', tuple(path), H, d)
        if len(path) >= n or not B[xt]:
            return
        for y in range(n):
            if y in path:
                continue
            free = [g for g in J if g not in used and I.v[y].get(g, 0) > 0]
            for Hy in subsets_upto(free, HMAX, lo=0):
                nby = list(B[xt]) + list(Hy)
                if len(nby) > BMAX or val(y, nby) <= val(y, B[y]):
                    continue
                a2 = dict(assign); a2[len(path)] = Hy
                yield from ext(path + [y], used | set(Hy), a2)

    for x in (range(n) if start is None else [start]):
        yield from ext([x], frozenset(), {})


def transfer_moves(I, st, pool_only=None):
    """junk good g to agent b (pool goods included; nothing ever returns to the pool)"""
    own, isb = st
    for g in range(I.m):
        if not isb[g] and (pool_only is None or (own[g] < 0) == pool_only):
            for b in range(I.n):
                if b != own[g]:
                    yield ('T', g, b)


def rebase_moves(I, st, agent=None, dests=None):
    own, isb = st
    J = [g for g in range(I.m) if not isb[g]]
    B = bases(I, st)
    dests = list(range(I.n)) if dests is None else dests
    for a in (range(I.n) if agent is None else [agent]):
        mine = [g for g in J if I.v[a].get(g, 0) > 0]
        for H in subsets_upto(mine, HMAX):
            if len(H) > BMAX:
                continue
            for d in (dests if B[a] else [a]):
                yield ('D', a, H, d)


def touched(I, st, mv):
    """goods whose holder or label the move changes"""
    st2 = apply(I, st, mv)
    return frozenset(g for g in range(I.m) if st[0][g] != st2[0][g] or st[1][g] != st2[1][g])


def instances(src):
    """(name, sets, vals, m) from the project's sets: special, screen, suite, logs, rand:N:SEED:NMIN:NMAX"""
    import json, random, re, glob
    if src == 'special':
        from nof_var import SPECIAL
        return list(SPECIAL)
    if src in ('screen', 'suite'):
        from sdc_need import instances as inst
        return inst(src)
    if src == 'logs':
        seen = set(); items = []
        for f in sorted(glob.glob(os.path.join(_paths.ROOT, 'results', 'k4_sdc', '*.log'))):
            for line in open(f, errors='ignore'):
                for mt in re.finditer(r'(\[\[\[[0-9, \[\]]+\]\], \[\[[0-9, \[\]]+\]\]\])', line):
                    try:
                        sets, vals = json.loads(mt.group(1))
                    except Exception:
                        continue
                    if not all(len(a) == len(b) for a, b in zip(sets, vals)) or max(len(a) for a in sets) > 4:
                        continue
                    key = json.dumps((sets, vals))
                    if key in seen:
                        continue
                    seen.add(key); items.append(('log%d' % len(items), sets, vals, 1 + max(max(a) for a in sets)))
        return items
    if src.startswith('cores:'):
        # cores:FILE1,FILE2:N:SEED  random strict profiles of certified k = 4 cores
        import gzip
        _, files, N, seed = src.split(':')
        rng = random.Random(int(seed))
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in files.split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        items = []
        for t in range(int(N)):
            sets = rng.choice(cores)
            items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
        return items
    if src.startswith('gen:'):
        # gen:N:SEED:n:m:k  random instances: every agent values k random goods (k = m: every good), every good
        # valued by someone, values distinct integers per agent from 1..40
        _, N, seed, n, m, k = src.split(':')
        N, n, m, k = int(N), int(n), int(m), int(k)
        rng = random.Random(int(seed)); items = []
        while len(items) < N:
            sets = [sorted(rng.sample(range(m), min(k, m))) for _ in range(n)]
            if len(set().union(*map(set, sets))) < m:
                continue
            vals = [rng.sample(range(1, 41), len(s)) for s in sets]
            items.append(('g%d' % len(items), sets, vals, m))
        return items
    raise ValueError(src)
