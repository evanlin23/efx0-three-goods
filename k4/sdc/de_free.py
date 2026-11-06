"""Draft and Exchange's moves at k = 4 with a free completion (k4/sdc.md §29).  States: partial allocations B (each
agent a base inside R_i; the rest is junk J).  Terminal: the bases extend to a complete EFX0
allocation (junk anywhere; SAT, imp_extend.extends).  Moves, each strictly improving every agent it touches (others
unchanged), so every reached state value-dominates the start:
  chain: x_0 takes H_0 (goods of J, or of B_{x_t}), each x_i (i >= 1) takes B_{x_{i-1}} plus H_i from J, the old base
         of x_t becomes junk (t >= 0; t = 0: x_0 just adds or swaps in junk goods);
  ring:  w_0 -> ... -> w_{k-1} -> w_0 (k >= 2), each w_{t+1} takes B_{w_t} plus H_{t+1} from J;
with the H's disjoint and inside the receiver's relevant goods, |H| <= DF_HMAX (default 4) and bases of at most
DF_BMAX (default 4) goods.  Search: BFS from the serial-dictatorship start of every order (n <= 4 by default),
reachable set capped.  Question: does a monotone path reach an extendable state from every order?

    python3 k4/sdc/de_free.py screen|suite|special|logs|cores:FILES N SEED [moves:chain]
    DF_NMAX (default 4): skip larger instances (every order is tried)."""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from nof_var import SPECIAL
from pysat.solvers import Cadical153

CHAIN_ONLY = False
NMAX = int(os.environ.get('DF_NMAX', '4')); CAP = int(os.environ.get('DF_CAP', '3000'))


def extends(E, base):
    cl = list(E.cl)
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
        if base[g] >= 0: cl.append([E.x[g][base[g]]])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok


def bundles(E, base):
    B = [[] for _ in range(E.n)]
    for g, a in enumerate(base):
        if a >= 0: B[a].append(g)
    return B


HMAX = int(os.environ.get('DF_HMAX', '4')); BMAX = int(os.environ.get('DF_BMAX', '4'))


def subsets_le2(xs):
    """subsets of xs of size at most HMAX (the name is historical)"""
    for r in range(min(HMAX, len(xs)) + 1):
        yield from itertools.combinations(xs, r)


def moves(E, base, describe=False):
    """the states one move reaches; with describe, a dict state -> (kind, agents, H per agent) for one move to it"""
    n = E.n; B = bundles(E, base); J = [g for g in range(E.m) if base[g] < 0]
    val = lambda i, S: sum(E.v[i].get(g, 0) for g in S)
    out = set(); desc = {}
    # chains (simple paths x_0, ..., x_t)
    def ext_chain(path, usedH, assign):
        x_t = path[-1]
        # close: x_0 takes H_0 from J (minus used) or B_{x_t}
        pool0 = [g for g in J if g not in usedH and E.v[path[0]].get(g, 0) > 0] + \
                ([g for g in B[x_t] if E.v[path[0]].get(g, 0) > 0] if len(path) > 1 else [])
        for H0 in subsets_le2(pool0):
            if not H0: continue
            newb0 = (list(B[path[0]]) if len(path) == 1 else []) + list(H0)
            if len(newb0) > BMAX or val(path[0], newb0) <= val(path[0], B[path[0]]): continue
            nb = list(base)
            if len(path) > 1:
                for g in B[x_t]: nb[g] = -1
                for i in range(len(path) - 1, 0, -1):
                    for g in B[path[i - 1]]: nb[g] = path[i]
                    for g in assign[i]: nb[g] = path[i]
            for g in H0: nb[g] = path[0]
            out.add(tuple(nb)); desc.setdefault(tuple(nb), ('chain', tuple(path), {0: H0, **assign}))
        if len(path) >= n: return
        # extend: next agent y takes B_{x_t} plus H from J
        if not B[x_t]: return
        for y in range(n):
            if y in path: continue
            free = [g for g in J if g not in usedH and E.v[y].get(g, 0) > 0]
            for H in subsets_le2(free):
                nby = list(B[x_t]) + list(H)
                if len(nby) > BMAX or val(y, nby) <= val(y, B[y]): continue
                ext_chain(path + [y], usedH | set(H), {**assign, len(path): H})
    for x in range(n): ext_chain([x], frozenset(), {})
    if CHAIN_ONLY: return desc if describe else out
    # rings
    def ext_ring(path, usedH, assign):
        x_t = path[-1]
        if not B[x_t]: return
        for y in range(n):
            if y in path[1:]: continue
            free = [g for g in J if g not in usedH and E.v[y].get(g, 0) > 0]
            for H in subsets_le2(free):
                nby = list(B[x_t]) + list(H)
                if len(nby) > BMAX or val(y, nby) <= val(y, B[y]): continue
                if y == path[0]:
                    if len(path) < 2: continue
                    nb = list(base)
                    for i in range(len(path)):
                        nxt = path[(i + 1) % len(path)]
                        for g in B[path[i]]: nb[g] = nxt
                    for i, Hs in {**assign, 0: H}.items():
                        for g in Hs: nb[g] = path[i]
                    out.add(tuple(nb)); desc.setdefault(tuple(nb), ('ring', tuple(path), {**assign, 0: H}))
                elif len(path) < n:
                    ext_ring(path + [y], usedH | set(H), {**assign, len(path): H})
    for x in range(n): ext_ring([x], frozenset(), {})
    return desc if describe else out


def search(E, start, memo):
    def ok(b):
        if b not in memo: memo[b] = extends(E, b)
        return memo[b]
    frontier = [start]; seen = {start}; d = 0
    while frontier:
        for b in frontier:
            if ok(b): return d
        nxt = []
        for b in frontier:
            for b2 in moves(E, b):
                if b2 not in seen:
                    seen.add(b2); nxt.append(b2)
                    if len(seen) > CAP: return 'cap'
        frontier = nxt; d += 1
    return None


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    CHAIN_ONLY = 'moves:chain' in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith('moves:')]
    print('$ python3 k4/sdc/de_free.py', *sys.argv[1:], flush=True)
    if src == 'special': items = SPECIAL
    elif src.startswith('cores:'):
        N, seed = int(args[1]), int(args[2]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    elif src == 'logs':
        import re, glob
        seen = set(); items = []
        for f in sorted(glob.glob(os.path.join(_paths.ROOT, 'results', 'k4_sdc', '*.log'))):
            for line in open(f, errors='ignore'):
                for mt in re.finditer(r'(\[\[\[[0-9, \[\]]+\]\], \[\[[0-9, \[\]]+\]\]\])', line):
                    try: sets, vals = json.loads(mt.group(1))
                    except Exception: continue
                    if not all(len(a) == len(b) for a, b in zip(sets, vals)) or max(len(a) for a in sets) > 4: continue
                    key = json.dumps((sets, vals))
                    if key in seen: continue
                    seen.add(key); items.append(('log%d' % len(items), sets, vals, 1 + max(max(a) for a in sets)))
    else:
        items = instances(src)
    for name, sets, vals, m in items:
        n = len(sets)
        if n > NMAX: continue
        E = Enc(sets, vals, m); memo = {}; C['instances'] += 1; res = {}
        for o in itertools.permutations(range(n)):
            Y = tuple(sd(E, list(o))[0])
            if Y not in res:
                base = [-1] * m
                for i, g in enumerate(Y):
                    if g is not None: base[g] = i
                res[Y] = search(E, tuple(base), memo)
            C['starts'] += 1; C['start: least depth %s' % res[Y]] += 1
        bad = [Y for Y, d in res.items() if d is None or d == 'cap']
        C['instances with a start without a monotone repair'] += bool(bad)
        if bad and C['shown'] < 4:
            C['shown'] += 1; print('NO MONOTONE REPAIR', name, json.dumps((sets, vals)), 'picks', bad[0], res[bad[0]], flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
