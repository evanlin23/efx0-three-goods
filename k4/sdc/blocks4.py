"""Theorem A's per-block count at k = 4 (k4/sdc.md §15).  For the plain neediest-first R1 run pi (rule_order 'need2'
with R1 priority), split pi into blocks (a block starts when no unprocessed agent has lost a good).  Build LB4r's
state from the picks, run the upgrades of a policy, and for an owner o (not frozen) compute Lemma K's options
(k4/rulef_model.py services, kept set K = empty) for every agent threatened by W_o.  Per block B:
    need(B)   = least size |G u H| of a service of the threatened agents of B (slot goods and kept-out sets),
    places(B) = the slot places of B's agents other than o (capK).
Questions:
  (P) for some owner, need(B) <= places(B) for every block B (owner's block included, the owner's place excluded);
  (P') the same for every block but the owner's, and the owner's block short by at most one;
compared with Lemma K's global deficit (<= 0) and with plain extendability.

    python3 k4/sdc/blocks4.py screen|suite|cores:FILES N SEED [pol]"""
import sys, os, json, gzip, random, itertools, collections
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import completable
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4'))
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4', 'c4_verify_H'))
import lb4r as M
import rulef_model as RM

INF = float('inf')


def blocks_of(E, pi, Y):
    left = set(range(E.m)); blk = {}; b = -1; done = set()
    for i in pi:
        rest = [j for j in range(E.n) if j not in done]
        if not any(any(g not in left for g in E.R[j]) for j in rest):
            b += 1
        blk[i] = b; done.add(i)
        if Y[i] is not None: left.discard(Y[i])
    return blk


def options(inst, s, o, needs):
    """Lemma K's options per threatened agent (K = empty): list of (x, [(kind, set)]), capK; None if some x has none."""
    base, pick, marked = s
    J = [g for g in range(inst.m) if base[g] == -1]
    Bo = M.base_of(inst, s, o); Wo = set(Bo) | set(J)
    NA = set(needs[o])
    for i in range(inst.n):
        if i != o: NA |= needs[i]
    bases = [M.base_of(inst, s, i) for i in range(inst.n)]
    capK = [0 if (len(bases[x]) == 1 and bases[x][0] in NA) else max(0, 2 - len(bases[x])) for x in range(inst.n)]
    opts = []
    for x in range(inst.n):
        if x == o or not RM.threatened(inst, x, Wo, bases[x]): continue
        ox = []
        if capK[x] >= 1:
            ox += [('s', frozenset([g])) for g in J if not RM.threatened(inst, x, Wo - {g}, bases[x] + [g])]
        cand = [g for g in J if inst.v[x][g] > 0]; mins = []
        for r in range(len(cand) + 1):
            for D in itertools.combinations(cand, r):
                D = frozenset(D)
                if any(Q <= D for Q in mins): continue
                if not RM.threatened(inst, x, Wo - D, bases[x]): mins.append(D)
        ox += [('r', D) for D in mins]
        if not ox: return None, capK
        opts.append((x, ox))
    return opts, capK


def min_service(opts):
    best = [INF]
    def dfs(i, U, G):
        if len(U) >= best[0]: return
        if i == len(opts): best[0] = len(U); return
        for kind, S in opts[i][1]:
            if kind == 's' and (S & G): continue
            dfs(i + 1, U | S, G | S if kind == 's' else G)
    dfs(0, frozenset(), frozenset())
    return best[0]


def analyse(E, inst, pol):
    Y, pi = rule_order(E, 'need2', True)
    blk = blocks_of(E, pi, Y)
    base = [-1] * inst.m; pick = [-1] * inst.n
    for i, g in enumerate(Y):
        if g is not None: base[g] = i; pick[i] = g
    s = (tuple(base), tuple(pick), tuple([False] * inst.n))
    if pol != 'none': s, _ = M.up_run(inst, s, pol)
    needs = M.all_needs(inst, s); NA = M.NA_of(needs)
    om = M.omega(inst, s, needs)
    rows = []
    for o in RM.owners(inst, s, needs, NA):
        opts, capK = options(inst, s, o, needs)
        if opts is None: rows.append((o, None)); continue
        nb = max(blk.values()) + 1
        per = []
        for b in range(nb):
            ob = [(x, ox) for x, ox in opts if blk[x] == b]
            places = sum(capK[x] for x in range(inst.n) if blk[x] == b and x != o)
            per.append((min_service(ob), places, b == blk[o]))
        glob = min_service(opts) - sum(capK[x] for x in range(inst.n) if x != o)
        rows.append((o, (per, glob)))
    return Y, pi, blk, om, rows


if __name__ == '__main__':
    args = sys.argv[1:]
    pol = 'shrink'
    if args[-1] in ('shrink', 'envyFree', 'none'): pol = args.pop()
    src = args[0]; C = collections.Counter(); shown = 0
    print('$ python3 k4/sdc/blocks4.py', *sys.argv[1:])
    if src.startswith('cores:'):
        N, seed = int(args[1]), int(args[2]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    else:
        items = instances(src)
    for name, sets, vals, m in items:
        if len(sets) > 9: continue
        E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v)
        Y, pi, blk, om, rows = analyse(E, inst, pol)
        C['instances'] += 1
        ext = completable(E, Y)
        C['plain extends'] += ext
        gl = [r[1][1] for r in rows if r[1] is not None]
        Kok = om <= 0 or (gl and min(gl) <= 0)
        C['omega <= 0'] += om <= 0
        C['Lemma K (K = empty) deficit <= 0 or omega <= 0'] += Kok
        P = any(r[1] is not None and all(nd <= pl for nd, pl, _ in r[1][0]) for r in rows)
        P1 = any(r[1] is not None and all(nd <= pl + (1 if own else 0) for nd, pl, own in r[1][0]) for r in rows)
        C['(P) every block self-sufficient, some owner'] += P
        C["(P') ... owner's block short by <= 1"] += P1
        if om > 0:
            C['omega > 0: (P)'] += P
            C['omega > 0: Lemma K'] += bool(gl and min(gl) <= 0)
            C['omega > 0: Lemma K but not (P)'] += bool(gl and min(gl) <= 0) and not P
            if bool(gl and min(gl) <= 0) and not P and shown < 6:
                shown += 1
                print('K-not-P', name, 'sets', sets, 'vals', vals, 'pi', pi, 'Y', Y, 'blocks', blk)
                for o, r in rows:
                    if r: print('   owner', o, 'per-block (need, places, own)', r[0], 'global', r[1])
            nshort = min((sum(1 for nd, pl, own in r[1][0] if nd > pl) for r in rows if r[1] is not None), default=None)
            C['omega > 0: least number of short blocks = %s' % nshort] += 1
    for k in sorted(C, key=str): print(k, C[k])
