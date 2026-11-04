"""Owner-free per-block surplus (k4/sdc.md §15).  For the plain neediest-first R1 run pi with LB4r upgrades of a policy:
threats from the unpicked goods J alone (x is threatened if some set of its goods in J, less one good, is worth more
than its base); every agent's slot places counted (capK, frozen agents 0).  Per block B:
    d(B) = places(B) - need(B),   need(B) = least |G u H| of a Lemma K service of B's threatened agents (W = J).
Reports the distribution of d(B), the number of blocks with d(B) < 0, and how this relates to omega, to Lemma K's
deficit (best owner, K = empty) and to plain extendability; 'thr-free' = the block has a threatened free agent.

    python3 k4/sdc/blocks4j.py screen|suite|cores:FILES N SEED [pol]"""
import sys, os, json, gzip, random, itertools, collections
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import completable
from blocks4 import blocks_of, min_service, M, RM

INF = float('inf')


def options_J(inst, s, needs):
    base = s[0]; J = [g for g in range(inst.m) if base[g] == -1]; W = set(J)
    NA = M.NA_of(needs)
    bases = [M.base_of(inst, s, i) for i in range(inst.n)]
    capK = [0 if (len(bases[x]) == 1 and bases[x][0] in NA) else max(0, 2 - len(bases[x])) for x in range(inst.n)]
    opts = {}
    for x in range(inst.n):
        if not RM.threatened(inst, x, W | {-1}, bases[x]) and not RM.threatened(inst, x, W, bases[x]): continue
        ox = []
        if capK[x] >= 1:
            ox += [('s', frozenset([g])) for g in J if not RM.threatened(inst, x, (W - {g}) | {-1}, bases[x] + [g])]
        cand = [g for g in J if inst.v[x][g] > 0]; mins = []
        for r in range(len(cand) + 1):
            for D in itertools.combinations(cand, r):
                D = frozenset(D)
                if any(Q <= D for Q in mins): continue
                if not RM.threatened(inst, x, (W - D) | {-1}, bases[x]): mins.append(D)
        ox += [('r', D) for D in mins]
        opts[x] = ox
    return opts, capK


def threatened_dummy(inst, x, L, H):
    L = [g for g in L if g != -1] + ([-1] if -1 in L else [])
    vals = [inst.v[x][g] if g >= 0 else 0 for g in L]
    if not vals: return False
    return sum(vals) - min(vals) > sum(inst.v[x][g] for g in H)


RM.threatened = threatened_dummy   # the owner's bundle always holds a good x does not value (the -1 dummy)

if __name__ == '__main__':
    args = sys.argv[1:]; pol = 'shrink'
    if args[-1] in ('shrink', 'envyFree', 'none'): pol = args.pop()
    src = args[0]; C = collections.Counter(); shown = 0
    print('$ python3 k4/sdc/blocks4j.py', *sys.argv[1:])
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
        Y, pi = rule_order(E, 'need2', True); blk = blocks_of(E, pi, Y)
        base = [-1] * m; pick = [-1] * inst.n
        for i, g in enumerate(Y):
            if g is not None: base[g] = i; pick[i] = g
        s = (tuple(base), tuple(pick), tuple([False] * inst.n))
        if pol != 'none': s, _ = M.up_run(inst, s, pol)
        needs = M.all_needs(inst, s); NA = M.NA_of(needs); fr = M.frozen_pre(inst, s, NA)
        C['instances'] += 1
        om = M.omega(inst, s, needs)
        opts, capK = options_J(inst, s, needs)
        if any(not ox for ox in opts.values()): C['some agent has no option'] += 1; continue
        nb = max(blk.values()) + 1; ds = []
        for b in range(nb):
            ob = [(x, ox) for x, ox in opts.items() if blk[x] == b]
            places = sum(capK[x] for x in range(inst.n) if blk[x] == b)
            d = places - min_service(ob)
            tf = any(blk[x] == b and not fr[x] and capK[x] >= 1 for x in opts)
            ds.append((d, tf))
            C['block d = %d%s' % (d, ' thr-free' if tf else '')] += 1
        neg = sum(1 for d, _ in ds if d < 0)
        ext = completable(E, Y)
        C['omega %s, blocks with d < 0: %d, plain extends %s' % ('> 0' if om > 0 else '<= 0', neg, ext)] += 1
        if neg >= 2 and shown < 5:
            shown += 1
            print('two short blocks', name, 'sets', sets, 'vals', vals, 'pi', pi, 'Y', Y, 'blocks', blk, 'd', ds, 'omega', om, 'ext', ext)
    for k in sorted(C, key=str): print(k, C[k])
