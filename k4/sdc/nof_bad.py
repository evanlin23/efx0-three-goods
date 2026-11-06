"""The plain-run failures of NOF-R1 (k4/sdc.md §15).  For the plain neediest-first R1 run whose picks do not extend:
LB4r's state after need-shrinking upgrades; the owner-free slack D = S - need_J (S = all slot places, need_J = least
Lemma K service of the agents threatened by the unpicked goods J alone, sharing allowed); for every owner o (not
frozen), Lemma K's deficit with K = empty, split as  deficit_o = -D + cap(o) - [o threatened by J] + extra_o
(extra_o: what the owner's base adds); the deferrals that work, and what the deferred agent is.

    python3 k4/sdc/nof_bad.py screen|suite|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import completable, sd
import blocks4 as B4
import blocks4j as BJ
from blocks4 import blocks_of, M, RM

thrJ = RM.threatened          # blocks4j patched RM.threatened to the 'dummy good in the bundle' form


def state(inst, Y, pol='shrink'):
    base = [-1] * inst.m; pick = [-1] * inst.n
    for i, g in enumerate(Y):
        if g is not None: base[g] = i; pick[i] = g
    s = (tuple(base), tuple(pick), tuple([False] * inst.n))
    return M.up_run(inst, s, pol)


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); shown = 0
    print('$ python3 k4/sdc/nof_bad.py', *sys.argv[1:])
    if src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
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
        E = Enc(sets, vals, m)
        Y, pi = rule_order(E, 'need2', True)
        if completable(E, Y): continue
        v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v); n = inst.n
        s, ups = state(inst, Y)
        needs = M.all_needs(inst, s); NA = M.NA_of(needs); fr = M.frozen_pre(inst, s, NA)
        optsJ, capK = BJ.options_J(inst, s, needs)
        S = sum(capK); needJ = B4.min_service(list(optsJ.items()))
        D = S - needJ
        C['failures'] += 1
        C['owner-free slack D = %d' % D] += 1
        rows = []
        for o in RM.owners(inst, s, needs, NA):
            opts, ck = B4.options(inst, s, o, needs)
            if opts is None: rows.append((o, None)); continue
            dfc = B4.min_service(opts) - sum(ck[x] for x in range(n) if x != o)
            extra = dfc + D - capK[o] + (1 if o in optsJ else 0)
            rows.append((o, dfc, capK[o], o in optsJ, extra))
        best = min((r[1] for r in rows if r[1] is not None), default=None)
        C['best owner deficit %s' % best] += 1
        works = [o for o in pi if completable(E, sd(E, [i for i in pi if i != o] + [o])[0])]
        blk = blocks_of(E, pi, Y)
        for k in works:
            C['working deferral: %s, %s, block %s' % ('frozen' if fr[k] else 'free', 'J-threatened' if k in optsJ else 'not threatened',
                                                       'last' if blk[k] == max(blk.values()) else 'earlier')] += 1
        if shown < 6:
            shown += 1
            print('FAIL', name, 'sets', sets, 'vals', vals, 'pi', pi, 'Y', Y, 'blocks', blk, 'ups', ups)
            print('   frozen', [i for i in range(n) if fr[i]], 'J-threatened', sorted(optsJ), 'capK', capK, 'S', S, 'needJ', needJ, 'D', D)
            print('   owners (o, deficit, cap, J-thr, extra):', rows)
            print('   working deferrals', works)
    for k in sorted(C, key=str): print(k, C[k])
