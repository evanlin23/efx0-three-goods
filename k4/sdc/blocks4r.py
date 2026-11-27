"""blocks4.py with the owner fixed to r = the last agent of pi that is neither frozen nor upgraded (LB+'s owner) and a
census of every block: for each agent, leader or not, frozen, threatened by W_r, its cost (least kept-out set) and its
slot places.  Checks the Block Lemma (BL): need(B) <= places(B) for every block B, the owner's place counted in its
own block; and reports the blocks where BL fails.

    python3 k4/sdc/blocks4r.py screen|suite|cores:FILES N SEED [pol]"""
import sys, os, json, gzip, random, collections
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import completable
from blocks4 import blocks_of, options, min_service, M, RM

if __name__ == '__main__':
    args = sys.argv[1:]; pol = 'shrink'
    if args[-1] in ('shrink', 'envyFree', 'none'): pol = args.pop()
    src = args[0]; C = collections.Counter(); shown = 0
    print('$ python3 k4/sdc/blocks4r.py', *sys.argv[1:])
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
        if M.omega(inst, s, needs) <= 0: C['omega <= 0'] += 1; continue
        cand = [i for i in pi if not fr[i] and not s[2][i]]
        if not cand: C['every agent frozen or upgraded'] += 1; continue
        r = cand[-1]
        opts, capK = options(inst, s, r, needs)
        if opts is None: C['r has an agent with no option'] += 1; continue
        nb = max(blk.values()) + 1; bad = []
        for b in range(nb):
            ob = [(x, ox) for x, ox in opts if blk[x] == b]
            places = sum(capK[x] for x in range(inst.n) if blk[x] == b)
            nd = min_service(ob)
            if nd > places: bad.append((b, nd, places))
        glob = min_service(opts) - sum(capK[x] for x in range(inst.n) if x != r)
        C['omega > 0'] += 1
        C['BL holds (every block)'] += not bad
        C['r works (Lemma K, K = empty)'] += glob <= 0
        C['r is in the last block'] += blk[r] == nb - 1
        if bad:
            C['BL fails in %d blocks' % len(bad)] += 1
            if shown < 8:
                shown += 1; thr = {x for x, _ in opts}
                print('BL fails', name, 'sets', sets, 'vals', vals, 'pi', pi, 'Y', Y, 'r', r, 'upgraded', [i for i in range(inst.n) if s[2][i]], 'bad', bad)
                for b, nd, pl in bad:
                    for x in [i for i in pi if blk[i] == b]:
                        print('    agent', x, 'leader' if x == min((i for i in pi if blk[i] == b), key=pi.index) else '', 'frozen' if fr[x] else '', 'threatened' if x in thr else '', 'cap', capK[x], 'base', M.base_of(inst, s, x))
        # census of threatened agents
        thr = {x: ox for x, ox in opts}
        for x, ox in thr.items():
            lead = x == min((i for i in pi if blk[i] == blk[x]), key=pi.index)
            cost = min(len(S) for k, S in ox if k == 'r') if any(k == 'r' for k, S in ox) else None
            C['threatened: %s %s cost %s' % ('leader' if lead else 'non-leader', 'frozen' if fr[x] else 'free', cost)] += 1
    for k in sorted(C, key=str): print(k, C[k])
