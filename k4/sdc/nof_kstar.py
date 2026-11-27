"""Which deferral repairs a plain-run failure of NOF-R1 (k4/sdc.md §15)?  For every plain neediest-first R1 run whose
picks do not extend, with B* its last block, r the last agent of pi that is neither frozen nor upgraded (LB4r state
after need-shrinking upgrades), test explicit candidates k*:
  lead   : the leader of B*;
  thr    : the frozen agents of B* threatened by W_r = J + base(r) (each tested);
  first  : the first frozen agent of B* threatened by W_r;
  chain  : the frozen agents of B* threatened by W_r with a need chain ending at r.

    python3 k4/sdc/nof_kstar.py screen|suite|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import completable, sd
from blocks4 import blocks_of, M, RM
import blocks4 as B4

thr_raw = RM.threatened


def chains_end(inst, s, needs, x, fr):
    """ends of need chains from x: x <- j (j needs base(x) = Y_x) <- ... until a non-frozen agent"""
    ends = set(); stack = [x]; seen = {x}
    while stack:
        y = stack.pop(); Yy = s[1][y]
        nd = [j for j in range(inst.n) if j != y and Yy >= 0 and Yy in needs[j]]
        for j in nd:
            if j in seen: continue
            seen.add(j)
            if fr[j]: stack.append(j)
            else: ends.add(j)
    return ends


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); shown = 0
    print('$ python3 k4/sdc/nof_kstar.py', *sys.argv[1:])
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
        base = [-1] * m; pick = [-1] * n
        for i, g in enumerate(Y):
            if g is not None: base[g] = i; pick[i] = g
        s = (tuple(base), tuple(pick), tuple([False] * n)); s, ups = M.up_run(inst, s, 'shrink')
        needs = M.all_needs(inst, s); NA = M.NA_of(needs); fr = M.frozen_pre(inst, s, NA)
        blk = blocks_of(E, pi, Y); last = max(blk.values()); Bs = [i for i in pi if blk[i] == last]
        cand = [i for i in pi if not fr[i] and not s[2][i]]
        r = cand[-1] if cand else None
        works = {o for o in pi if completable(E, sd(E, [i for i in pi if i != o] + [o])[0])}
        C['failures'] += 1
        C['r in B*'] += r in Bs
        lead = Bs[0]
        C['defer lead of B* works'] += lead in works
        C['lead of B* frozen'] += fr[lead]
        if r is not None:
            Wr = set(g for g in range(m) if s[0][g] == -1) | set(M.base_of(inst, s, r))
            thr = [x for x in Bs if x != r and fr[x] and thr_raw(inst, x, Wr, M.base_of(inst, s, x))]
            ch = [x for x in thr if r in chains_end(inst, s, needs, x, fr)]
            C['|thr| = %d' % len(thr)] += 1
            C['some thr works'] += any(x in works for x in thr)
            C['every thr works'] += bool(thr) and all(x in works for x in thr)
            C['first thr works'] += bool(thr) and thr[0] in works
            C['|chain| = %d' % len(ch)] += 1
            C['some chain works'] += any(x in works for x in ch)
            C['first chain works'] += bool(ch) and ch[0] in works
            if not (thr and thr[0] in works) and shown < 5:
                shown += 1
                print('first-thr fails', name, 'sets', sets, 'vals', vals, 'pi', pi, 'Y', Y, 'blocks', blk, 'ups', ups, 'r', r, 'thr', thr, 'chain', ch, 'works', sorted(works))
    for k in sorted(C, key=str): print(k, C[k])
