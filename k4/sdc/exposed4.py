"""How many 4-good agents are exposed in neediest-first runs (k4/sdc.md §25)?  The proved theorems of K4.C4.AB / AB.L
(A4: no exposed 4-good agent; B4w, A4T: exactly one) leave open the runs with two or more exposed 4-good agents
(K4.C4.GAP).  For a run of Phase 1 (an R1 order: neediest first with R1 priority, LB4r's index Phase 1, or a random R1
order), LB4r's state after envy-free upgrades to the fixpoint, r = the last-processed unmarked agent, W = J + base(r):
count the 4-good agents other than r threatened by W with their base.

    python3 k4/sdc/exposed4.py screen|suite|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import sd
from blocks4 import M, RM
from rd_check import state_of


def exposed4(inst, s, pi):
    needs = M.all_needs(inst, s)
    r = [i for i in pi if not s[2][i]][-1]
    W = set(g for g in range(inst.m) if s[0][g] == -1) | set(M.base_of(inst, s, r))
    ex = [x for x in range(inst.n) if x != r and len(inst.R[x]) == 4 and RM.threatened(inst, x, W, M.base_of(inst, s, x))]
    return len(ex), bool(M.any_output(inst, s, 'bundle'))


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/sdc/exposed4.py', *sys.argv[1:], flush=True)
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
        rng = random.Random(1); items = instances(src)
    for name, sets, vals, m in items:
        if len(sets) > 9: continue
        E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v); n = inst.n
        Y, pi = rule_order(E, 'need2', True)
        runs = {'neediest-first R1': (state_of(inst, Y), pi)}
        s_lb, run_lb = M.phase1_state(inst, ())
        runs['LB4r index'] = (s_lb, [x for x, _, _ in run_lb])
        o = rng.sample(range(n), n); Yr, _ = sd(E, o, True)
        # order actually processed by the R1 sd: recompute
        left = set(range(m)); done = []; rank = {a: k for k, a in enumerate(o)}
        while len(done) < n:
            cand = [i for i in range(n) if i not in done]
            i = min(cand, key=lambda a: (0 if any(g not in left for g in E.R[a]) else 1, rank[a]))
            done.append(i)
            if Yr[i] is not None: left.discard(Yr[i])
        runs['random R1'] = (state_of(inst, Yr), done)
        C['instances'] += 1
        for key, (s0, order) in runs.items():
            s1 = M.up_run(inst, s0, 'envyFree')[0]
            k, out = exposed4(inst, s1, order)
            C['%s: exposed 4-good agents %d' % (key, min(k, 3))] += 1
            if k >= 2: C['%s: >= 2 exposed, output anyway (no rotation)' % key] += out
    for k in sorted(C, key=str): print(k, C[k])
