"""Rotation descent RD (k4/sdc.md §17): for an LB4r state s reached from the serial-dictatorship state of an order by a
run of upgrades and rotations, if s has no output, some RotStep s -> s' reaches a state with an output or with a
smaller Lemma K deficit (k4/rulef_model.py deficit_K: best owner and kept set).  If RD held, LB4r would succeed from
every start after at most (initial deficit) rotations.  Tests every state reachable within D rotations from the
states of several starting orders: neediest first (with and without R1), index order, LB4r's Phase 1 with index
insertion, and random orders.  A *trap* is a state without an output at which no RotStep lowers the deficit.

    python3 k4/sdc/rd_check.py screen|suite|special|cores:FILES N SEED [D]"""
import sys, os, json, gzip, random, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import sd
from blocks4 import M, RM
from nof_var import SPECIAL

INF = float('inf')


def state_of(inst, Y):
    base = [-1] * inst.m; pick = [-1] * inst.n
    for i, g in enumerate(Y):
        if g is not None: base[g] = i; pick[i] = g
    return (tuple(base), tuple(pick), tuple([False] * inst.n))


def analyse(sets, vals, m, D, rng, C, name):
    E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
    for i, (S, V) in enumerate(zip(sets, vals)):
        for g, x in zip(S, V): v[i][g] = x
    inst = M.Inst(v); n = inst.n
    starts = {'nf': rule_order(E, 'need2', False)[0], 'nfR1': rule_order(E, 'need2', True)[0],
              'index': sd(E, list(range(n)))[0], 'rand': sd(E, rng.sample(range(n), n))[0]}
    lb = M.phase1_state(inst, ())[0]
    memo = {}
    def info(s):
        if s not in memo:
            memo[s] = (bool(M.any_output(inst, s, 'bundle')), RM.deficit_K(inst, s))
        return memo[s]
    traps = 0
    for key, Y in list(starts.items()) + [('lb4r', None)]:
        s0 = lb if Y is None else state_of(inst, Y)
        for pol in ('shrink', 'envyFree', 'none'):
            s1 = M.up_run(inst, s0, pol)[0] if pol != 'none' else s0
            frontier = [s1]; seen = {s1}
            for d in range(D + 1):
                nxt = []
                for s in frontier:
                    out, dk = info(s)
                    if out: continue
                    C['states without output'] += 1
                    succ = M.rot_steps(inst, s)
                    good = False
                    for s2 in succ:
                        o2, d2 = info(s2)
                        if o2 or d2 < dk: good = True; break
                    if not good:
                        C['TRAP (no rotation lowers the deficit)'] += 1; traps += 1
                        if C['TRAP (no rotation lowers the deficit)'] <= 5:
                            print('TRAP', name, key, pol, 'depth', d, 'deficit', dk, 'rotations', len(succ), json.dumps((sets, vals)), flush=True)
                    if d < D:
                        for s2 in succ:
                            if s2 not in seen: seen.add(s2); nxt.append(s2)
                frontier = nxt
    return traps


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/rd_check.py', *sys.argv[1:], flush=True)
    rng = random.Random(5)
    if src == 'special': items = SPECIAL; D = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    elif src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); D = int(sys.argv[4]) if len(sys.argv) > 4 else 2
        rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    else:
        items = instances(src); D = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    for name, sets, vals, m in items:
        if len(sets) > 6: continue
        C['instances'] += 1
        tr = analyse(sets, vals, m, D, rng, C, name)
        C['instances with a trap'] += tr > 0
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
