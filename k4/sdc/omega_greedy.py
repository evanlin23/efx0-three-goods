"""Greedy omega repair from the neediest-first start (k4/sdc.md §27).  From the state of the plain neediest-first run
after envy-free upgrades, repeatedly apply the RotStep with the smallest resulting omega (rule 'min'), or the smallest
omega among improving rotations, falling back to all ('imp'); ties broken by the smallest Lemma K deficit, then by
the rotation's description.  Stops at an output, or fails when no rotation lowers omega.

    python3 k4/sdc/omega_greedy.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from blocks4 import M, RM
from nof_var import SPECIAL
from rd_check import state_of


def greedy(inst, s, rule, out):
    steps = 0
    while True:
        if out(s): return steps
        om = M.omega(inst, s); best = None
        for s2, (c, O) in M.rot_steps(inst, s).items():
            k = c[0]; imp = sum(inst.v[k][g] for g in O) > inst.v[k][s[1][k]]
            o2 = out(s2); om2 = -99 if o2 else M.omega(inst, s2)
            if not o2 and om2 >= om: continue
            key = (0 if (rule == 'min' or imp) else 1, om2, RM.deficit_K(inst, s2) if not o2 else -99, tuple(c), tuple(O))
            if best is None or key < best[0]: best = (key, s2)
        if best is None: return None
        s = best[1]; steps += 1


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/omega_greedy.py', *sys.argv[1:], flush=True)
    if src == 'special': items = SPECIAL
    elif src.startswith('cores:'):
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
        E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v); memo = {}
        def out(s):
            if s not in memo: memo[s] = bool(M.any_output(inst, s, 'bundle'))
            return memo[s]
        Y, pi = rule_order(E, 'need2', False)
        s1 = M.up_run(inst, state_of(inst, Y), 'envyFree')[0]
        C['instances'] += 1
        if out(s1): continue
        C['needs rotations'] += 1
        for rule in ('min', 'imp'):
            d = greedy(inst, s1, rule, out)
            C['%s: %s' % (rule, 'fails' if d is None else 'succeeds after %d' % d)] += 1
            if d is None and C['shown ' + rule] < 3:
                C['shown ' + rule] += 1; print('GREEDY %s FAILS' % rule, name, json.dumps((sets, vals)), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
