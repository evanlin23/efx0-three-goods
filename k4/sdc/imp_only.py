"""Improving rotations only (k4/sdc.md §28).  From the plain neediest-first start after envy-free upgrades, search
(BFS, every depth, reachable set capped), after each upgrade policy (upgrades raise the upgraded agent's value), over
RotSteps whose new base O is worth more to k than its pick
(v_k(O) > v_k(Y_k)); every state reached this way has bundle values at least the start's pick values (the output then
value-dominates the picks).  Reports whether an output is reachable this way and the least depth; compared with all
rotations.

    python3 k4/sdc/imp_only.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from blocks4 import M
from nof_var import SPECIAL
from rd_check import state_of


def bfs(inst, s1, improving, cap=3000):
    memo = {}
    def out(s):
        if s not in memo: memo[s] = bool(M.any_output(inst, s, 'bundle'))
        return memo[s]
    frontier = [s1]; seen = {s1}; d = 0
    while frontier:
        for s in frontier:
            if out(s): return d
        nxt = []
        for s in frontier:
            for s2, (c, O) in M.rot_steps(inst, s).items():
                k = c[0]
                if improving and not sum(inst.v[k][g] for g in O) > inst.v[k][s[1][k]]: continue
                if s2 not in seen:
                    seen.add(s2); nxt.append(s2)
                    if len(seen) > cap: return 'cap'
        frontier = nxt; d += 1
    return None


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/imp_only.py', *sys.argv[1:], flush=True)
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
        inst = M.Inst(v)
        Y, pi = rule_order(E, 'need2', False)
        C['instances'] += 1
        best = None
        for pol in ('envyFree', 'shrink', 'none'):
            s = M.up_run(inst, state_of(inst, Y), pol)[0] if pol != 'none' else state_of(inst, Y)
            d = bfs(inst, s, True)
            C[pol + ': improving rotations only: least depth %s' % d] += 1
            if isinstance(d, int) and (best is None or d < best): best = d
        C['some policy: improving rotations only: least depth %s' % best] += 1
        if best is None:
            print('IMPROVING FAILS', name, json.dumps((sets, vals)), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
