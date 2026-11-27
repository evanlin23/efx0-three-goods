"""Traps in LB4r's rotation graph (k4/sdc.md §23).  From the serial-dictatorship states of all orders (n <= 5) after each
upgrade policy, build the whole graph of states reachable by RotSteps (capped), and find the *trap* states: reachable
states from which no state with an LB4r output is reachable.  No trap means every rotation sequence can still be
extended to a success; a trap means the order of rotations matters.

    python3 k4/sdc/rot_traps.py screen|special|cores:FILES N SEED [CAP]"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from blocks4 import M
from nof_var import SPECIAL
from rd_check import state_of

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time(); CAP = 3000
    print('$ python3 k4/sdc/rot_traps.py', *sys.argv[1:], flush=True)
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
        n = len(sets)
        if n > 5: continue
        E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v)
        roots = set()
        for o in itertools.permutations(range(n)):
            s0 = state_of(inst, sd(E, list(o))[0])
            for pol in ('shrink', 'envyFree', 'none'):
                roots.add(M.up_run(inst, s0, pol)[0] if pol != 'none' else s0)
        succ = {}; stack = list(roots); seen = set(roots); capped = False
        while stack:
            s = stack.pop()
            if M.any_output(inst, s, 'bundle'): succ[s] = None; continue
            nx = list(M.rot_steps(inst, s)); succ[s] = nx
            for s2 in nx:
                if s2 not in seen:
                    seen.add(s2); stack.append(s2)
                    if len(seen) > CAP: capped = True; break
            if capped: break
        C['instances'] += 1
        if capped: C['capped'] += 1; continue
        good = {s for s, nx in succ.items() if nx is None}
        changed = True
        while changed:
            changed = False
            for s, nx in succ.items():
                if s not in good and nx and any(x in good for x in nx): good.add(s); changed = True
        traps = [s for s in succ if s not in good]
        C['states'] += len(succ); C['trap states'] += len(traps)
        C['instances with a trap'] += bool(traps)
        C['instances with a trap among the roots'] += any(s in roots for s in traps)
        if traps and C['shown'] < 3:
            C['shown'] += 1; print('TRAP', name, json.dumps((sets, vals)), len(traps), 'of', len(succ), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
