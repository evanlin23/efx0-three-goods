"""The smallest excess (k4/sdc.md §27): from EVERY order's serial-dictatorship start, after each upgrade policy, and
from every state reachable by RotSteps, classify the states without an LB4r output by omega and ask whether
  (D1) some RotStep reaches an output or lowers omega,
  (D0) some RotStep reaches an output or omega <= 0 (which gives an output with no owner when every base has at most
       two goods, EFX.LB4R.output_none_of_omega; the states with omega <= 0 and no output have a three-good base).
At omega = 1 the two agree; a state failing (D1) at omega = 1 is a counterexample to 'excess one is repaired by one
rotation' from that start.

    python3 k4/sdc/omega_small.py screen|suite|special|cores:FILES N SEED
    OS_NMAX (default 5): skip larger instances (every order up to n = 5, 30 sampled orders above)."""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from blocks4 import M
from nof_var import SPECIAL
from rd_check import state_of

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdc/omega_small.py', *sys.argv[1:], flush=True)
    NMAX = int(os.environ.get('OS_NMAX', '5'))
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
        if n > NMAX: continue
        E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v)
        orders = list(itertools.permutations(range(n))) if n <= 5 else \
            [tuple(random.Random(hash(name) % 1000 + t).sample(range(n), n)) for t in range(30)]
        memo = {}
        def out(s):
            if s not in memo: memo[s] = bool(M.any_output(inst, s, 'bundle'))
            return memo[s]
        C['instances'] += 1
        seen = set(); frontier = []
        for o in orders:
            s0 = state_of(inst, sd(E, list(o))[0])
            for pol in ('shrink', 'envyFree', 'none'):
                s1 = M.up_run(inst, s0, pol)[0] if pol != 'none' else s0
                if s1 not in seen: seen.add(s1); frontier.append(s1)
        while frontier:
            nxt = []
            for s in frontier:
                if out(s): continue
                om = M.omega(inst, s); d1 = d0 = False
                for s2 in M.rot_steps(inst, s):
                    if s2 not in seen: seen.add(s2); nxt.append(s2)
                    if out(s2): d1 = d0 = True
                    else:
                        om2 = M.omega(inst, s2); d1 |= om2 < om; d0 |= om2 <= 0
                key = 'omega %d' % om if om <= 3 else 'omega >= 4'
                C[key + ': states without output'] += 1
                C[key + ': (D1) fails'] += not d1
                C[key + ': (D0) fails'] += not d0
                if om == 1 and not d1 and shown[name] < 1:
                    shown[name] += 1
                    print('OMEGA1-STUCK', name, json.dumps((sets, vals)), 'state', s, flush=True)
            frontier = nxt
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
