"""Is LB4r's move set complete (k4/sdc.md §23)?  For an instance and a start (the serial-dictatorship state of an order,
or LB4r's own Phase 1 with index insertion), each upgrade policy, explore EVERY state reachable by RotSteps (any depth;
the reachable set is finite) and ask whether some state has an LB4r output (exact SAT test of Lean's Output).
  complete start  = some reachable state has an output;
  dead start      = none does (rotations can never repair this start).
Reports, per instance: starts tried, dead starts, the least depth needed, the size of the reachable sets.

    python3 k4/sdc/rot_complete.py screen|suite|special|cores:FILES N SEED [CAP]
    RC_NMAX (default 5): skip larger instances; above n = 5, RC_SAMPLE (default 30) random orders instead of all n!."""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import sd
from blocks4 import M
from nof_var import SPECIAL
from rd_check import state_of


def explore(inst, s1, cap, memo):
    """BFS from s1 over RotSteps; returns (least depth with an output or None, states seen, capped?)"""
    def out(s):
        if s not in memo: memo[s] = bool(M.any_output(inst, s, 'bundle'))
        return memo[s]
    frontier = [s1]; seen = {s1}; d = 0
    while frontier:
        for s in frontier:
            if out(s): return d, len(seen), False
        nxt = []
        for s in frontier:
            for s2 in M.rot_steps(inst, s):
                if s2 not in seen:
                    seen.add(s2); nxt.append(s2)
                    if len(seen) >= cap: return None, len(seen), True
        frontier = nxt; d += 1
    return None, len(seen), False


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/rot_complete.py', *sys.argv[1:], flush=True)
    CAP = 4000
    NMAX = int(os.environ.get('RC_NMAX', '5')); SAMPLE = int(os.environ.get('RC_SAMPLE', '30'))
    if src == 'special': items = SPECIAL
    elif src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); CAP = int(sys.argv[4]) if len(sys.argv) > 4 else CAP
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
        items = instances(src); CAP = int(sys.argv[2]) if len(sys.argv) > 2 else CAP
    for name, sets, vals, m in items:
        n = len(sets)
        if n > NMAX: continue
        E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v)
        if n <= 5:
            orders = list(itertools.permutations(range(n)))
        else:
            orng = random.Random(hash(name) % 1000); orders = [tuple(orng.sample(range(n), n)) for _ in range(SAMPLE)]
        starts = {('order',) + o: state_of(inst, sd(E, list(o))[0]) for o in orders}
        starts[('lb4r-index',)] = M.phase1_state(inst, ())[0]
        memo = {}; C['instances'] += 1; dead_here = 0; maxd = 0
        for key, s0 in starts.items():
            best = None; capped = False
            for pol in ('shrink', 'envyFree', 'none'):
                s1 = M.up_run(inst, s0, pol)[0] if pol != 'none' else s0
                d, size, cp = explore(inst, s1, CAP, memo)
                C['reachable-set size > 500'] += size > 500
                capped |= cp
                if d is not None and (best is None or d < best): best = d
                if best == 0: break
            C['starts'] += 1
            if best is None:
                if capped: C['starts: no output found, search capped'] += 1
                else:
                    C['DEAD starts (no reachable output)'] += 1; dead_here += 1
            else:
                C['starts: least rotations %d' % best] += 1; maxd = max(maxd, best)
        C['instances with a dead start'] += dead_here > 0
        if dead_here and C['shown'] < 5:
            C['shown'] += 1; print('DEAD START', name, json.dumps((sets, vals)), dead_here, 'of', len(starts), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
