"""omega as a potential for rotations (k4/sdc.md §26).  omega = |J| - (slot places) is LB4r's junk excess; omega <= 0
means an output with no owner exists (EFX.LB4R.output_none_of_omega).  A rotation of a frozen agent that takes two
or more junk goods into its new base lowers omega when the chain end keeps its place.  Test, at every reachable state
without an output (from every order with n <= 5, every policy, BFS to DEPTH):
  (O1) some rotation reaches an output or lowers omega;
  (O2) some rotation reaches an output, lowers omega, or keeps omega and lowers Lemma K's deficit;
  (I1), (I2): the same, counting only *improving* rotations (the rotated agent k gains: v_k(O) > v_k(Y_k));
in mode 'all' (every reachable state) and 'guided' (only along rotations that satisfy the criterion, LEX_MODE=guided,
criterion O1, O2, I1 or I2 via OM_CRIT).  No trap in guided mode would make (omega, deficit) a potential proving RC there.

    python3 k4/sdc/omega_check.py screen|special|cores:FILES N SEED [DEPTH]"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from blocks4 import M, RM
from nof_var import SPECIAL
from rd_check import state_of

GUIDED = os.environ.get('LEX_MODE', 'all') == 'guided'
CRIT = os.environ.get('OM_CRIT', 'O2')

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/omega_check.py', *sys.argv[1:], 'mode', 'guided' if GUIDED else 'all', CRIT, flush=True)
    if src == 'special': items = SPECIAL; DEPTH = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    elif src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); DEPTH = int(sys.argv[4]) if len(sys.argv) > 4 else 4
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
        items = instances(src); DEPTH = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    for name, sets, vals, m in items:
        n = len(sets)
        if n > 5: continue
        E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v); memo = {}
        def info(s):
            if s not in memo:
                out = bool(M.any_output(inst, s, 'bundle'))
                memo[s] = (out, M.omega(inst, s), None if out else RM.deficit_K(inst, s))
            return memo[s]
        roots = set()
        for o in itertools.permutations(range(n)):
            s0 = state_of(inst, sd(E, list(o))[0])
            for pol in ('shrink', 'envyFree', 'none'):
                roots.add(M.up_run(inst, s0, pol)[0] if pol != 'none' else s0)
        frontier = list(roots); seen = set(roots); bad = {'O1': 0, 'O2': 0, 'I1': 0, 'I2': 0}
        for d in range(DEPTH + 1):
            nxt = []
            for s in frontier:
                out, om, dk = info(s)
                if out: continue
                C['states without output'] += 1
                steps = M.rot_steps(inst, s); succ = list(steps); good = {'O1': [], 'O2': [], 'I1': [], 'I2': []}
                for s2 in succ:
                    o2, om2, dk2 = info(s2)
                    c, O = steps[s2]; k = c[0]
                    imp = sum(inst.v[k][g] for g in O) > inst.v[k][s[1][k]]
                    if o2 or om2 < om:
                        good['O1'].append(s2); good['O2'].append(s2)
                        if imp or o2: good['I1'].append(s2); good['I2'].append(s2)
                    elif om2 == om and dk2 is not None and dk is not None and dk2 < dk:
                        good['O2'].append(s2)
                        if imp: good['I2'].append(s2)
                for k in good:
                    if not good[k]: C['trap for %s' % k] += 1; bad[k] += 1
                if d < DEPTH:
                    for s2 in (good[CRIT] if GUIDED else succ):
                        if s2 not in seen: seen.add(s2); nxt.append(s2)
            frontier = nxt
        C['instances'] += 1
        for k in bad:
            if bad[k]: C['instances with a trap for %s' % k] += 1
        if bad[CRIT] and C['shown'] < 4:
            C['shown'] += 1; print('TRAP', CRIT, name, json.dumps((sets, vals)), bad, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
