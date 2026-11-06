"""omega-guided repair from the neediest-first start (k4/sdc.md §26).  From the state of the plain neediest-first order
(no R1) after each upgrade policy, follow only rotations that reach an output or lower omega (LB4r's junk excess), and
report traps: states reached this way with no output and no such rotation.  No trap from some policy means the
omega-guided search is complete from that start; then a proof of NF could run by induction on omega.

    python3 k4/sdc/omega_nf.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from blocks4 import M
from nof_var import SPECIAL
from rd_check import state_of

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/omega_nf.py', *sys.argv[1:], flush=True)
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
        Y, pi = rule_order(E, 'need2', False); s0 = state_of(inst, Y)
        C['instances'] += 1; complete_some = False; needs_rot = False
        for pol in ('shrink', 'envyFree', 'none'):
            s1 = M.up_run(inst, s0, pol)[0] if pol != 'none' else s0
            if out(s1): complete_some = True; break
            needs_rot = True
            stack = [s1]; seen = {s1}; traps = 0; reached = False
            while stack:
                s = stack.pop()
                if out(s): reached = True; continue
                om = M.omega(inst, s)
                nx = [s2 for s2 in M.rot_steps(inst, s) if out(s2) or M.omega(inst, s2) < om]
                if not nx: traps += 1
                for s2 in nx:
                    if s2 not in seen: seen.add(s2); stack.append(s2)
            C['policy %s: start needs rotations' % pol] += 1
            C['policy %s: omega-guided search reaches an output' % pol] += reached
            C['policy %s: with traps' % pol] += traps > 0
            if reached and not traps: complete_some = True
        C['start has an output (some policy)'] += not needs_rot
        if needs_rot:
            C['needs rotations'] += 1
            C['some policy: omega-guided search complete (no trap)'] += complete_some
            if not complete_some and C['shown'] < 4:
                C['shown'] += 1; print('NOT COMPLETE', name, json.dumps((sets, vals)), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
