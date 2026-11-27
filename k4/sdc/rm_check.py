"""Improving rotations as a potential (k4/sdc.md §17).  An LB4r RotStep along a chain k -> ... -> last with new base O for
k raises the base value of every chain agent after k (each takes a good it needs, worth more than its base), and of k
when v_k(O) > v_k(Y_k); every other base is unchanged.  So *improving* rotations (v_k(O) > v_k(Y_k)) strictly raise the
vector of base values, and every sequence of them is finite.  Conjecture RM: every state reachable from the serial-
dictatorship state of an order by upgrades and improving rotations, at which no improving rotation applies (a sink),
has an LB4r output.  Tests every sink reachable from the starts of rd_check.py (neediest first with and without R1,
index order, LB4r's Phase 1, a random order) under each upgrade policy.

    python3 k4/sdc/rm_check.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import sd
from blocks4 import M
from nof_var import SPECIAL
from rd_check import state_of


def improving_steps(inst, s):
    out = []
    for s2, (c, O) in M.rot_steps(inst, s).items():
        k = c[0]
        if sum(inst.v[k][g] for g in O) > inst.v[k][s[1][k]]: out.append(s2)
    return out


def analyse(sets, vals, m, rng, C, name, cap=4000):
    E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
    for i, (S, V) in enumerate(zip(sets, vals)):
        for g, x in zip(S, V): v[i][g] = x
    inst = M.Inst(v); n = inst.n
    starts = {'nf': state_of(inst, rule_order(E, 'need2', False)[0]), 'nfR1': state_of(inst, rule_order(E, 'need2', True)[0]),
              'index': state_of(inst, sd(E, list(range(n)))[0]), 'rand': state_of(inst, sd(E, rng.sample(range(n), n))[0]),
              'lb4r': M.phase1_state(inst, ())[0]}
    memo = {}
    def has_out(s):
        if s not in memo: memo[s] = bool(M.any_output(inst, s, 'bundle'))
        return memo[s]
    bad = 0
    for key, s0 in starts.items():
        for pol in ('shrink', 'envyFree', 'none'):
            s1 = M.up_run(inst, s0, pol)[0] if pol != 'none' else s0
            stack = [s1]; seen = {s1}; sinks = badsinks = 0
            while stack and len(seen) < cap:
                s = stack.pop()
                if has_out(s): continue
                nx = improving_steps(inst, s)
                if not nx:
                    badsinks += 1
                    continue
                for s2 in nx:
                    if s2 not in seen: seen.add(s2); stack.append(s2)
            C['starts'] += 1
            if len(seen) >= cap: C['starts cut at %d states' % cap] += 1
            if badsinks:
                C['starts with a sink without output'] += 1; bad += 1
                if C['starts with a sink without output'] <= 6:
                    print('BAD SINK', name, key, pol, badsinks, json.dumps((sets, vals)), flush=True)
            if not has_out(s1) and not badsinks: C['starts needing rotations, every sink has an output'] += 1
    return bad


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/rm_check.py', *sys.argv[1:], flush=True)
    rng = random.Random(5)
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
        if len(sets) > 6: continue
        C['instances'] += 1
        C['instances with a bad sink'] += analyse(sets, vals, m, rng, C, name) > 0
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
