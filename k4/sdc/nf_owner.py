"""Who owns the output after the repairing rotation, from the neediest-first start (k4/sdc.md §27).  From the state P of
the plain neediest-first run after envy-free upgrades, with no output, take every RotStep along k, x_1, ..., x_t with
new base O, and every owner o (or none) of an output of the rotated state, and classify o against the chain: 'k' (the
rotated agent; LB+'s Theorem B form), 'end=r' (x_t is LB+'s owner r, the last agent of the order neither frozen nor
marked; Theorem B4's form), 'end' (x_t, another agent), 'mid' (x_1..x_{t-1}), 'off' (not on the chain), 'none' (no
owner).  Per start: which classes some repairing rotation reaches, and whether one of 'k', 'end=r', 'none' does (the
three mechanisms of LB+ and Lemma K).  Starts needing two rotations are reported and skipped.

    python3 k4/sdc/nf_owner.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from blocks4 import M, RM
from nof_var import SPECIAL
from rd_check import state_of


def classify(c, o, r):
    if o is None: return 'none'
    if o == c[0]: return 'k'
    if o == c[-1]: return 'end=r' if o == r else 'end'
    if o in c: return 'mid'
    return 'off'


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/nf_owner.py', *sys.argv[1:], flush=True)
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
        s = M.up_run(inst, state_of(inst, Y), 'envyFree')[0]
        C['instances'] += 1
        if M.any_output(inst, s, 'bundle'): continue
        C['no output at the start'] += 1
        NA = M.NA_of(M.all_needs(inst, s)); fr = M.frozen_pre(inst, s, NA)
        cand_r = [i for i in pi if not fr[i] and not s[2][i]]; r = cand_r[-1] if cand_r else None
        cls = set(); chains_k = set()
        for s2, (c, O) in M.rot_steps(inst, s).items():
            for o in M.any_output(inst, s2, 'bundle'):
                cls.add(classify(c, o, r))
                if o == c[0]: chains_k.add(tuple(c))
        if not cls:
            C['needs two rotations'] += 1
            print('TWO', name, json.dumps((sets, vals)), flush=True); continue
        C['one rotation'] += 1
        C['one rotation, classes ' + '+'.join(sorted(cls))] += 1
        for x in ('k', 'end=r', 'end', 'mid', 'off', 'none'):
            C['one rotation, some output owned by ' + x] += x in cls
        C["one rotation, some output owned by k, by r at the chain end, or by none"] += bool(cls & {'k', 'end=r', 'none'})
        if 'k' not in cls and C['shown'] < 4:
            C['shown'] += 1; print('NO K-OWNER', name, json.dumps((sets, vals)), sorted(cls), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
