"""A Theorem B for the neediest-first start (k4/sdc.md §27).  Let P be the state of the plain neediest-first run after
envy-free upgrades, r the last agent of the order neither frozen nor marked (LB+'s owner), W_r = J + base(r).
Statement NF-B: P has an LB4r output, or some FrozenAt agent k threatened by W_r has a need chain k -> ... -> r and a
base O (any nonempty subset of R_k cap W_r passing RotChecks) such that the rotated state has an output.
Also: the same with 'k threatened by W_r' dropped (any chain to r), and with any chain end.

    python3 k4/sdc/nf_thmB.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from blocks4 import M, RM
from nof_var import SPECIAL
from rd_check import state_of

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/nf_thmB.py', *sys.argv[1:], flush=True)
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
        needs = M.all_needs(inst, s); NA = M.NA_of(needs); fr = M.frozen_pre(inst, s, NA)
        cand_r = [i for i in pi if not fr[i] and not s[2][i]]; r = cand_r[-1] if cand_r else None
        J = set(g for g in range(m) if s[0][g] == -1)
        Wr = J | (set(M.base_of(inst, s, r)) if r is not None else set())
        b_thr = b_r = b_any = False
        for s2, (c, O) in M.rot_steps(inst, s).items():
            if not M.any_output(inst, s2, 'bundle'): continue
            k, t = c[0], c[-1]
            b_any = True
            if t == r:
                b_r = True
                if RM.threatened(inst, k, Wr, M.base_of(inst, s, k)): b_thr = True
        C['NF-B (k threatened by W_r, chain to r, one rotation)'] += b_thr
        C['one rotation with chain end r'] += b_r
        C['one rotation, any chain'] += b_any
        if not b_thr and C['shown'] < 4:
            C['shown'] += 1; print('NF-B FAILS', name, json.dumps((sets, vals)), 'chain-to-r', b_r, 'any', b_any, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
