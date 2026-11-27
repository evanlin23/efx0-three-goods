"""What the greedy omega rotation is (k4/sdc.md §27).  From the plain neediest-first state after envy-free upgrades,
when there is no output, take the rotation minimizing omega (ties by Lemma K's deficit, then description; rule 'min' of
omega_greedy.py) and classify it: the size of k's new base O and how many of its goods were junk; whether it is
improving (v_k(O) > v_k(Y_k)); whether k is threatened by W_t = J + base(t) for the chain end t; whether t is the
owner r of LB+'s Theorem A (the last agent of the order that is neither frozen nor marked); chain length; whether t is
free after; the drop of omega; and whether the result has an output.

    python3 k4/sdc/omega_classify.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from blocks4 import M, RM
from nof_var import SPECIAL
from rd_check import state_of

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter()
    print('$ python3 k4/sdc/omega_classify.py', *sys.argv[1:], flush=True)
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
        if M.any_output(inst, s, 'bundle'): continue
        om = M.omega(inst, s); needs = M.all_needs(inst, s); NA = M.NA_of(needs); fr = M.frozen_pre(inst, s, NA)
        cand_r = [i for i in pi if not fr[i] and not s[2][i]]; r = cand_r[-1] if cand_r else None
        J = set(g for g in range(m) if s[0][g] == -1)
        best = None
        for s2, (c, O) in M.rot_steps(inst, s).items():
            o2 = bool(M.any_output(inst, s2, 'bundle')); om2 = -99 if o2 else M.omega(inst, s2)
            if not o2 and om2 >= om: continue
            key = (om2, RM.deficit_K(inst, s2) if not o2 else -99, tuple(c), tuple(O))
            if best is None or key < best[0]: best = (key, s2, c, O, o2)
        C['states needing a rotation'] += 1
        if best is None: C['no omega-lowering rotation'] += 1; continue
        _, s2, c, O, o2 = best; k, t = c[0], c[-1]
        Wt = J | set(M.base_of(inst, s, t))
        f2 = M.frozen_pre(inst, s2, M.NA_of(M.all_needs(inst, s2)))
        desc = '|O|=%d (%d junk), %s, k %s by W_t, chain end %s, chain length %d, end %s after, omega %d -> %s' % (
            len(O), len(set(O) & J), 'improving' if sum(v[k][g] for g in O) > v[k][s[1][k]] else 'downgrade',
            'threatened' if RM.threatened(inst, k, Wt, M.base_of(inst, s, k)) else 'NOT threatened',
            'r' if t == r else 'other', len(c), 'frozen' if f2[t] else 'free', om, 'output' if o2 else M.omega(inst, s2))
        C[desc] += 1
    for k in sorted(C, key=lambda x: -C[x]): print(C[k], k)
