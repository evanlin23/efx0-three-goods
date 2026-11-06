"""Lemma Omega (k4/sdc.md §26) and the existence step it leaves.
  (L) For every improving RotStep (v_k(O) > v_k(Y_k)) with |O| = 2 whose chain end has a one-good base:
      omega' = omega - (#chain agents x_1..x_t not frozen after) - (#other agents frozen before and not after),
      and no agent outside the chain becomes frozen.  Checked on every such rotation met.
  (E) From the plain neediest-first start (each upgrade policy), following only such rotations that leave some agent
      free (so omega drops by Lemma Omega), every reached state without an LB4r output has another one.  A trap is a
      reached state without output and without such a rotation.  If some policy has no trap, induction on omega
      (omega <= 0 gives an output with no owner, EFX.LB4R.output_none_of_omega) repairs the start.

    python3 k4/sdc/lemma_omega.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from blocks4 import M
from nof_var import SPECIAL
from rd_check import state_of


def omega_moves(inst, s, C):
    """improving |O| = 2 rotations with a one-good chain end; checks (L); returns those that lower omega"""
    needs = M.all_needs(inst, s); NA = M.NA_of(needs); fr = M.frozen_pre(inst, s, NA); om = M.omega(inst, s, needs)
    good = []
    for s2, (c, O) in M.rot_steps(inst, s).items():
        k = c[0]; t = c[-1]
        if len(O) != 2 or len(M.base_of(inst, s, t)) != 1: continue
        if sum(inst.v[k][g] for g in O) <= inst.v[k][s[1][k]]: continue
        n2 = M.all_needs(inst, s2); NA2 = M.NA_of(n2); fr2 = M.frozen_pre(inst, s2, NA2); om2 = M.omega(inst, s2, n2)
        chain_free = sum(1 for x in c[1:] if not fr2[x])
        others_unfrozen = sum(1 for x in range(inst.n) if x not in c and fr[x] and not fr2[x])
        others_frozen = sum(1 for x in range(inst.n) if x not in c and not fr[x] and fr2[x])
        C['(L) rotations checked'] += 1
        ok = om2 == om - chain_free - others_unfrozen and others_frozen == 0
        C['(L) holds'] += ok
        if not ok and C['(L) shown'] < 3:
            C['(L) shown'] += 1; print('LEMMA OMEGA FAILS', om, om2, chain_free, others_unfrozen, others_frozen, list(c), list(O), flush=True)
        if om2 < om: good.append(s2)
    return good


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/lemma_omega.py', *sys.argv[1:], flush=True)
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
        C['instances'] += 1; done = False; tried = False
        for pol in ('shrink', 'envyFree', 'none'):
            s1 = M.up_run(inst, s0, pol)[0] if pol != 'none' else s0
            if out(s1): done = True; break
            tried = True
            stack = [s1]; seen = {s1}; traps = 0
            while stack:
                s = stack.pop()
                if out(s): continue
                nx = omega_moves(inst, s, C)
                if not nx:
                    traps += 1
                    if M.omega(inst, s) <= 0: C['trap with omega <= 0 (should not happen)'] += 1
                for s2 in nx:
                    if s2 not in seen: seen.add(s2); stack.append(s2)
            C['policy %s: needs rotations' % pol] += 1
            C['policy %s: (E) holds (no trap)' % pol] += traps == 0
            if traps == 0: done = True
        if tried:
            C['instances needing rotations'] += 1
            C['(E) holds for some policy'] += done
            if not done and C['shown'] < 4:
                C['shown'] += 1; print('(E) FAILS', name, json.dumps((sets, vals)), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
