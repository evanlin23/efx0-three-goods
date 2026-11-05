"""LB+'s rotation choice as a greedy procedure at k = 4 (k4/sdc.md §24).  From the serial-dictatorship state of an order
pi (after the upgrades of a policy), repeat until an LB4r output exists:
  r  = the last agent of pi that is neither frozen nor marked (the owner of LB+'s Theorem A);
  k* = the first agent of pi that is FrozenAt, threatened by W_r = J + base(r), and has a need chain to r;
  rotate k* along a shortest need chain to r (RotStep), with base O = the largest set of k*'s goods in J + base(r) worth
       more than its pick that passes RotChecks; then move k* to the end of pi (Proposition D4: the deferral).
Fails if no k* or no admissible O exists, or after n rotations.  Compared with the exhaustive search (rot_complete.py).

    python3 k4/sdc/greedy_kstar.py screen|suite|special|cores:FILES N SEED"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from blocks4 import M, RM
from nof_var import SPECIAL
from rd_check import state_of


def greedy(inst, s, pi, limit):
    pi = list(pi)
    for step in range(limit + 1):
        if M.any_output(inst, s, 'bundle'): return step, 'output'
        if step == limit: return None, 'limit'
        needs = M.all_needs(inst, s); NA = M.NA_of(needs); fa = M.frozen_at(inst, s, NA)
        cand_r = [i for i in pi if not fa[i] and not s[2][i]]
        if not cand_r: return None, 'no owner r'
        r = cand_r[-1]
        Wr = set(g for g in range(inst.m) if s[0][g] == -1) | set(M.base_of(inst, s, r))
        chains = [c for c in M.chains(inst, s, needs, NA) if c[-1] == r]
        ks = [k for k in pi if fa[k] and RM.threatened(inst, k, Wr, M.base_of(inst, s, k)) and any(c[0] == k for c in chains)]
        if not ks: return None, 'no k*'
        k = ks[0]; c = min((c for c in chains if c[0] == k), key=len)
        pool = [g for g in range(inst.m) if inst.v[k][g] > 0 and (s[0][g] == -1 or s[0][g] == r)]
        done = False
        for size in range(len(pool), 0, -1):
            for O in itertools.combinations(pool, size):
                if sum(inst.v[k][g] for g in O) <= inst.v[k][s[1][k]]: continue
                s2 = M.rotate(s, c, O)
                if M.rot_checks(inst, s2):
                    s, done = s2, True; break
            if done: break
        if not done: return None, 'no admissible O'
        pi = [i for i in pi if i != k] + [k]
    return None, 'limit'


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/greedy_kstar.py', *sys.argv[1:], flush=True)
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
        inst = M.Inst(v); C['instances'] += 1; failed_here = 0
        for o in itertools.permutations(range(n)):
            s0 = state_of(inst, sd(E, list(o))[0]); res = None; why = collections.Counter()
            for pol in ('shrink', 'envyFree', 'none'):
                s1 = M.up_run(inst, s0, pol)[0] if pol != 'none' else s0
                d, how = greedy(inst, s1, o, n)
                why[how] += 1
                if d is not None and (res is None or d < res): res = d
                if res == 0: break
            C['starts'] += 1
            if res is None:
                C['GREEDY FAILS'] += 1; failed_here += 1
                for w in why: C['  failure reason (per policy): ' + w] += why[w]
            else: C['greedy succeeds after %d rotations' % res] += 1
        C['instances where greedy fails from some order'] += failed_here > 0
        if failed_here and C['shown'] < 4:
            C['shown'] += 1; print('GREEDY FAILS', name, json.dumps((sets, vals)), failed_here, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
