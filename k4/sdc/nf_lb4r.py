"""LB4r with the neediest-first Phase 1 (k4/sdc.md §16): build LB4r's state from the plain neediest-first R1 picks
(--nor1: without R1 priority)
(EFX.NOF.runState of EFX.NOF.sdList), run the upgrades of a policy (shrink, envyFree, none), then up to Q rotations
(lb4r.reach: every RotStep), and report the least number of rotations after which some state has an LB4r Output
(exact SAT test, Lean's Output).  Conjecture NF1: one rotation always suffices for some policy.

    python3 k4/sdc/nf_lb4r.py screen|suite [Q] | files | attempts | cores:FILES N SEED [Q] | SRC N SEED (SRC: rand, hyper,
        advt4x, advt3x, big8, big12 of sdc_rand.py, or gen:n:m:k) | climb SEED n STEPS ROUNDS   [--nor1]
    climb: maximize the least number of rotations (search depth NFQ, default 2; stops at an instance needing NFQ or
    having no output within NFQ rotations); NFSEEDS=FILE (JSON lines [sets, vals]) starts from those instances"""
import sys, os, json, gzip, random, collections, time
R1 = '--nor1' not in sys.argv
if not R1: sys.argv.remove('--nor1')
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from blocks4 import M


def least_rotations(sets, vals, m, Q=2):
    E = Enc(sets, vals, m); Y, pi = rule_order(E, 'need2', R1)
    v = [[0] * m for _ in sets]
    for i, (S, V) in enumerate(zip(sets, vals)):
        for g, x in zip(S, V): v[i][g] = x
    inst = M.Inst(v); n = inst.n
    base = [-1] * m; pick = [-1] * n
    for i, g in enumerate(Y):
        if g is not None: base[g] = i; pick[i] = g
    s0 = (tuple(base), tuple(pick), tuple([False] * n))
    best = None
    for pol in ('shrink', 'envyFree', 'none'):
        s1 = M.up_run(inst, s0, pol)[0] if pol != 'none' else s0
        levels = M.reach(inst, s1, Q if best is None else min(Q, best - 1))
        for d, lv in enumerate(levels):
            if best is not None and d >= best: break
            if any(M.any_output(inst, s, 'bundle') for s in lv):
                best = d; break
        if best == 0: break
    return best

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/nf_lb4r.py', *sys.argv[1:], '' if R1 else '--nor1', flush=True)
    Q = 2
    if src == 'climb':
        from sdc_climb import mutate, start
        seed, n, steps, rounds = map(int, sys.argv[2:6]); rng = random.Random(seed)
        QC = int(os.environ.get('NFQ', '2'))
        def cost(sets, vals):
            b = least_rotations(sets, vals, 1 + max(max(x) for x in sets), QC)
            return -9 if b is None else -b
        seeds = [json.loads(l) for l in open(os.environ['NFSEEDS'])] if os.environ.get('NFSEEDS') else None
        for r in range(rounds):
            sets, vals = start(rng, n) if seeds is None else [list(map(list, x)) for x in rng.choice(seeds)]
            c = cost(sets, vals); best = c
            for st in range(steps):
                mu = mutate(sets, vals, rng)
                if mu is None or len(mu[0]) != n: continue
                c2 = cost(*mu)
                if c2 <= c or rng.random() < 0.03:
                    (sets, vals), c = mu, c2; best = min(best, c)
                    if c <= -QC:
                        print('NEEDS', -c, json.dumps((sets, vals)), flush=True); break
            C['round: least rotations reached %d' % -best] += 1
            print('round', r, 'final', -c, 'max', -best, 'time %.0f' % (time.time() - t0), flush=True)
        items = []
    elif src == 'attempts':
        items = [('least-count', [[0,1,4,5],[2,3,4,5],[2,3,4,5]], [[1,4,6,8],[2,3,4,8],[2,7,8,4]], 6),
                 ('Q0', [[0,1,4,5],[2,3,4,5],[2,3,4,5]], [[1,4,6,8],[3,5,7,6],[2,4,5,8]], 6),
                 ('Q2', [[0,1,3,4],[2,3,6,7],[2,5,7],[4,5,6,7]], [[2,3,10,6],[2,8,3,4],[2,4,3],[4,8,2,3]], 8),
                 ('Q3', [[0,2,5,6],[1,4,5,6],[2,3,5],[3,4,6]], [[2,8,4,5],[2,8,5,4],[4,2,3],[2,4,3]], 7),
                 ('r4253', [[0,2,5,6],[1,4,6],[2,3,4,5],[3,4,5,6]], [[2,4,10,7],[2,4,3],[4,5,8,2],[2,6,10,7]], 7),
                 ('r3943', [[0,1,3,4],[2,3,4,5],[2,3,6],[2,5,6],[4,5,6]], [[6,4,1,8],[6,8,5,4],[3,4,2],[4,2,3],[4,2,3]], 7),
                 ('T3', [[5,0,4,2],[3,1,4],[4,1,3,0]], [[1,38,36,6],[12,22,30],[28,20,12,38]], 6),
                 ('T3-climb', [[5,0,4,2],[3,1,4],[4,1,3,0]], [[1,19,18,3],[6,11,15],[14,10,6,19]], 6)]
    elif src in ('screen', 'suite'):
        if len(sys.argv) > 2: Q = int(sys.argv[2])
        items = instances(src)
    elif src == 'files':
        sys.path.insert(0, os.path.join(_paths.ROOT, 'k4'))
        import adaptive_H as AH
        from sdc_ht import build_hh
        R = os.path.join(_paths.ROOT, 'results', 'k4_de4'); items = []
        for f in ['robust_failures.json', 'refute_lp_instance.json', 'refute_rob_instance.json', 'shed_failures_found.json',
                  'shed2_near.json', 'unclean_cycles.json']:
            d = json.load(open(os.path.join(R, f)))
            if isinstance(d, dict): d = d.get('instances', [])
            for t, e in enumerate(d):
                sets, vals = (e['sets'], e['vals']) if isinstance(e, dict) else (e[0], e[1])
                items.append(('%s#%d' % (f, t), sets, vals, 1 + max(max(x) for x in sets)))
        for t in (2, 3, 4, 5):
            S, V, m = AH.build(t); items.append(('H%d' % t, S, V, m))
        for t in (3, 4):
            S, V, m = build_hh(t); items.append(('HH%d' % t, S, V, m))
        Q = 1
    else:
        N, seed = int(sys.argv[2]), int(sys.argv[3]); Q = int(sys.argv[4]) if len(sys.argv) > 4 else 2
        rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        import sdc_rand
        from de4lib import random_profile
        os.chdir(cwd)
        cores = None
        if src.startswith('cores:'):
            cores = []
            for fn in src[6:].split(','):
                cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            if cores is not None:
                sets = rng.choice(cores); vals = random_profile(sets, rng)
            elif src.startswith('gen:'):
                _, n, m, k = src.split(':'); n, m, k = int(n), int(m), int(k)
                while True:
                    sets = [sorted(rng.sample(range(m), rng.randint(max(1, k - 1), k))) for _ in range(n)]
                    if len(set().union(*map(set, sets))) == m: break
                vals = [rng.sample(range(1, 60), len(s)) for s in sets]
            else:
                os.chdir(_paths.DE4); sets, vals = sdc_rand.gen(src, rng); os.chdir(cwd)
            items.append(('r%d' % t, sets, vals, 1 + max(max(x) for x in sets)))
    for name, sets, vals, m in items:
        best = least_rotations(sets, vals, m, Q)
        C['instances'] += 1
        C['least rotations: %s' % best] += 1
        if best is None or best >= 2: print('NEEDS', best, name, json.dumps((sets, vals)), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
