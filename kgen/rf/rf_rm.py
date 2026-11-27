"""The coordinator's extremal variant (2026-11-27): OC1 at rank-maximal (RM) maximum-matching SD pick vectors, at k = 5, 6.
rank_i(Y) = 1 + the number of i's relevant goods valued above Y_i (agents without a pick have no rank).  Among the
maximum-matching SD vectors (picks of some SD order matching nu agents) the RM-optimal ones lexicographically maximize
(#rank 1, #rank 2, ...).  Question: does OC1 (rf_lib.Inst.oc1) hold at every RM-optimal vector?

    MAINWT=<main> python3 rf_rm.py known                         the known k >= 5 failures (rf_known.items) and every
                                                                 FAILSTART instance in results/kgen_rf/rf_climb_*.log
    python3 rf_rm.py rand K N NINST SEED                         random strict cores (rf_run.gen_sets)
    python3 rf_rm.py climb K N NCLIMB STEPS SEED                 hill climbs toward an RM-optimal vector failing OC1"""
import sys, os, json, glob, random, itertools, collections, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rf_lib import Inst
from rf_run import gen_sets, rand_vals, strict_balanced, VMAX
from rf_climb import good_states


def max_vectors(I):
    N = I.nu(); out = set()
    for o in itertools.permutations(range(I.n)):
        p = I.sd(o)
        if sum(x is not None for x in p) == N: out.add(p)
    return out


def signature(I, p):
    K = max(len(s) for s in I.sets); c = [0] * K
    for i, g in enumerate(p):
        if g is None: continue
        r = 1 + sum(1 for h in I.sets[i] if I.v[i][h] > I.v[i][g]); c[r - 1] += 1
    return tuple(c)


def rm_optimal(I, vecs):
    sig = {p: signature(I, p) for p in vecs}; best = max(sig.values()); return [p for p in vecs if sig[p] == best]


def analyse(sets, vals):
    I = Inst(sets, vals); vecs = max_vectors(I); rm = rm_optimal(I, vecs); C = collections.Counter(); bad = []
    res = {p: I.oc1(p) for p in vecs}
    C['instances'] += 1; C['max SD vectors'] += len(vecs); C['RM-optimal vectors'] += len(rm)
    for p in rm:
        C['RM-optimal: ' + res[p]] += 1
        if res[p] == 'OC1 fails': bad.append(p)
    f = [p for p in vecs if res[p] == 'OC1 fails']
    C['instances with a failing max vector'] += bool(f)
    if f: C['  ... of which some RM-optimal vector fails'] += bool(bad)
    return C, bad, f


def score(sets, vals):
    I = Inst(sets, vals); vecs = max_vectors(I); rm = rm_optimal(I, vecs)
    g = [good_states(I, p) for p in rm]; return (sum(1 for x in g if x == 0), -min(g))


def job_rand(a):
    k, n, seed = a; rng = random.Random(seed); sets = gen_sets(n, k, rng); vals = [rand_vals(len(s), rng) for s in sets]
    C, bad, f = analyse(sets, vals); return sets, vals, C, bad, f


def job_climb(a):
    k, n, steps, seed = a; rng = random.Random(seed); sets = gen_sets(n, k, rng); vals = [rand_vals(len(s), rng) for s in sets]
    sc = score(sets, vals)
    for _ in range(steps):
        if sc[0] > 0: break
        v2 = [list(x) for x in vals]; i = rng.randrange(n)
        for _t in range(100):
            y = list(v2[i]); y[rng.randrange(len(y))] = rng.randint(1, VMAX)
            if strict_balanced(y): break
        else: continue
        v2[i] = y; sc2 = score(sets, v2)
        if sc2 >= sc: vals, sc = v2, sc2
    C, bad, f = analyse(sets, vals); return sets, vals, C, bad, f


if __name__ == '__main__':
    mode = sys.argv[1]; print('$ python3 kgen/rf/rf_rm.py', *sys.argv[1:], flush=True); t0 = time.time(); T = collections.Counter()
    if mode == 'known':
        from rf_known import items
        insts = [(nm, s, v) for nm, s, v in items]
        here = os.path.dirname(os.path.abspath(__file__))
        for fn in sorted(glob.glob(os.path.join(here, '..', '..', 'results', 'kgen_rf', 'rf_climb_*.log'))):
            for line in open(fn):
                if line.startswith('FAILSTART '):
                    d = json.loads(line.split(' ', 1)[1]); insts.append((os.path.basename(fn) + ':%d' % d['seed'], d['sets'], d['vals']))
        for nm, s, v in insts:
            C, bad, f = analyse(s, v); T.update(C)
            I = Inst(s, v); vecs = max_vectors(I); rm = rm_optimal(I, vecs)
            print('%s: failing max vectors %s; RM-optimal %s (signature %s); RM-optimal failing: %s'
                  % (nm, f, rm, signature(I, rm[0]), bad or 'none'), flush=True)
    else:
        k, n = int(sys.argv[2]), int(sys.argv[3])
        if mode == 'rand':
            NI, SEED = int(sys.argv[4]), int(sys.argv[5]); tasks = [(k, n, SEED * 10 ** 6 + i) for i in range(NI)]; fn = job_rand
        else:
            NC, ST, SEED = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]); tasks = [(k, n, ST, SEED * 10 ** 6 + i) for i in range(NC)]; fn = job_climb
        with mp.Pool() as pool:
            for sets, vals, C, bad, f in pool.imap_unordered(fn, tasks):
                T.update(C)
                if bad: print('RM FAILS', json.dumps({'sets': sets, 'vals': vals, 'rm_failing': bad}), flush=True)
                elif f: print('FAILSTART (RM holds)', json.dumps({'sets': sets, 'vals': vals, 'failing': f}), flush=True)
    for key in sorted(T): print(T[key], key)
    print('time %.0f s' % (time.time() - t0))
