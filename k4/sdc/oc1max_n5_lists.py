"""OC1^max (k4/attack_log.md 21:56) on the n = 5 core hypergraphs of results/k4_certs_5_*.json.gz, random strict
profiles, every order.  Earlier OC1 data at n = 5 used only the lists with one or two 4-good agents; the core
counterexamples of the TTC session live in the lists with three.  For each hypergraph: R random profiles that are
strict (disjoint nonempty subsets of R_i have different values), balanced (2 v_i(g) < v_i(R_i)) and satisfy (C4)
(two private goods p, q only with p + q < s + t); then every order, classified as maximum-matching or not and by its
OC1 outcome (coordinator's checker oc1_mc2_rand.Inst).  A maximum-matching order that fails is printed.

    python3 k4/sdc/oc1max_n5_lists.py LIST[,LIST...] R SEED [STRIDE]"""
import sys, os, gzip, json, random, itertools, collections, time, multiprocessing as mp
import _paths
from oc1_mc2_rand import Inst
from oc1_max_orders import nu

RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results')


def profile(sets, rng):
    n = len(sets)
    priv = [[k for k, g in enumerate(s) if all(g not in sets[j] for j in range(n) if j != i)] for i, s in enumerate(sets)]
    vals = []
    for i, s in enumerate(sets):
        while True:
            x = [rng.randint(1, 30) for _ in s]
            if 2 * max(x) >= sum(x): continue
            if len(priv[i]) == 2 and not sum(x[k] for k in priv[i]) < sum(x) - sum(x[k] for k in priv[i]): continue
            sums = collections.defaultdict(list); ok = True
            for r in range(1, len(x) + 1):
                for T in itertools.combinations(range(len(x)), r): sums[sum(x[k] for k in T)].append(set(T))
            for L in sums.values():
                if any(not (a & b) for a, b in itertools.combinations(L, 2)): ok = False; break
            if ok: break
        vals.append(x)
    return vals, max(len(p) for p in priv)


def job(args):
    lst, idx, sets, R, seed = args
    rng = random.Random(seed); C = collections.Counter(); bad = []
    for _ in range(R):
        vals, mp_ = profile(sets, rng); I = Inst(sets, vals); N = nu(I)
        cls = 'MC2' if mp_ <= 1 else 'two-private'
        pk = collections.Counter(I.sd(o) for o in itertools.permutations(range(I.n)))
        for p, c in pk.items():
            r = I.check(p); kind = 'max' if sum(x is not None for x in p) == N else 'non-max'
            C[(cls, kind, r)] += c
            if kind == 'max' and r == 'OC1 fails': bad.append((vals, p))
    return lst, idx, sets, C, bad


if __name__ == '__main__':
    lists = sys.argv[1].split(','); R = int(sys.argv[2]); SEED = int(sys.argv[3])
    STRIDE = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    print('$ python3 k4/sdc/oc1max_n5_lists.py', *sys.argv[1:], flush=True)
    tasks = []
    for lst in lists:
        d = json.load(gzip.open(os.path.join(RES, 'k4_certs_5_%s.json.gz' % lst)))
        for c in d['cores'][::STRIDE]:
            tasks.append((lst, c['idx'], c['sets'], R, SEED * 1000003 + len(tasks)))
    print('hypergraphs', len(tasks), flush=True)
    t0 = time.time(); T = collections.Counter(); done = 0
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for lst, idx, sets, C, bad in pool.imap_unordered(job, tasks, chunksize=8):
            done += 1
            for k, c in C.items(): T[(lst,) + k] += c
            for vals, p in bad:
                T['MAX FAILURES'] += 1
                print('OC1max FAILS', json.dumps({'list': lst, 'idx': idx, 'sets': sets, 'vals': vals, 'picks': p}), flush=True)
            if done % 2000 == 0: print('...', done, 'hypergraphs, %.0f s' % (time.time() - t0), flush=True)
    for k in sorted(T, key=str): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
