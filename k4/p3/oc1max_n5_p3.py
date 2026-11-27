"""OC1^max (LEDGER K4.SDC.OC1MAX, k4/sdc.md section 31 on claude/kind-lamport-y8fdme) on every n = 5 core hypergraph
with p <= 3 (every good valued by at most three agents; 14,402 of the 31,584 in results/k4_certs_5_*.json.gz), or with
--p=2 on the 676 multigraph ones; R random strict profiles each (half drawn as in the coordinator's oc1max_n5_lists.py,
integers 1..30 rejected unless strict, balanced and (C4); half as uniform order types from k4/check4.core_domains),
every order. Uses the coordinator's checker oc1_mc2_rand.Inst (brute-force one-absorber completion, official moves:
additions, chains, rings), imported from the directory OC1_SRC (default: k4/sdc of this checkout; the file is on
claude/kind-lamport-y8fdme). A maximum-matching order that fails is printed (then replay it with k4/p3/oc1max.py).
    OC1_SRC=DIR python3 k4/p3/oc1max_n5_p3.py R SEED [--n=5] [--p=3] [--lists=...] [--procs=4]
--n=4 uses results/k4_certs_4_{n4_1,n4_2,n4_3,pure}.json.gz. For each profile with a failing maximum order it also records
whether some maximum-matching order of that profile passes (the exists-order form).
"""
import sys, os, gzip, json, random, itertools, collections, time, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
SRC = os.environ.get('OC1_SRC', os.path.join(ROOT, 'k4', 'sdc'))
sys.path.insert(0, SRC); sys.path.insert(0, os.path.join(ROOT, 'k4'))
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
from oc1max_n5_lists import profile as coord_profile
import check4


def typed_profile(sets, m, rng):
    doms = check4.core_domains(sets, m, False)
    return [[t[g] for g in S] for t, S in ((D[rng.randrange(len(D))], S) for D, S in zip(doms, sets))]


def pmax(sets, m): return max(sum(g in S for S in sets) for g in range(m))


def job(args):
    lst, idx, sets, m, R, seed = args
    rng = random.Random(seed); C = collections.Counter(); bad = []
    for r in range(R):
        vals = coord_profile(sets, rng)[0] if r % 2 == 0 else typed_profile(sets, m, rng)
        I = Inst(sets, vals); N = nu(I)
        pk = collections.Counter(I.sd(o) for o in itertools.permutations(range(I.n)))
        some_max_ok = False; any_fail = False
        for p, c in pk.items():
            kind = 'max' if sum(x is not None for x in p) == N else 'non-max'
            res = I.check(p)
            C[(kind, res)] += c; C[(kind, 'distinct pick vectors')] += 1
            if kind == 'max' and res == 'OC1 fails': bad.append((vals, p)); any_fail = True
            if kind == 'max' and res != 'OC1 fails': some_max_ok = True
        if any_fail:
            C[('profiles with a failing maximum order', 'some maximum order passes' if some_max_ok else 'NO MAXIMUM ORDER PASSES')] += 1
    return lst, idx, sets, C, bad


if __name__ == '__main__':
    R, SEED = int(sys.argv[1]), int(sys.argv[2])
    opt = dict(a[2:].split('=', 1) for a in sys.argv[3:] if a.startswith('--'))
    P = int(opt.get('p', 3)); NA = int(opt.get('n', 5))
    lists = opt.get('lists', 'n4_1,n4_2,n4_3,n4_4,pure' if NA == 5 else 'n4_1,n4_2,n4_3,pure').split(',')
    print('$ python3 k4/p3/oc1max_n5_p3.py ' + ' '.join(sys.argv[1:]) + f'   (checker from {SRC})', flush=True)
    tasks = []
    for lst in lists:
        d = json.load(gzip.open(os.path.join(ROOT, 'results', f'k4_certs_{NA}_{lst}.json.gz'), 'rt'))
        for c in d['cores']:
            if pmax(c['sets'], c['m']) <= P:
                tasks.append((lst, c.get('idx', 0), c['sets'], c['m'], R, SEED * 1000003 + len(tasks)))
    print(f'hypergraphs with p <= {P}: {len(tasks)}, {R} profiles each', flush=True)
    t0 = time.time(); T = collections.Counter(); done = 0
    with mp.Pool(int(opt.get('procs', 4))) as pool:
        for lst, idx, sets, C, bad in pool.imap_unordered(job, tasks, chunksize=8):
            for k, c in C.items(): T[(lst,) + k] += c
            done += 1
            for vals, p in bad:
                print('OC1MAX FAILS', json.dumps({'list': lst, 'idx': idx, 'sets': sets, 'vals': vals, 'picks': p}), flush=True)
            if done % 2000 == 0: print(f'  {done} hypergraphs, {time.time()-t0:.0f}s', flush=True)
    for k in sorted(T, key=str): print(k, T[k])
    fails = sum(c for k, c in T.items() if k[1] == 'max' and k[2] == 'OC1 fails')
    print(f'maximum-matching orders that fail OC1: {fails}; time {time.time()-t0:.0f} s')
