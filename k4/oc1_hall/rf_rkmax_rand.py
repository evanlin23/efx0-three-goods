"""RKMAX's sigma-maximal starts on random strict profiles of the n = 5 pure cores (k4/oc1_hall.md §24.14; EVIDENCE
only, PROMPT.md §5 rule 3).  Question (coordinator, RKMAX plan (a)): does sigma-maximality exclude one receiver with
|D_T| in {0, 2, 3} at n >= 5?  On the export profiles (§24.12) no such vector occurs; here the profiles are random.

For every core of results/k4_certs_5_pure.json.gz and PER random strict profiles (each agent's values a random
4-subset of 1..20 in random order, seeded): every order is run, the sigma-maximal maximum-matching vectors are
classified by (|U|, |D_T|), and at every vector with |U| = 1 and |D_T| != 1 OC1 is checked by the raw checker
(k4/sdc/oc1_mc2_rand.Inst.check).  Such vectors are printed (first few), and an OC1 failure there would refute RKMAX.

    python3 k4/oc1_hall/rf_rkmax_rand.py [PER] [SEED]
"""
import sys, os, json, gzip, collections, itertools, random, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, threatened
from rf_rkmax import sigma
import _paths
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst as RawInst


def job(task):
    idx, sets, per, seed = task
    rng = random.Random(seed * 100003 + idx); m = 1 + max(max(s) for s in sets)
    C = collections.Counter(); ex = []
    for _ in range(per):
        vals = [rng.sample(range(1, 21), len(s)) for s in sets]
        I = Inst(sets, vals, m)
        mx = [Y for Y in set(picks(I, o) for o in itertools.permutations(range(I.n))) if None not in Y]
        if not mx: C['profiles with no maximum-matching vector'] += 1; continue
        C['profiles'] += 1
        best = max(sigma(I, Y) for Y in mx)
        for Y in [Y for Y in mx if sigma(I, Y) == best]:
            P = Picks(I, Y)
            U = [i for i in range(I.n) if i not in P.F]; DT = [k for k in P.D if threatened(I, k, P.pv[k], P.J)]
            C['sigma-maximal vectors by (|U|, |D_T|) = (%d, %d)' % (len(U), len(DT))] += 1
            if len(U) == 1 and len(DT) != 1:
                res = RawInst(sets, vals).check(Y)
                C['  (1, %d): OC1 %s' % (len(DT), res)] += 1
                if len(ex) < 2 or res == 'OC1 fails' or len(DT) >= 2 or res != 'picks complete':
                    ex.append({'idx': idx, 'sets': sets, 'vals': vals, 'picks': list(Y), 'sigma': list(best), 'class': [len(U), len(DT)], 'OC1': res})
    return C, ex


if __name__ == '__main__':
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    print('$ python3 k4/oc1_hall/rf_rkmax_rand.py', per, seed, flush=True)
    cores = json.load(gzip.open(os.path.join(_paths.ROOT, 'results', 'k4_certs_5_pure.json.gz')))['cores']
    T = collections.Counter(); shown = 0
    with mp.Pool() as pool:
        for C, ex in pool.imap_unordered(job, [(c['idx'], c['sets'], per, seed) for c in cores], chunksize=8):
            T.update(C)
            for e in ex:
                if shown < 12 or e['OC1'] == 'OC1 fails' or e['class'][1] >= 2: shown += 1; print('ONE-RECEIVER SIGMA-MAXIMAL VECTOR, |D_T| != 1:', json.dumps(e), flush=True)
    for k in sorted(T): print(k, T[k])
