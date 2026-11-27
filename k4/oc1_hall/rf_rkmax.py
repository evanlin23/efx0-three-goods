"""The §24.10 class table at the sigma-maximal starts of Conjecture RKMAX (k4/sdc.md §31, ledger K4.SDC.RKMAX) instead
of the RF starts (k4/oc1_hall.md §24.12; coordinator's request).

For every distinct profile of an OC1^max failure export, every serial-dictatorship order is run.  Among the pick
vectors that are maximum matchings (no pickless agent; the cores have nu = n), those whose rank signature
sigma = (#agents holding their rank-1 good, #rank 2, #rank 3, #rank 4) is lexicographically maximal are the
sigma-maximal starts.  Each is classified by (|U|, |D_T|) and by the first repair found, in the order of
rf_n5_all.classify: P (the picks complete), K (a canonical chain from a truly dangerous agent with H0 inside the shared
junk or its own junk), T (a receiver trades with a pick-dangerous agent), RAW (any official move of the raw checker),
FAIL (OC1 fails: a counterexample to RKMAX, printed).

    python3 k4/oc1_hall/rf_rkmax.py EXPORT [EXPORT ...]
(the n = 4 export results/k4_oc1max/two_move_starts_n4.json.gz on main; the n = 5 exports two_move_starts_n5_partial6 /
sel2 of compute/k4-oc1max-cert)
"""
import sys, os, json, gzip, collections, itertools, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks
import rf_n5_all as A
import _paths


def sigma(I, Y):
    s = [0, 0, 0, 0]
    for i, g in enumerate(Y):
        r = sorted(I.R[i], key=lambda h: I.key[i][h], reverse=True).index(g)
        s[r] += 1
    return tuple(s)


def job(task):
    sets, profiles, tag = task
    m = 1 + max(max(s) for s in sets); C = collections.Counter(); bad = []
    for vals in profiles:
        I = Inst(sets, vals, m)
        vecs = set(picks(I, o) for o in itertools.permutations(range(I.n)))
        mx = [Y for Y in vecs if None not in Y]
        C[tag + 'profiles'] += 1
        if not mx: C[tag + 'profiles with no maximum-matching SD vector'] += 1; continue
        best = max(sigma(I, Y) for Y in mx)
        top = [Y for Y in mx if sigma(I, Y) == best]
        C[tag + 'sigma-maximal vectors per profile: %d' % len(top)] += 1
        C[tag + 'sigma-maximal vector is the unique max-matching vector: %s' % (len(mx) == 1)] += 1
        for Y in top:
            C2 = collections.Counter(); b2 = []
            A.classify(I, sets, vals, Y, None, Y, C2, b2, '')
            for k, v in C2.items(): C[tag + k] += v
            for b in b2:
                C[tag + 'RKMAX FAILS (OC1 fails at a sigma-maximal start)'] += 1
                if len(bad) < 3: bad.append({'sets': sets, 'vals': vals, 'picks': list(Y), 'sigma': list(best)})
    return C, bad


def tasks_of(path, tag):
    d = json.load(gzip.open(path))
    for hg in d['hypergraphs']:
        profs = list({json.dumps(st['vals']): st['vals'] for st in hg['starts']}.values())
        for a in range(0, len(profs), 1000):
            yield (hg['sets'], profs[a:a + 1000], tag)


if __name__ == '__main__':
    print('$ python3 k4/oc1_hall/rf_rkmax.py', *[os.path.basename(p) for p in sys.argv[1:]], flush=True)
    tasks = []
    for p in sys.argv[1:]:
        tasks += list(tasks_of(p, ('n=4 ' if 'n4' in os.path.basename(p) else 'n=5 ')))
    T = collections.Counter(); shown = 0
    with mp.Pool() as pool:
        for C, bad in pool.imap_unordered(job, tasks):
            T.update(C)
            for b in bad:
                if shown < 10: shown += 1; print('RKMAX FAILS:', json.dumps(b), flush=True)
    for k in sorted(T): print(k, T[k])
