"""Conjecture HS-MAX at n = 4, 5 (k4/rkmax.md §5): at every sigma-optimal maximum-matching start, the picks complete,
or the hypotheses of a proved repair hold (Prop. T0 / Lemma S' (contains Theorems U and S) / Lemma RF-B).  rk_classes.classify_fast on
the sigma-optimal vectors of the profiles of an n = 5 failure export (FILE), or of random MC2-class cores.
    python3 rk_hsmax_n5.py n4                 # the n = 4 export profiles
    python3 rk_hsmax_n5.py FILE STRIDE
    python3 rk_hsmax_n5.py rand N n SEED"""
import sys, os, gzip, json, collections, time, random, multiprocessing as mp
from rklib import Prof, lexmax
from rk_classes import classify_fast, rand_task


def job(task):
    sets, vals = task
    P = Prof(sets, vals); nu, mm = P.max_matchings()
    best, O = lexmax(mm, P.sigma)
    C = collections.Counter(); C['profiles'] += 1; bad = []
    for Y in O:
        c, ro = classify_fast(sets, vals, Y, P)
        C['sigma-optimal: ' + c] += 1
        C['  %s class (|U|,|D_T|)=(%d,%d)' % (c, len(ro['U']), len(ro['DT']))] += 1
        if c in ('GAP-M', 'F'): bad.append((Y, c))
    return C, (sets, vals, bad) if bad else None


if __name__ == '__main__':
    print('$ python3 k4/rkmax/rk_hsmax_n5.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True)
    if sys.argv[1] == 'n4':
        d = json.load(gzip.open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results',
                                             'k4_oc1max', 'two_move_starts_n4.json.gz')))
        prof = {}
        for h in d['hypergraphs']:
            for st in h['starts']: prof[(json.dumps(h['sets']), json.dumps(st['vals']))] = (h['sets'], st['vals'])
        tasks = list(prof.values())
    elif sys.argv[1] == 'rand':
        N, n, SEED = map(int, sys.argv[2:5])
        with mp.Pool() as pool: tasks = pool.map(rand_task, [(n, SEED * 1000003 + t) for t in range(N)])
    else:
        d = json.load(gzip.open(sys.argv[1])); STRIDE = int(sys.argv[2])
        tasks = []
        for h in d['hypergraphs']:
            seen = set()
            for st in h['starts']:
                key = json.dumps(st['vals'])
                if key in seen: continue
                seen.add(key); tasks.append((h['sets'], st['vals']))
        tasks = tasks[::STRIDE]
    print('profiles', len(tasks), flush=True)
    T = collections.Counter(); t0 = time.time(); shown = 0; done = 0
    with mp.Pool() as pool:
        for C, bad in pool.imap_unordered(job, tasks, chunksize=2):
            T.update(C); done += 1
            if bad and shown < 20:
                shown += 1; print('GAP', json.dumps({'sets': bad[0], 'vals': bad[1], 'picks': bad[2]}), flush=True)
            if done % 2000 == 0: print('..', done, '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
