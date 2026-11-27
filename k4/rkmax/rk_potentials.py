"""Which extremal rule over maximum-matching SD vectors lands on OC1 (resp. on picks that complete with no move)?
(k4/rkmax.md §5).  n = 4 export profiles (every profile with a failing maximum-matching start).

For each profile: every maximum matching that is Pareto optimal (= an SD outcome, Lemma SDPO) with its OC1 status
(P picks complete / M one move / F fails), sigma, rank sum, number of receivers |U|, the largest receiver rank, and
whether Prop. T0 applies (some receiver z with Theta(z) empty).  For each candidate potential (lexicographic keys,
maximized), count the profiles where EVERY optimum is OC1 / is 'P' / satisfies T0.
    python3 rk_potentials.py [STRIDE]"""
import sys, os, gzip, json, collections, time, multiprocessing as mp
from rklib import Prof
from rk_classes import theta

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')


def feats(P, Y):
    ro = P.roles(Y); r = P.ranks(Y)
    return dict(sig=P.sigma(Y), rs=-sum(r), lmr=tuple(-x for x in sorted(r, reverse=True)), U=len(ro['U']),
                umax=-max(r[u] for u in ro['U']), DT=-len(ro['DT']), D=-len(ro['D']), F=-len(ro['F']),
                t0=any(not theta(P, Y, ro, z) for z in ro['U']))


POTS = {
    'RM (sigma)': lambda f: f['sig'],
    'RS': lambda f: f['rs'],
    'LMR': lambda f: f['lmr'],
    '|U| then sigma': lambda f: (f['U'], f['sig']),
    'sigma then |U|': lambda f: (f['sig'], f['U']),
    'fewest frozen then sigma': lambda f: (f['F'], f['sig']),
    'fewest dangerous then sigma': lambda f: (f['D'], f['sig']),
    'fewest D_T then sigma': lambda f: (f['DT'], f['sig']),
    'best worst-receiver rank then sigma': lambda f: (f['umax'], f['sig']),
    'RS then |U|': lambda f: (f['rs'], f['U']),
}


def job(task):
    sets, vals = task
    P = Prof(sets, vals); nu, mm = P.max_matchings()
    po = [M for M in mm if P.pareto_optimal(M)]
    F = {M: feats(P, M) for M in po}; st = {M: P.oc1(M) for M in po}
    C = collections.Counter(); C['profiles'] += 1
    C['profiles where some PO max matching completes at the picks'] += any(st[M] == 'P' for M in po)
    C['profiles where some PO max matching satisfies T0'] += any(F[M]['t0'] for M in po)
    for name, key in POTS.items():
        b = max(key(F[M]) for M in po); O = [M for M in po if key(F[M]) == b]
        C[name + ': every optimum OC1'] += all(st[M] != 'F' for M in O)
        C[name + ': every optimum completes at picks'] += all(st[M] == 'P' for M in O)
        C[name + ': every optimum satisfies T0'] += all(F[M]['t0'] for M in O)
    return C


if __name__ == '__main__':
    STRIDE = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    print('$ python3 k4/rkmax/rk_potentials.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz')))
    prof = collections.OrderedDict()
    for h in d['hypergraphs']:
        for st in h['starts']: prof[(json.dumps(h['sets']), json.dumps(st['vals']))] = (h['sets'], st['vals'])
    tasks = list(prof.values())[::STRIDE]
    print('profiles', len(tasks), flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, tasks, chunksize=8): T.update(C)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
