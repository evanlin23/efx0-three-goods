"""Independent check of Conjecture RKMAX at n = 4 (k4/rkmax.md §2), second implementation (rklib.py; the first is
k4/sdc/extremal_rank_check.py on claude/kind-lamport-y8fdme).

Data: the certifier's complete n = 4 export results/k4_oc1max/two_move_starts_n4.json.gz (every (type profile, picks)
pair of a strict connected n = 4 core whose maximum-matching SD picks fail OC1; a profile outside it has no failing
maximum-matching start, by the OC1^max certificate K4.SDC.OC1MAX.N3).

For every exported profile (sets, vals):
  1. enumerate ALL matchings directly, keep the maximum ones (nu), compute sigma, take the lexicographic maximum set O;
  2. check every M in O is Pareto optimal (brute force over all matchings) and is the SD outcome of some order;
  3. check OC1 at every M in O with rklib's raw checker (completion at the picks 'P', one official move 'M', fails 'F');
  4. also: the exported failing picks fail OC1 under rklib (re-check of the export, every start);
  5. also the minimum-rank-sum (RS) and leximin (LMR) optima, and the classes (|U|, |D_T|) of the sigma-optimal starts.
    python3 rk_check_n4.py [STRIDE]"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
from rklib import Prof, lexmax

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')

POT = {'RM': lambda P, M: P.sigma(M),
       'RS': lambda P, M: -sum(P.ranks(M)),
       'LMR': lambda P, M: tuple(-x for x in sorted(P.ranks(M), reverse=True))}


def job(task):
    sets, vals, starts = task
    P = Prof(sets, vals); n = P.n
    C = collections.Counter(); C['profiles'] += 1
    nu, mm = P.max_matchings()
    sdset = set(P.sd(o) for o in itertools.permutations(range(n)))
    res = {}
    def oc(M):
        if M not in res: res[M] = P.oc1(M)
        return res[M]
    for name, f in POT.items():
        best, O = lexmax(mm, lambda M: f(P, M))
        C[name + ': optimal vectors'] += len(O)
        for M in O:
            C[name + ': optimal vector is PO'] += P.pareto_optimal(M)
            C[name + ': optimal vector is an SD outcome'] += M in sdset
            r = oc(M); C[name + ': optimal vector OC1 ' + r] += 1
            if name == 'RM':
                ro = P.roles(M)
                C['RM optimum class (|U|,|D_T|)=(%d,%d) OC1 %s' % (len(ro['U']), len(ro['DT']), r)] += 1
        C[name + ': profiles with every optimum OC1'] += all(oc(M) != 'F' for M in O)
        C[name + ': profiles with some optimum OC1'] += any(oc(M) != 'F' for M in O)
    # re-check the exported failing starts
    for st in starts:
        Y = tuple(st['picks'])
        C['exported starts'] += 1
        C['exported start is a maximum matching'] += sum(g is not None for g in Y) == nu
        C['exported start is SD'] += Y in sdset
        C['exported start fails OC1 (rklib)'] += oc(Y) == 'F'
        C['exported start sigma < sigma-max'] += P.sigma(Y) < max(P.sigma(M) for M in mm)
    return C


if __name__ == '__main__':
    STRIDE = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    print('$ python3 k4/rkmax/rk_check_n4.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz')))
    prof = collections.OrderedDict()
    for h in d['hypergraphs']:
        for st in h['starts']:
            key = (json.dumps(h['sets']), json.dumps(st['vals']))
            prof.setdefault(key, (h['sets'], st['vals'], []))[2].append(st)
    tasks = list(prof.values())[::STRIDE]
    print('profiles', len(tasks), 'starts', sum(len(t[2]) for t in tasks), flush=True)
    T = collections.Counter(); t0 = time.time(); done = 0
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, tasks, chunksize=8):
            T.update(C); done += 1
            if done % 10000 == 0: print('..', done, '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
