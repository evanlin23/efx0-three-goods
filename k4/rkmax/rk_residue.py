"""The HS-MAX residue at arbitrary starts (k4/rkmax.md §6): Pareto-optimal maximum matchings (= SD outcomes) that are
hard (no one-absorber completion at the picks) and covered by none of Prop. T0, Lemma S', Lemma RF-B.  HS-MAX says
none of them is sigma-maximal.  For each: OC1 status, class, receiver ranks, and the fewest-agent sigma-raising change
(components and roles), to see what a proof of "residue => not sigma-maximal" must produce.
    python3 rk_residue.py n4 STRIDE | FILE STRIDE"""
import sys, os, gzip, json, collections, time, multiprocessing as mp
from rklib import Prof
from rk_classes import theta, sprime_cases, rfb_cases
from rk_witness import components, role

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')


def job(task):
    sets, vals = task
    P = Prof(sets, vals); n = P.n; nu, mm = P.max_matchings()
    smax = max(P.sigma(M) for M in mm)
    C = collections.Counter()
    for Y in mm:
        if not P.pareto_optimal(Y): continue
        C['PO max matchings'] += 1
        ro = P.roles(Y)
        if any(not theta(P, Y, ro, z) for z in ro['U']): C['T0'] += 1; continue
        if P.one_absorber([frozenset([g]) for g in Y]) is not None: C['picks complete (not T0)'] += 1; continue
        if sprime_cases(P, Y, ro): C["hard, S'"] += 1; continue
        if rfb_cases(P, Y, ro): C['hard, RF-B'] += 1; continue
        st = P.oc1(Y); sY = P.sigma(Y); r = P.ranks(Y)
        C['RESIDUE (hard, no T0/S\'/RF-B), OC1 %s, sigma-max %s' % (st, sY == smax)] += 1
        C['  residue class (|U|,|D|,|D_T|)=(%d,%d,%d), receiver ranks %s' % (
            len(ro['U']), len(ro['D']), len(ro['DT']), sorted(r[u] for u in ro['U']))] += 1
        better = [M for M in mm if P.sigma(M) > sY]
        if better:
            k = min(sum(1 for i in range(n) if M[i] != Y[i]) for M in better)
            descs = set()
            for M in better:
                if sum(1 for i in range(n) if M[i] != Y[i]) != k: continue
                rM = P.ranks(M)
                descs.add(' + '.join(sorted(kind + '[' + ' '.join('%s:%d>%d' % (role(ro, a), r[a], rM[a]) for a in seq)
                                            + ']' for kind, seq in components(P, Y, M))))
            for dsc in descs: C['  residue: a fewest-agent sigma-raising change: ' + dsc] += 1
    return C


if __name__ == '__main__':
    print('$ python3 k4/rkmax/rk_residue.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True)
    F = os.path.join(ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz') if sys.argv[1] == 'n4' else sys.argv[1]
    STRIDE = int(sys.argv[2])
    d = json.load(gzip.open(F)); prof = {}
    for h in d['hypergraphs']:
        for st in h['starts']: prof[(json.dumps(h['sets']), json.dumps(st['vals']))] = (h['sets'], st['vals'])
    tasks = list(prof.values())[::STRIDE]
    print('profiles', len(tasks), flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, tasks, chunksize=4): T.update(C)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
