"""Class U0 (k4/rkmax.md §6): perfect starts with exactly one receiver z, Theta(z) = {k}, D_T empty, hard, where Lemma S'
fails for every (P, h, r).  For each: OC1 status, sigma-maximal?, and the fewest-agent sigma-raising changes; also the
local data of k and z (ranks, which junk goods they value, the good a that z receives on a longest chain).
    python3 rk_u0_class.py STRIDE"""
import sys, os, gzip, json, collections, time, multiprocessing as mp
from rklib import Prof
from rk_classes import theta, sprime_cases, rfb_cases
from rk_witness import components, role

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')


def job(task):
    sets, vals = task
    P = Prof(sets, vals); n = P.n; nu, mm = P.max_matchings(); smax = max(P.sigma(M) for M in mm)
    C = collections.Counter(); ex = []
    for Y in mm:
        if not P.pareto_optimal(Y): continue
        ro = P.roles(Y)
        if len(ro['U']) != 1 or ro['DT']: continue
        z = ro['U'][0]; th = theta(P, Y, ro, z)
        if len(th) != 1: continue
        if P.one_absorber([frozenset([g]) for g in Y]) is not None: C['U0 start, picks complete'] += 1; continue
        if sprime_cases(P, Y, ro): C["U0 start, hard, S' applies"] += 1; continue
        k = th[0]; r = P.ranks(Y); J = set(ro['J'])
        C['U0 start, hard, no S\': OC1 %s, RF-B %s, sigma-max %s' % (P.oc1(Y), bool(rfb_cases(P, Y, ro)), P.sigma(Y) == smax)] += 1
        Jk = J & P.rel[k]; Jz = J & P.rel[z]
        C['  r_z=%d r_k=%d |J_k|=%d |J_z|=%d |J_k&J_z|=%d k values Y_z %s' % (
            r[z], r[k], len(Jk), len(Jz), len(Jk & Jz), Y[z] in P.rel[k])] += 1
        better = [M for M in mm if P.sigma(M) > P.sigma(Y)]
        kk = min(sum(1 for i in range(n) if M[i] != Y[i]) for M in better)
        descs = set()
        for M in better:
            if sum(1 for i in range(n) if M[i] != Y[i]) != kk: continue
            rM = P.ranks(M)
            descs.add(' + '.join(sorted(kind + '[' + ' '.join(('k' if a == k else 'z' if a == z else role(ro, a)) +
                                                              ':%d>%d' % (r[a], rM[a]) for a in seq) + ']'
                                        for kind, seq in components(P, Y, M))))
        for dsc in descs: C['  sigma-raising: ' + dsc] += 1
        if len(ex) < 2: ex.append({'sets': sets, 'vals': vals, 'picks': Y, 'z': z, 'k': k})
    return C, ex


if __name__ == '__main__':
    STRIDE = int(sys.argv[1])
    print('$ python3 k4/rkmax/rk_u0_class.py', STRIDE, flush=True)
    d = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz'))); prof = {}
    for h in d['hypergraphs']:
        for st in h['starts']: prof[(json.dumps(h['sets']), json.dumps(st['vals']))] = (h['sets'], st['vals'])
    tasks = list(prof.values())[::STRIDE]
    T = collections.Counter(); shown = 0
    with mp.Pool() as pool:
        for C, ex in pool.imap_unordered(job, tasks, chunksize=4):
            T.update(C)
            for e in ex:
                if shown < 4: shown += 1; print('EXAMPLE', json.dumps(e))
    for k in sorted(T): print(k, T[k])
