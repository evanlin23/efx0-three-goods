"""Witnesses for "every failing start is rank-dominated" (k4/rkmax.md §3): for every start of a failure export, a
maximum matching that rank-dominates it (fewest agents changed), written to a gzip JSON file that
tools-free k4/rkmax/rk_dom_check.py re-checks from the raw definitions.
    python3 rk_dom_witness.py EXPORT OUT.json.gz"""
import sys, os, gzip, json, time, multiprocessing as mp
from rklib import Prof
from rk_dominance import dom


def job(task):
    hi, sets, starts = task
    out = []
    for si, st in starts:
        P = Prof(sets, st['vals']); n = P.n; nu, mm = P.max_matchings(); Y = tuple(st['picks'])
        rY = P.ranks(Y)
        D = [M for M in mm if dom(P.ranks(M), rY)]
        best = min(D, key=lambda M: (sum(1 for i in range(n) if M[i] != Y[i]), M)) if D else None
        out.append([hi, si, list(best) if best else None])
    return out


if __name__ == '__main__':
    F, OUT = sys.argv[1], sys.argv[2]
    d = json.load(gzip.open(F)); tasks = []
    for hi, h in enumerate(d['hypergraphs']):
        S = list(enumerate(h['starts']))
        for i in range(0, len(S), 256): tasks.append((hi, h['sets'], S[i:i + 256]))
    t0 = time.time(); W = []
    with mp.Pool() as pool:
        for out in pool.imap(job, tasks): W.extend(out)
    W.sort()
    res = {'what': 'for every start of the export (hypergraph index, start index), a maximum matching that rank-dominates '
                   'its picks (k4/rkmax.md Lemma TC(b)), or null', 'export': os.path.basename(F),
           'witnesses': W}
    with gzip.open(OUT, 'wt') as f: json.dump(res, f)
    print('starts', len(W), 'with witness', sum(w[2] is not None for w in W), 'time %.0f s' % (time.time() - t0))
