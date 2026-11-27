"""Profile of the HARD sigma-optimal starts (picks with no one-absorber completion), k4/rkmax.md §6.
For each: |U|, |D|, |D_T|, the Theta(z) sizes of the receivers, the receivers' ranks, whether some k in Theta(z) has a
canonical chain to z, and the Lemma S' cases (k, chain, h, r): is h junk or Y_z, is r the head z, another receiver, a
chain agent or another holder; whether k in Theta(z_head); or Lemma RF-B.
    python3 rk_hard_profile.py n4 | FILE STRIDE"""
import sys, os, gzip, json, collections, time, multiprocessing as mp
from rklib import Prof, lexmax
from rk_classes import theta, sprime_cases, rfb_cases

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')


def job(task):
    sets, vals = task
    P = Prof(sets, vals); nu, mm = P.max_matchings(); best, O = lexmax(mm, P.sigma)
    C = collections.Counter()
    for Y in O:
        if P.one_absorber([frozenset([g]) for g in Y]) is not None: continue
        ro = P.roles(Y); r = P.ranks(Y)
        C['hard sigma-optimal'] += 1
        C['class (|U|,|D|,|D_T|)=(%d,%d,%d)' % (len(ro['U']), len(ro['D']), len(ro['DT']))] += 1
        C['receiver (rank, |Theta|): %s' % sorted((r[z], len(theta(P, Y, ro, z))) for z in ro['U'])] += 1
        cases = sprime_cases(P, Y, ro, first=False)
        if cases:
            kinds = set()
            for k, ch, h, rr in cases:
                z = ch[-1]
                rk = 'head' if rr == z else 'receiver' if rr in ro['U'] else 'chain' if rr in ch else 'other'
                kinds.add("S': h %s, r %s, |P|=%d, k in Theta(z) %s, k in D_T %s" % (
                    'Y_z' if h == Y[z] else 'junk', rk, len(ch) - 1, k in theta(P, Y, ro, z), k in ro['DT']))
            for s in kinds: C['   ' + s] += 1
            C['covered by S\''] += 1
        elif rfb_cases(P, Y, ro): C['covered by RF-B only'] += 1
        else: C['NOT COVERED'] += 1
    return C


if __name__ == '__main__':
    print('$ python3 k4/rkmax/rk_hard_profile.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True)
    if sys.argv[1] == 'n4':
        F = os.path.join(ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz'); STRIDE = 1
    else:
        F = sys.argv[1]; STRIDE = int(sys.argv[2])
    d = json.load(gzip.open(F)); prof = {}
    for h in d['hypergraphs']:
        for st in h['starts']: prof[(json.dumps(h['sets']), json.dumps(st['vals']))] = (h['sets'], st['vals'])
    tasks = list(prof.values())[::STRIDE]
    print('profiles', len(tasks), flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, tasks, chunksize=8): T.update(C)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
