"""Extremal forms of OC1^{exists max} at n = 5 (companion of extremal_rank_check.py): on the certifier's n = 5 failure
exports (two_move_starts_n5_sel2.json.gz: COMPLETE for 5_pure #419, #447, #38; two_move_starts_n5_partial6.json.gz:
partial), for every exported profile, are the maximum-matching SD pick vectors that are optimal for RM / LMR / RS
(definitions in extremal_rank_check.py) all OC1-good?  OC1 is checked only at the optimal vectors (raw checker
oc1_mc2_rand.Inst.check).  Where an export is complete for a core, a profile outside it has no failing maximum-matching
start, so 0 failures here certifies the statement on that core's profile types.
    python3 k4/sdc/extremal_rank_n5.py FILE [STRIDE]"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
from extremal_rank_check import ranks, POT

NAMES = ('RM', 'LMR', 'RS')


def job(a):
    idx, sets, vals, fail = a
    I = Inst(sets, vals); n = I.n; N = nu(I)
    vec = set(I.sd(o) for o in itertools.permutations(range(n)))
    mm = [p for p in vec if sum(x is not None for x in p) == N]
    rk = {p: ranks(I, p) for p in mm}
    C = collections.Counter(); C['profiles'] += 1; ex = None
    opt = {}
    for name in NAMES:
        f = POT[name]; best = max(f(rk[p]) for p in mm); opt[name] = [p for p in mm if f(rk[p]) == best]
    need = set(p for name in NAMES for p in opt[name])
    res = {p: I.check(p) for p in need}; ok = {p: res[p] != 'OC1 fails' for p in need}
    for name in NAMES:
        O = opt[name]; a_ = all(ok[p] for p in O); s_ = any(ok[p] for p in O)
        for p in O: C[name + ' optimal vectors: ' + res[p]] += 1
        C[name + ' all optimal OK'] += a_; C[name + ' some optimal OK'] += s_
        C[name + ' optimal set size %d' % len(O)] += 1
        C[name + ' exported failing vector is optimal'] += tuple(fail) in O
        if not a_ and ex is None: ex = (name, idx, sets, vals, [(p, rk[p], ok[p]) for p in O])
    return C, ex


if __name__ == '__main__':
    F = sys.argv[1]; STRIDE = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    print('$ python3 k4/sdc/extremal_rank_n5.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open(F))
    tasks = []
    for h in d['hypergraphs']:
        seen = set()
        for st in h['starts']:
            key = json.dumps(st['vals'])
            if key in seen: continue
            seen.add(key); tasks.append((h['idx'], h['sets'], st['vals'], st['picks']))
    tasks = tasks[::STRIDE]
    print('profiles', len(tasks), flush=True)
    T = collections.Counter(); t0 = time.time(); shown = collections.Counter(); done = 0
    with mp.Pool() as pool:
        for C, ex in pool.imap_unordered(job, tasks, chunksize=8):
            T.update(C); done += 1
            if ex and shown[ex[0]] < 3:
                shown[ex[0]] += 1
                print('FAIL', ex[0], json.dumps({'idx': ex[1], 'sets': ex[2], 'vals': ex[3], 'optimal': ex[4]}), flush=True)
            if done % 20000 == 0: print('..', done, '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
