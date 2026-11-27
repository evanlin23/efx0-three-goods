"""Rule (b) of the certifier's good-order export (k4/attack_log.md, 2026-11-27 03:33): at a start where OC1^max fails,
every order whose FIRST agent is the failing start's receiver gives picks satisfying OC1.  Coordinator's independent
test on the n = 4 export (results/k4_oc1max/two_move_starts_n4.json.gz: every OC1^max-failing (type, picks) pair).
Receiver: an agent whose pick no other agent prefers to its own pick.  For each start: the receivers (expected: one),
then every order with a receiver first; orders whose picks are not a maximum matching are counted separately (rule (b)
concerns maximum-matching orders); OC1 via oc1_mc2_rand.Inst.check (raw EFX0, official moves).
    python3 k4/sdc/receiver_first_check.py [STRIDE]"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu

RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results')


def job(a):
    sets, st = a
    I = Inst(sets, st['vals']); P = tuple(st['picks']); n = I.n; N = nu(I)
    rec = [u for u in range(n) if P[u] is not None and all(I.v[i].get(P[u], 0) <= I.v[i].get(P[i], 0) for i in range(n) if i != u)]
    C = collections.Counter(); C['receivers=%d' % len(rec)] += 1; bad = []
    for u in rec:
        seen = {}
        for rest in itertools.permutations([i for i in range(n) if i != u]):
            p = I.sd((u,) + rest)
            if p in seen: continue
            if sum(x is not None for x in p) != N: seen[p] = 'non-max'; C['receiver-first non-max pick vectors'] += 1; continue
            r = I.check(p); seen[p] = r
            C['receiver-first max pick vectors: ' + r] += 1
            if r == 'OC1 fails': bad.append(((u,) + rest, p))
    return C, (sets, st['vals'], P, bad) if bad else None


if __name__ == '__main__':
    STRIDE = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    print('$ python3 k4/sdc/receiver_first_check.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open(os.path.join(RES, 'k4_oc1max', 'two_move_starts_n4.json.gz')))
    tasks = [(h['sets'], st) for h in d['hypergraphs'] for st in h['starts']][::STRIDE]
    print('starts', len(tasks), flush=True)
    T = collections.Counter(); t0 = time.time(); shown = 0
    with mp.Pool() as pool:
        for C, bad in pool.imap_unordered(job, tasks, chunksize=32):
            T.update(C)
            if bad:
                T['starts violating rule (b)'] += 1
                if shown < 5: shown += 1; print('RULE (b) FAILS', json.dumps({'sets': bad[0], 'vals': bad[1], 'picks': bad[2], 'bad': bad[3]}), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
