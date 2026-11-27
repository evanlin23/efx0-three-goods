"""Census of the stored n = 5 two-move starts of a chunk (the coordinator's request; workstream compute/k4-oc1max-cert).

For each stored OC1^max-failing start of a chunk summary (results/k4_oc1max/n5/*_summary.jsonl.gz, field oc1_fails):
- the least number of sequential official moves to a one-absorber completion (three_move_hunt.depth, up to 3);
- ROUND-P (roundp_check.round_p with R = 2: one round of at most two vertex-disjoint OC1' moves);
- the number of receivers.
Per chunk also: how many cores have nu = n, and whether every core with OC1^max failures has nu = n.
The coordinator's code is used unmodified, from a checkout of main given as SDC_DIR (its k4/sdc directory).

    python3 k4/oc1cert/census_n5.py SDC_DIR SUMMARY.jsonl.gz OUT.json.gz [--jobs=2]"""
import sys, os, gzip, json, collections, time, multiprocessing as mp

SDC = sys.argv[1]
sys.path.insert(0, SDC)
import _paths  # noqa: F401,E402
from oc1_mc2_rand import Inst  # noqa: E402
import roundp_check as RP, three_move_hunt as H  # noqa: E402


def receivers(I, P):
    val = lambda i, g: I.v[i].get(g, 0) if g is not None else 0
    return [j for j in range(I.n) if P[j] is not None and not any(i != j and val(i, P[j]) > val(i, P[i]) for i in range(I.n))]


def job(a):
    lst, idx, sets, vals, picks = a
    I = Inst(sets, vals); P = tuple(picks)
    d = H.depth(I, P, 3)
    r, st = RP.round_p(I, P, 2)
    return {'list': lst, 'idx': idx, 'sets': sets, 'vals': vals, 'picks': list(P), 'least moves': d,
            'ROUND-P (moves in the smallest repairing round, R = 2)': r, 'ROUND-P state': st,
            'receivers': receivers(I, P)}


if __name__ == '__main__':
    src, out = os.path.abspath(sys.argv[2]), os.path.abspath(sys.argv[3])
    opt = dict(a[2:].split('=', 1) for a in sys.argv[4:] if a.startswith('--') and '=' in a)
    print('$ python3 k4/oc1cert/census_n5.py SDC_DIR', *sys.argv[2:], flush=True)
    tasks = []; T = collections.Counter()
    for l in gzip.open(src, 'rt'):
        if not l.strip(): continue
        r = json.loads(l); n = len(r['sets'])
        T['cores: nu = n' if r['nu'] == n else 'cores: nu < n'] += 1
        if r.get('oc1_fails'):
            T['cores with OC1^max failures: nu = n' if r['nu'] == n else 'cores with OC1^max failures: NU < N'] += 1
        for f in r.get('oc1_fails') or []: tasks.append((r['list'], r['idx'], r['sets'], f['vals'], f['picks']))
    print('stored failing starts', len(tasks), flush=True)
    res = []; t0 = time.time()
    with mp.Pool(int(opt.get('jobs', 2))) as pool:
        for x in pool.imap_unordered(job, tasks):
            res.append(x)
            T['least moves %s' % x['least moves']] += 1
            T['ROUND-P %s' % x['ROUND-P (moves in the smallest repairing round, R = 2)']] += 1
            T['receivers %d' % len(x['receivers'])] += 1
            T['(least moves, ROUND-P, receivers) = (%s, %s, %d)' % (x['least moves'], x['ROUND-P (moves in the smallest repairing round, R = 2)'], len(x['receivers']))] += 1
            if x['least moves'] not in (0, 1, 2): print('THREE OR MORE MOVES', json.dumps(x), flush=True)
            if x['ROUND-P (moves in the smallest repairing round, R = 2)'] is None: print('ROUND-P FAILS', json.dumps(x), flush=True)
    for k in sorted(T): print(k, T[k])
    with gzip.open(out, 'wt') as f:
        json.dump({'what': 'least moves and ROUND-P at the stored two-move starts of %s' % os.path.basename(src),
                   'code': 'three_move_hunt.depth and roundp_check.round_p (main, unmodified)', 'totals': dict(T),
                   'starts': sorted(res, key=lambda x: (x['list'], x['idx']))}, f)
    print('wrote', out, '%.0f s' % (time.time() - t0))
