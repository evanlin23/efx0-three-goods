"""Batch runner: OC1^max for every strict profile of every core hypergraph in a k = 4 core list (results/k4_certs_*.json.gz,
written by k4/search4.py), by the ordinal CEGAR of k4/oc1cert/cegar.py.

    python3 k4/oc1cert/run.py LIST[,LIST...] --out=results/k4_oc1max/cert_<tag>.json.gz [--jobs=4] [--stride=S --offset=O]
           [--limit=SEC] [--no-compact] [--depth=D] [--idx=I,J,...]
--depth=D: up to D moves in sequence (OC_D form; default 1 = OC1^max).  --idx: only these core indices (within m).

LIST is a name like 2, 3, 4_n4_1, 5_pure (results/k4_certs_<LIST>.json.gz).  A hypergraph whose outer loop finds a
(profile, picks) pair with no witness is re-checked at once with the raw checker k4/sdc/oc1_mc2_rand.Inst (its SD picks
over every order, its moves, its brute-force one-absorber completion) and printed as OC1MAX CANDIDATE FAILURE."""
import sys, os, gzip, json, time, itertools, collections, multiprocessing as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from cegar import Cert


def raw_check(sets, vals, picks):
    from oc1_mc2_rand import Inst
    I = Inst(sets, vals)
    orders = [o for o in itertools.permutations(range(I.n)) if I.sd(o) == tuple(picks)]
    return {'orders_giving_picks': len(orders), 'raw': I.check(tuple(picks))}


def job(task):
    lst, idx, sets, limit, compact, depth = task
    t0 = time.time()
    C = Cert(sets, depth=depth)
    r = C.run(time_limit=limit)
    rec = {'list': lst, 'idx': idx, 'sets': sets, 'm': C.m, 'nu': C.nu, 'domains': [len(D) for D in C.dom],
           'result': r, 'stats': C.stats(), 'time': round(time.time() - t0, 3)}
    if r == 'certified':
        W = C.compact() if compact else C.witnesses
        rec['witnesses'] = [w.to_json() for w in W]
        rec['n_witnesses_before_compaction'] = len(C.witnesses)
    elif r == 'FAIL':
        rec['fails'] = []
        for prof, Y in C.fails:
            vals = [list(C.dom[i][t]) for i, t in enumerate(prof)]
            rec['fails'].append({'vals': vals, 'picks': list(Y), 'raw_check': raw_check(sets, vals, Y)})
    rec['time'] = round(time.time() - t0, 3)
    return rec


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], '1') for a in sys.argv[1:] if a.startswith('--'))
    lists = args[0].split(',')
    out = opt.get('out'); jobs = int(opt.get('jobs', mp.cpu_count()))
    stride, offset = int(opt.get('stride', 1)), int(opt.get('offset', 0))
    limit = float(opt['limit']) if 'limit' in opt else None
    compact = 'no-compact' not in opt
    depth = int(opt.get('depth', 1))
    idxs = set(map(int, opt['idx'].split(','))) if 'idx' in opt else None
    print('$ python3 k4/oc1cert/run.py', *sys.argv[1:], flush=True)
    tasks = []
    for lst in lists:
        d = json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_certs_%s.json.gz' % lst)))
        for c in d['cores'][offset::stride]:
            if idxs is not None and (lst, c['idx']) not in idxs and c['idx'] not in idxs: continue
            tasks.append((lst, c['idx'], c['sets'], limit, compact, depth))
    print('hypergraphs', len(tasks), 'jobs', jobs, flush=True)
    t0 = time.time(); T = collections.Counter(); recs = []; tmax = (0, None)
    with mp.Pool(jobs) as pool:
        for k, rec in enumerate(pool.imap_unordered(job, tasks, chunksize=1 if len(tasks) < 200 else 4)):
            recs.append(rec)
            T['result %s' % rec['result']] += 1
            T['%s nu=%d n=%d' % (rec['list'], rec['nu'], len(rec['sets']))] += 1
            for kd, c in rec['stats']['kinds'].items(): T['witness kind %s (found by the inner)' % kd] += c
            T['iterations'] += rec['stats']['iters']
            T['witnesses kept'] += len(rec.get('witnesses', []))
            if rec['time'] > tmax[0]: tmax = (rec['time'], (rec['list'], rec['idx']))
            if rec['result'] != 'certified':
                print('NOT CERTIFIED', json.dumps({x: rec[x] for x in rec if x != 'witnesses'}), flush=True)
                for f in rec.get('fails', []):
                    if f['raw_check']['raw'] == 'OC1 fails' and f['raw_check']['orders_giving_picks'] > 0:
                        print('OC1MAX CANDIDATE FAILURE (raw checker agrees)', json.dumps({'sets': rec['sets'], **f}), flush=True)
            if (k + 1) % 500 == 0:
                print('... %d hypergraphs, %.0f s' % (k + 1, time.time() - t0), flush=True)
    recs.sort(key=lambda r: (r['list'], r['idx']))
    for key in sorted(T): print(key, T[key])
    print('slowest hypergraph %.2f s %s' % tmax)
    print('time %.0f s' % (time.time() - t0))
    if out:
        os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
        with gzip.open(out, 'wt') as f:
            json.dump({'statement': 'OC1^max (K4.SDC.OC1MAX) for every strict profile: for every type profile and every '
                                    'SD order whose picks form a maximum matching, the picks have a one-absorber EFX0 '
                                    'completion or at most DEPTH official moves (addition, chain, ring) give bases that '
                                    'have one (DEPTH = 1 is OC1^max)', 'depth': depth,
                       'generator': 'k4/oc1cert/cegar.py', 'lists': lists, 'stride': stride, 'offset': offset,
                       'cores': recs}, f)
        print('wrote', out)


if __name__ == '__main__':
    main()
