"""OC1^exists-max on the n = 5 cores where OC1^max fails (workstream compute/k4-oc1max-cert): the cores of an n = 5
chunk summary (results/k4_oc1max/n5/*_summary.jsonl.gz) that have recorded OC1^max failures, by k4/oc1cert/exists.py.
On every other core of the chunk, OC1^max holds for every profile (the chunk's run found no failure there), so the
exists-order form follows with K4.SDC.MAXSD.

    python3 k4/oc1cert/exists_n5.py SUMMARY.jsonl.gz OUT.json.gz [--jobs=2]"""
import sys, os, gzip, json, time, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), 'k4', 'sdc'))
import exists

if __name__ == '__main__':
    src, out = sys.argv[1], sys.argv[2]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[3:] if a.startswith('--') and '=' in a)
    print('$ python3 k4/oc1cert/exists_n5.py', *sys.argv[1:], flush=True)
    recs = [json.loads(l) for l in gzip.open(src, 'rt') if l.strip()]
    tasks = [(r['list'], r['idx'], r['sets']) for r in recs if r.get('oc1_fails')]
    print('cores with OC1^max failures', len(tasks), 'of', len(recs), flush=True)
    T = collections.Counter(); res = []; t0 = time.time()
    with mp.Pool(int(opt.get('jobs', 2))) as pool:
        for rec in pool.imap_unordered(exists.job, tasks):
            res.append(rec); T['result %s' % rec['result']] += 1; T['iterations'] += rec['iters']
            if rec['result'] != 'certified': print('OC1EXMAX FAILS', json.dumps({k: rec[k] for k in rec if k != 'entries'}), flush=True)
            if len(res) % 20 == 0: print('... %d, %.0f s' % (len(res), time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
    with gzip.open(out, 'wt') as f:
        json.dump({'statement': 'OC1^exists-max on the n = 5 cores of %s with OC1^max failures' % src,
                   'generator': 'k4/oc1cert/exists.py', 'cores': sorted(res, key=lambda r: (r['list'], r['idx']))}, f)
    print('wrote', out)
