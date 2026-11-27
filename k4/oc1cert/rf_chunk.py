"""Conjecture RF (receiver first, K4.SDC.RF) at every OC1^max-failing pair the CEGAR meets on an n = 5 chunk run before
run.py checked RF itself (workstream compute/k4-oc1max-cert).

The cores of the chunk summary with recorded OC1^max failures are rerun with run.job at depth 2 (no compaction), which
now checks RF at every failing (type profile, picks) pair met (good_orders.rf, raw Inst code). The CEGAR is
deterministic, so the number of pairs met is compared with the summary's n_oc1_fail_pairs_met.

    python3 k4/oc1cert/rf_chunk.py SUMMARY.jsonl.gz OUT.jsonl.gz [--jobs=2]"""
import sys, os, gzip, json, time, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(HERE)), 'k4', 'sdc'))
import run


def job(r):
    out = run.job((r['list'], r['idx'], r['sets'], None, False, 2))
    return r, out


if __name__ == '__main__':
    src, dst = sys.argv[1], sys.argv[2]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[3:] if a.startswith('--') and '=' in a)
    print('$ python3 k4/oc1cert/rf_chunk.py', *sys.argv[1:], flush=True)
    recs = [json.loads(l) for l in gzip.open(src, 'rt') if l.strip()]
    tasks = [r for r in recs if r.get('oc1_fails')]
    print('cores with OC1^max failures', len(tasks), 'of', len(recs), flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool(int(opt.get('jobs', 2))) as pool, gzip.open(dst, 'wt') as f:
        for k, (r, o) in enumerate(pool.imap_unordered(job, tasks)):
            rf = o.get('rf', {'pairs checked': 0, 'violations': [], 'receiver-first maximum pick vectors checked': 0})
            T['cores'] += 1; T['result %s' % o['result']] += 1
            T['RF: failing pairs checked (every pair met)'] += rf['pairs checked']
            T['RF: receiver-first maximum pick vectors checked'] += rf['receiver-first maximum pick vectors checked']
            T['RF: VIOLATIONS'] += len(rf['violations'])
            for nr, c in rf.get('receivers at the failing start', {}).items(): T['failing pairs met with %s receivers' % nr] += c
            same = o.get('n_oc1_fail_pairs_met', 0) == r['n_oc1_fail_pairs_met']
            T['pairs met equal to the chunk run' if same else 'PAIRS MET DIFFER FROM THE CHUNK RUN'] += 1
            for v in rf['violations']:
                print('RF VIOLATION', json.dumps({'list': r['list'], 'idx': r['idx'], 'sets': r['sets'], **v}), flush=True)
            f.write(json.dumps({'list': r['list'], 'idx': r['idx'], 'm': o['m'], 'sets': r['sets'], 'result': o['result'],
                                'n_oc1_fail_pairs_met': o.get('n_oc1_fail_pairs_met', 0),
                                'chunk run n_oc1_fail_pairs_met': r['n_oc1_fail_pairs_met'], 'rf': rf}) + '\n')
            if (k + 1) % 20 == 0: print('... %d, %.0f s' % (k + 1, time.time() - t0), flush=True)
    for key in sorted(T): print(key, T[key])
    print('time %.0f s' % (time.time() - t0)); print('wrote', dst)
