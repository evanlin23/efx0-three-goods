"""Rule (b) (receiver-first orders satisfy OC1) on the certifier's stored n = 5 OC1^max failures: the oc1_fails field of
results/k4_oc1max/n5/5_pure_s5o0_summary.jsonl.gz (compute/k4-oc1max-cert).  Coordinator's own code, as in
receiver_first_check.py.
    python3 k4/sdc/receiver_first_n5.py SUMMARY.jsonl.gz"""
import sys, gzip, json, collections, multiprocessing as mp
import _paths  # noqa: F401
import receiver_first_check as R

if __name__ == '__main__':
    print('$ python3 k4/sdc/receiver_first_n5.py', *sys.argv[1:], flush=True)
    rows = [json.loads(l) for l in gzip.open(sys.argv[1])]
    tasks = [(r['sets'], {'vals': f['vals'], 'picks': f['picks']}) for r in rows for f in r.get('oc1_fails') or []]
    print('stored failing starts', len(tasks), flush=True)
    T = collections.Counter()
    with mp.Pool() as pool:
        for C, bad in pool.imap_unordered(R.job, tasks, chunksize=4):
            T.update(C)
            if bad: T['starts violating rule (b)'] += 1; print('RULE (b) FAILS', json.dumps({'sets': bad[0], 'vals': bad[1], 'picks': bad[2], 'bad': bad[3]}), flush=True)
    for k in sorted(T): print(k, T[k])
