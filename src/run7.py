"""n = 7 frontier (default m = 13, 12, 11); tests conjecture D (model C3, then G), saves results and certificates.
--n=8 runs n = 8 instead (e.g. `run7.py 15 --n=8`); --jobs=N sets the number of parallel workers (default: all CPUs).
Cores come from nauty's genbg (cores_nauty.py). The v1 version of this file is in archive/v1-python-enumeration/."""
import sys, time, json, collections, gzip, os, multiprocessing
from frontier import solve_core, options
from cores_nauty import gen_cores_nauty

if __name__ == '__main__':
    ms, opts = options(sys.argv[1:]); n = int(opts.get('n', 7)); ms = ms or list(range(2 * n - 1, n + 3, -1))
    jobs = int(opts.get('jobs', os.cpu_count())); tag = "_".join(map(str, ms))
    t0 = time.time(); log = lambda s: print(f"[{time.time()-t0:6.0f}s] {s}", flush=True); out, certs = [], []
    with multiprocessing.Pool(jobs) as pool:
        for m in ms:
            t1 = time.time(); cores = gen_cores_nauty(n, m)
            log(f"n={n} m={m} beta={2*n-m+1}: {len(cores)} connected cores (generated in {time.time()-t1:.1f}s, {jobs} jobs)")
            tally = collections.Counter()
            for k, (rec, cert) in enumerate(pool.imap(solve_core, [(n, m, pi, sets, ['C3', 'G']) for pi, sets in cores]), 1):
                if cert: certs.append(cert)
                tally[rec['final']] += 1; out.append(rec)
                if k % 500 == 0: log(f"   {k}/{len(cores)} {dict(tally)}")
            log(f"n={n} m={m} DONE: {dict(tally)}")
            json.dump(out, open(f'frontier_results_{n}_{tag}.json', 'w'))
            with gzip.open(f'certs_{n}_{tag}.json.gz', 'wt') as f: json.dump(certs, f)
    log("ALL DONE")
