"""n = 7 frontier (default m = 13, 12, 11); tests conjecture D (model C3, then G), saves results and certificates.
--n=8 runs n = 8 instead (e.g. `run7.py 15 --n=8`); --jobs=N sets the number of parallel workers (default: all CPUs).
Cores come from nauty's genbg (cores_nauty.py). The v1 version of this file is in archive/v1-python-enumeration/.
Checkpoints: each solved hypergraph is appended to checkpoint_{n}_{m}.jsonl as soon as it finishes; a rerun resumes
from it, and it is deleted once that m is complete and its results are written. --fresh ignores an existing one."""
import sys, time, json, collections, gzip, os, multiprocessing
from frontier import solve_core, options
from cores_nauty import gen_cores_nauty

def solve_indexed(task):
    k, t = task
    return k, solve_core(t)

def load_checkpoint(path):
    """Records by hypergraph (its `sets`, as JSON); a line cut off by an interruption is ignored."""
    done = {}
    if os.path.exists(path):
        for line in open(path):
            try: d = json.loads(line)
            except json.JSONDecodeError: continue
            done[json.dumps(d['sets'])] = (d['rec'], d['cert'])
    return done

if __name__ == '__main__':
    ms, opts = options(sys.argv[1:]); n = int(opts.get('n', 7)); ms = ms or list(range(2 * n - 1, n + 3, -1))
    jobs = int(opts.get('jobs', os.cpu_count())); tag = "_".join(map(str, ms))
    t0 = time.time(); log = lambda s: print(f"[{time.time()-t0:6.0f}s] {s}", flush=True); out, certs = [], []
    with multiprocessing.Pool(jobs) as pool:
        for m in ms:
            t1 = time.time(); cores = gen_cores_nauty(n, m); ckpt = f'checkpoint_{n}_{m}.jsonl'
            if 'fresh' in opts and os.path.exists(ckpt): os.remove(ckpt)
            done = load_checkpoint(ckpt)
            results = [done.get(json.dumps(sets)) for _, sets in cores]
            log(f"n={n} m={m} beta={2*n-m+1}: {len(cores)} connected cores (generated in {time.time()-t1:.1f}s, {jobs} jobs)"
                + (f"; {sum(r is not None for r in results)} resumed from {ckpt}" if done else ""))
            todo = [(k, (n, m, pi, sets, ['C3', 'G'])) for k, (pi, sets) in enumerate(cores) if results[k] is None]
            tally = collections.Counter(r[0]['final'] for r in results if r is not None)
            with open(ckpt, 'a') as f:
                for i, (k, (rec, cert)) in enumerate(pool.imap_unordered(solve_indexed, todo), 1):
                    results[k] = (rec, cert); tally[rec['final']] += 1
                    f.write(json.dumps({'sets': cores[k][1], 'rec': rec, 'cert': cert}) + '\n'); f.flush()
                    if i % 500 == 0: log(f"   {len(cores) - len(todo) + i}/{len(cores)} {dict(tally)}")
            for rec, cert in results:
                out.append(rec)
                if cert: certs.append(cert)
            log(f"n={n} m={m} DONE: {dict(tally)}")
            json.dump(out, open(f'frontier_results_{n}_{tag}.json', 'w'))
            with gzip.open(f'certs_{n}_{tag}.json.gz', 'wt') as f: json.dump(certs, f)
            os.remove(ckpt)
    log("ALL DONE")
