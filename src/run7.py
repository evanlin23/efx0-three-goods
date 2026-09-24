"""n = 7 frontier (default m = 13, 12, 11); tests conjecture D (model C3), saves results and certificates."""
import sys, time, json, collections, gzip
from frontier import gen_cores, cegar, certify
ms = [int(a) for a in sys.argv[1:]] or [13, 12, 11]; tag = "_".join(map(str, ms))
t0 = time.time(); log = lambda s: print(f"[{time.time()-t0:6.0f}s] {s}", flush=True); out, certs = [], []
for m in ms:
    t1 = time.time(); cores = gen_cores(7, m)
    log(f"n=7 m={m} beta={15-m}: {len(cores)} connected cores (generated in {time.time()-t1:.0f}s)")
    tally = collections.Counter()
    for pi, sets in cores:
        rec = {'n': 7, 'm': m, 'pi': pi, 'sets': sets}
        for md in ('C3', 'G'):
            st, bad, masks, allocs = cegar(7, m, sets, md)
            if st == 'OK':
                unc = certify(7, masks); rec['final'] = md if unc == 0 else md + '-CERTFAIL'
                certs.append({'n': 7, 'm': m, 'pi': pi, 'sets': sets, 'mode': md, 'allocations': allocs}); break
            if st != 'FAIL': rec['final'] = md + '-' + st; break
            rec['bad_' + md] = bad
        else: rec['final'] = 'NO-EFX0'
        tally[rec['final']] += 1; out.append(rec)
    log(f"n=7 m={m} DONE: {dict(tally)}")
    json.dump(out, open(f'frontier_results_7_{tag}.json', 'w'))
    with gzip.open(f'certs_7_{tag}.json.gz', 'wt') as f: json.dump(certs, f)
log("ALL DONE")
