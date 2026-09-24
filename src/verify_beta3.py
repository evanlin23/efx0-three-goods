"""Exhaustive check of the constructive proof of conjecture D for beta = 3 (proofs/beta3.md, src/beta3.py).
For every connected core with m = 2n - 2 (nauty genbg) and every ranking profile (6^n), run beta3.construct and check
the allocation it returns: (1) EFX0 for that profile under the raw definition (tools/check_certs.safe, three balanced
realizations of a > b > c, which must agree), (2) at most one bundle with more than two goods. Any ProofError (a
claim of the written proof failing on an instance) is reported. The distinct allocations are saved per core as a
certificate in the frontier.py format, so tools/check_certs.py can re-check coverage of all profiles on its own.
Also tallies, per number q of Q-agents, which kind of large bundle the proof used (none, the main collector's, or a
dump target held by a P-agent or a Q-agent) and its largest size.
Usage: verify_beta3.py n [n ...] [--jobs=N] [--beta=3]   writes certs_beta3_{n}.json.gz, prints a summary per n
       (--beta=2 runs the same construction on the m = 2n - 1 cores, as a cross-check against proofs/beta2.md)"""
import sys, os, json, gzip, time, itertools, collections, multiprocessing
from frontier import PERMS, options
from cores_nauty import gen_cores_nauty
from verify_beta2 import raw_mask
import beta3


def check_core(task):
    n, m, pi, sets = task
    allocs, masks = {}, {}
    tally, worst = collections.Counter(), collections.Counter()
    bad = []
    for prof in itertools.product(range(6), repeat=n):
        rank = [tuple(sets[i][k] for k in PERMS[prof[i]]) for i in range(n)]
        info = {}
        try:
            X = tuple(beta3.construct(n, m, sets, rank, info))
        except beta3.ProofError as e:
            bad.append(('proof-claim', str(e), prof)); continue
        if X not in masks:
            masks[X] = raw_mask(n, m, sets, X)
            sizes = sorted(collections.Counter(X).values(), reverse=True) + [0, 0]
            if sizes[1] > 2: bad.append(('two-large-bundles', X, prof))
            allocs[X] = sizes[0]
        if not all(masks[X][i][prof[i]] for i in range(n)): bad.append(('not-EFX0', X, prof))
        kind = f"q={info['q']}:{info['large']}"
        tally[kind] += 1
        worst[kind] = max(worst[kind], allocs[X])
        tally['switches=%d' % info.get('switches', 0)] += 1
    cert = {'n': n, 'm': m, 'pi': pi, 'sets': sets, 'mode': 'beta3-construction', 'allocations': [list(X) for X in allocs]}
    return {'sets': sets, 'pi': pi, 'tally': dict(tally), 'largest': dict(worst), 'bad': bad[:5], 'nbad': len(bad)}, cert


if __name__ == '__main__':
    levels, opts = options(sys.argv[1:])
    jobs = int(opts.get('jobs', os.cpu_count()))
    beta = int(opts.get('beta', 3))
    t0 = time.time(); log = lambda s: print(f"[{time.time()-t0:6.0f}s] {s}", flush=True)
    problems = 0
    with multiprocessing.Pool(jobs) as pool:
        for n in levels:
            m = 2 * n + 1 - beta
            cores = gen_cores_nauty(n, m)
            log(f"n={n} m={m} (beta={beta}): {len(cores)} connected cores, {6 ** n} profiles each")
            tally, largest, certs = collections.Counter(), collections.Counter(), []
            for rec, cert in pool.imap(check_core, [(n, m, pi, sets) for pi, sets in cores]):
                tally.update(rec['tally']); certs.append(cert)
                for k, v in rec['largest'].items(): largest[k] = max(largest[k], v)
                if rec['nbad']:
                    problems += rec['nbad']; log(f"  PROBLEM in {rec['sets']}: {rec['nbad']} e.g. {rec['bad']}")
            with gzip.open(f'certs_beta{beta}_{n}.json.gz' if beta == 3 else f'certs_beta3code_beta{beta}_{n}.json.gz',
                           'wt') as f:
                json.dump(certs, f)
            cases = {k: v for k, v in sorted(tally.items()) if not k.startswith('switches')}
            sw = {k: v for k, v in sorted(tally.items()) if k.startswith('switches')}
            log(f"n={n} DONE: {sum(cases.values())} (core, profile) pairs; large bundle by q {cases}; largest bundle "
                f"{dict(sorted(largest.items()))}; collector switches {sw}; problems so far {problems}")
    log(f"ALL DONE; problems: {problems}"); sys.exit(1 if problems else 0)
