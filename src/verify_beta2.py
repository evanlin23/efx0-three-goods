"""Exhaustive check of the constructive proof of conjecture D for beta = 2 (proofs/beta2.md, src/beta2.py).
For every connected core with m = 2n - 1 (nauty genbg) and every ranking profile (6^n), run beta2.construct and check
the allocation it returns: (1) EFX0 for that profile under the raw definition (tools/check_certs.safe, three balanced
realizations of a > b > c, which must agree), (2) at most one bundle with more than two goods. Any ProofError (a
claim of the written proof failing on an instance) is reported. The distinct allocations are saved per core as a
certificate in the frontier.py format, so tools/check_certs.py can re-check coverage of all profiles on its own.
Usage: verify_beta2.py n [n ...] [--jobs=N]     writes certs_beta2_{n}.json.gz and prints a summary per n"""
import sys, os, json, gzip, time, itertools, collections, multiprocessing
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
from check_certs import safe, REAL
from frontier import PERMS, options
from cores_nauty import gen_cores_nauty
import beta2


def raw_mask(n, m, sets, X):
    """mask[i][k]: agent i is EFX0-safe in X when it ranks its goods by PERMS[k] (raw definition)."""
    bundles = [[g for g in range(m) if X[g] == j] for j in range(n)]
    mask = []
    for i, S in enumerate(sets):
        row = []
        for p in PERMS:
            res = {safe(dict(zip((S[p[0]], S[p[1]], S[p[2]]), r)), bundles, i) for r in REAL}
            if len(res) != 1: raise SystemExit("realizations disagree: ordinality violated")
            row.append(res.pop())
        mask.append(row)
    return mask


def check_core(task):
    n, m, pi, sets = task
    allocs, masks = {}, {}
    tally, worst = collections.Counter(), collections.Counter()
    bad = []
    for prof in itertools.product(range(6), repeat=n):
        rank = [tuple(sets[i][k] for k in PERMS[prof[i]]) for i in range(n)]
        info = {}
        try:
            X = tuple(beta2.construct(n, m, sets, rank, info))
        except beta2.ProofError as e:
            bad.append(('proof-claim', str(e), prof)); continue
        if X not in masks:
            masks[X] = raw_mask(n, m, sets, X)
            sizes = sorted(collections.Counter(X).values(), reverse=True) + [0, 0]
            if sizes[1] > 2: bad.append(('two-large-bundles', X, prof))
            allocs[X] = sizes[0]
        if not all(masks[X][i][prof[i]] for i in range(n)): bad.append(('not-EFX0', X, prof))
        tally[info['case']] += 1
        worst[info['case']] = max(worst[info['case']], allocs[X])
        tally['switches=%d' % info.get('switches', 0)] += 1
    cert = {'n': n, 'm': m, 'pi': pi, 'sets': sets, 'mode': 'beta2-construction', 'allocations': [list(X) for X in allocs]}
    return {'sets': sets, 'pi': pi, 'tally': dict(tally), 'largest': dict(worst), 'bad': bad[:5], 'nbad': len(bad)}, cert


if __name__ == '__main__':
    levels, opts = options(sys.argv[1:])
    jobs = int(opts.get('jobs', os.cpu_count()))
    t0 = time.time(); log = lambda s: print(f"[{time.time()-t0:6.0f}s] {s}", flush=True)
    problems = 0
    with multiprocessing.Pool(jobs) as pool:
        for n in levels:
            m = 2 * n - 1
            cores = gen_cores_nauty(n, m)
            log(f"n={n} m={m}: {len(cores)} connected cores, {6 ** n} profiles each")
            tally, largest, certs = collections.Counter(), collections.Counter(), []
            for rec, cert in pool.imap(check_core, [(n, m, pi, sets) for pi, sets in cores]):
                tally.update(rec['tally']); certs.append(cert)
                for k, v in rec['largest'].items(): largest[k] = max(largest[k], v)
                if rec['nbad']:
                    problems += rec['nbad']; log(f"  PROBLEM in {rec['sets']}: {rec['nbad']} e.g. {rec['bad']}")
            with gzip.open(f'certs_beta2_{n}.json.gz', 'wt') as f: json.dump(certs, f)
            cases = {k: v for k, v in tally.items() if not k.startswith('switches')}
            sw = {k: v for k, v in sorted(tally.items()) if k.startswith('switches')}
            log(f"n={n} DONE: {sum(cases.values())} (core, profile) pairs; cases {cases}; largest bundle by case "
                f"{dict(largest)}; collector switches {sw}; problems so far {problems}")
    log(f"ALL DONE; problems: {problems}"); sys.exit(1 if problems else 0)
