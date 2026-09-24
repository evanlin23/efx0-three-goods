"""Certify the cores that the structure theorem leaves for cyclomatic number beta = 3 (proofs/min_counterexample.md, §5).

A minimal counterexample within the class of instances whose incidence-graph components have beta <= 3 is a connected
core with beta = 3, n in {8, 9, 10} agents, and no good of degree 2 shared by two agents that have a private good.
n = 8 (m = 14) is ledger R4 (every connected core). This script lists, for each (n, m) given, every connected core
(nauty genbg, via cores_nauty.py) with no degree-2 good shared by two P-agents, and runs frontier.py's CEGAR search on
each (models C3, then G) over all 6^n ranking profiles. Certificates are frontier.py's format, for tools/check_certs.py.
With --full=FILE, also writes the complete list of connected cores for each (n, m) (records n, m, pi, sets), whose
completeness tools/check_enum.py checks by orbit counting; tools/check_min_cex_cores.py then re-derives the filter and
checks that every core it keeps has a certificate.
Usage: min_cex_cores.py n:m [n:m ...] [--out FILE] [--full FILE] [--jobs N] [--list-only]"""
import sys, time, json, gzip, collections, multiprocessing, os
from cores_nauty import gen_cores_nauty
from frontier import solve_core


def p_agents(sets):
    deg = collections.Counter(g for S in sets for g in S)
    return deg, [i for i, S in enumerate(sets) if any(deg[g] == 1 for g in S)]


def allowed(sets):
    """No good of degree 2 is valued by two agents that have a private good."""
    deg, P = p_agents(sets)
    return not any(d == 2 and sum(g in sets[i] for i in P) == 2 for g, d in deg.items())


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opts = dict((a[2:].split('=', 1) + ['1'])[:2] for a in sys.argv[1:] if a.startswith('--'))
    out = opts.get('out', 'certs_min_cex.json.gz'); jobs = int(opts.get('jobs', os.cpu_count()))
    t0 = time.time(); log = lambda s: print('[%6.0fs] %s' % (time.time() - t0, s), flush=True)
    certs, problems, full = [], 0, []
    with multiprocessing.Pool(jobs) as pool:
        for a in args:
            n, m = map(int, a.split(':'))
            cores = gen_cores_nauty(n, m)
            full += [{'n': n, 'm': m, 'pi': pi, 'sets': s} for pi, s in cores]
            keep = [(pi, s) for pi, s in cores if allowed(s)]
            kinds = collections.Counter((pi, tuple(sorted(d for d in p_agents(s)[0].values() if d >= 3))) for pi, s in keep)
            log('n=%d m=%d beta=%d: %d connected cores, %d with no degree-2 good shared by two P-agents; '
                '(P-agents, degrees >= 3): %s' % (n, m, 2 * n - m + 1, len(cores), len(keep), dict(kinds)))
            tally = collections.Counter()
            if 'list-only' in opts: continue
            for rec, cert in pool.imap_unordered(solve_core, [(n, m, pi, s, ['C3', 'G']) for pi, s in keep]):
                tally[rec['final']] += 1
                if cert: certs.append(cert)
                else: problems += 1; log('NO CERTIFICATE: %s' % json.dumps(rec)[:300])
                if rec['final'] not in ('C3', 'G'): problems += 1
            log('n=%d m=%d done: %s' % (n, m, dict(tally)))
    if 'full' in opts:
        with gzip.open(opts['full'], 'wt') as f: json.dump(full, f)
        log('wrote the %d connected cores to %s' % (len(full), opts['full']))
    if 'list-only' in opts: sys.exit(0)
    with gzip.open(out, 'wt') as f: json.dump(certs, f)
    log('wrote %d certificates to %s; problems: %d' % (len(certs), out, problems))
    sys.exit(1 if problems else 0)
