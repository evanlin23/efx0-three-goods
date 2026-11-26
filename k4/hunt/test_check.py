"""Sensitivity test of k4/hunt/check.py: thinned certificates must be rejected, and every coverage engine must agree.

For each core of the given certificate files (named cores or a class sample): drop a random fraction of the
allocations (several rates) and run the engines; when they say "not covered", the reported profile is re-checked
with explicit values against every remaining allocation (raw definition, cegar.efx0_raw) and must have none.
Usage: test_check.py FILE [FILE ...] [--cores=K] [--engines=sat2,dfs,sat]"""
import sys, os, gzip, json, random, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
import check, cegar

def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--'))
    engines = opt.get('engines', 'sat2,dfs').split(',')
    rng = random.Random(3)
    cores = []
    for f in files:
        d = json.load(gzip.open(f, 'rt'))
        for c in d['cores']:
            c.setdefault('n', d.get('n')); c.setdefault('m', d.get('m')); cores.append(c)
    cores = rng.sample(cores, min(int(opt.get('cores', 10)), len(cores)))
    print('command: python3 k4/hunt/test_check.py ' + ' '.join(sys.argv[1:]), flush=True)
    bad = rejected = total = 0
    for c in cores:
        for rate in (0.0, 0.02, 0.1, 0.3):
            A = [a for a in c['allocs'] if rng.random() >= rate]
            res = {e: check.covered((c['n'], c['m'], c['sets'], A, e)) for e in engines}
            verdicts = {e: r[0] for e, r in res.items()}
            total += 1
            if len(set(verdicts.values())) > 1: print('ENGINES DISAGREE', c['sets'], rate, verdicts); bad += 1
            if rate == 0.0 and not all(verdicts.values()): print('FULL CERTIFICATE REJECTED', c['sets']); bad += 1
            for e, (ok, msg) in res.items():
                if ok: continue
                if e == 'dfs': continue                          # the dfs engine reports no profile
                prof = [tuple(map(int, t)) for t in re.findall(r'\(([\d, ]+)\)', msg)]
                prof = [tuple(int(x) for x in t.split(',')) if isinstance(t, str) else t for t in
                        re.findall(r'\(([\d, ]+)\)', msg)]
                prof = [tuple(int(x) for x in t.split(',')) for t in re.findall(r'\(([\d, ]+)\)', msg)]
                if len(prof) != c['n'] or any(cegar.efx0_raw(c['sets'], prof, a, c['n']) for a in A):
                    print('REPORTED PROFILE IS COVERED', e, c['sets'], prof); bad += 1
            rejected += not verdicts[engines[0]]
        print(f"  core {c.get('name', c['sets'])}: ok", flush=True)
    print(f'{total} trials, {rejected} thinned certificates rejected, {bad} problems', flush=True)
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
