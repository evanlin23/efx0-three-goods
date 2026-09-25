"""k4/c4check.c -X (the checks of k4/c4.md §2-§4c) on single profiles, for every insertion sequence: the hard test set of
#30 (k4/gm4.md): the 148 profiles of results/k4_gm4_gmall_seeds_4.txt (pure n = 4) and the instances of
k4/gm4_counterexample.py. Sums the C4CHK counters (weighted by insertion sequences) and prints every violation line.
Usage: python3 k4/c4check_profiles.py"""
import os, re, subprocess, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import c4check_run, gm4_counterexample

def profiles():
    for line in open(os.path.join(HERE, '..', 'results', 'k4_gm4_gmall_seeds_4.txt')):
        if not line.startswith('GMALL'): continue
        vals = [list(map(int, v.split(','))) for v in line.split('|')[0].split()[1:]]
        m = int(re.search(r'm=(\d+)', line).group(1)); sets = json.loads(re.search(r'sets=(\[\[.*?\]\])', line).group(1))
        yield 'GMALL seed', m, sets, vals
    for label, V, _, _ in gm4_counterexample.INSTANCES:
        sets = [sorted(d) for d in V]; vals = [[d[g] for g in S] for d, S in zip(V, sets)]
        yield label.split(':')[0], 1 + max(max(S) for S in sets), sets, vals

def main():
    c4check_run.build()
    tot = {}; viol = []; runs = 0; count = {}
    for name, m, sets, vals in profiles():
        inp = f"{len(sets)} {m}\n" + ''.join(f"{len(S)} {' '.join(map(str, S))} 1\n{' '.join(map(str, v))}\n"
                                             for S, v in zip(sets, vals))
        p = subprocess.run([c4check_run.BIN] + c4check_run.OPTS, input=inp, capture_output=True, text=True, check=True)
        count[name] = count.get(name, 0) + 1
        for line in p.stderr.split('\n'):
            if line.startswith('C4CHK'):
                for kv in line.split()[1:]:
                    k, v = kv.split('='); tot[k] = tot.get(k, 0) + int(v)
            elif line.startswith('FAIL'): tot['construction_fails_lines'] = tot.get('construction_fails_lines', 0) + 1
            elif line.strip(): viol.append(line)
        runs += int(p.stdout.split()[1])
    print('# c4check_profiles.py options', ' '.join(c4check_run.OPTS))
    print('profiles:', ', '.join(f'{k} ({v})' for k, v in count.items()))
    print(f'{runs} (run, profile) pairs')
    print('  ' + ' '.join(f"{k}={v}" for k, v in tot.items()))
    print(f"  violation lines (every report other than FAIL): {len(viol)}")
    for l in viol[:10]: print('   ', l)

if __name__ == '__main__':
    main()
