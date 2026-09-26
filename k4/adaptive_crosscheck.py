"""Cross-check of the coverage predicate of k4/adaptive.c (rules 20-22, a port of #37's checks) against k4/c4check.c of
branch proof/k4-c4one, compiled separately (its path in C4CHECK_BIN; this script never builds it): for every strict
profile of every core of the given certificate files, the number of profiles on which no insertion sequence of the
family has a run covered by the theorems. c4check.c: -X -P2 -u2 -o0 -r1 -w0 -c0 with -i2 (every sequence) or -i6
(index, or one step changed); k4/adaptive.c: -A22 or -A20 with -u2 -r1 -w0 -c0 (its 'uncov' count).
Usage: C4CHECK_BIN=PATH adaptive_crosscheck.py FILE [FILE ...] [--jobs=J] [--n4=K]"""
import gzip, json, os, subprocess, sys
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_run as A

C4 = os.environ.get('C4CHECK_BIN')

def run(task):
    recs, which = task
    inp = ''.join(A.encode_core(c['sets'], c['m']) for c in recs)
    if which in ('-i2', '-i6'):
        p = subprocess.run([C4, '-X', '-P2', '-u2', '-o0', '-r1', '-w0', '-c0', which], input=inp, capture_output=True, text=True)
        return sum(int(l.split()[7]) for l in p.stdout.strip().split('\n'))
    p = subprocess.run([A.BIN, which, '-u2', '-r1', '-w0', '-c0'], input=inp, capture_output=True, text=True)
    return sum(A.parse(l)['uncov'] for l in p.stdout.strip().split('\n') if l.startswith('total'))

def main():
    args = sys.argv[1:]
    files = [a for a in args if not a.startswith('--')]
    jobs = int(next((a.split('=')[1] for a in args if a.startswith('--jobs=')), os.cpu_count()))
    n4 = next((int(a.split('=')[1]) for a in args if a.startswith('--n4=')), None)
    if not C4: raise SystemExit('set C4CHECK_BIN')
    A.build()
    print('# adaptive_crosscheck.py', ' '.join(args), '# adaptive.c sha256', A.SHA, flush=True)
    for f in files:
        cores = [c for c in json.load(gzip.open(f, 'rt'))['cores'] if n4 is None or sum(len(s) == 4 for s in c['sets']) == n4]
        res = {}
        with Pool(jobs) as pool:
            for which in ('-i2', '-A22', '-i6', '-A20'):
                res[which] = sum(pool.map(run, [([c], which) for c in cores]))
        print(f"{f}: cores={len(cores)} uncovered by every sequence: c4check {res['-i2']} adaptive {res['-A22']}; "
              f"by index or one change: c4check {res['-i6']} adaptive {res['-A20']}", flush=True)

if __name__ == '__main__':
    main()
