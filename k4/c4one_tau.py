"""k4/c4one.md §3: can the insertion sequence be chosen so that the theorems of k4/c4.md prove the run? Runs
k4/c4check.c with -X -P (a run succeeds when those theorems prove it) on every strict profile of every core with exactly
one 4-good agent in the given certificate files, with the given insertion options; prints the profiles with no success.
Usage: python3 k4/c4one_tau.py "OPTIONS" FILE [FILE ...]
  e.g. python3 k4/c4one_tau.py "-X -P -u2 -i2 -o0 -r1 -w0 -c0 -f3" results/k4_certs_3.json.gz   (-Q: q inserted first)"""
import os, sys, gzip, json, subprocess
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import lb4_run, c4check_run
BIN = c4check_run.BIN; opts = sys.argv[1].split(); files = sys.argv[2:]

def run(recs):
    p = subprocess.run([BIN] + opts, input=''.join(lb4_run.encode(c['sets'], c['m'], False) for c in recs), capture_output=True, text=True)
    t = f = 0; bad = 0
    for line in p.stdout.strip().split('\n'):
        w = line.split(); t += int(w[1]); f += int(w[7]); bad += int(w[7]) > 0
    return t, f, bad, [l for l in p.stderr.split('\n') if l.startswith('FAIL')][:2]
def main():
    c4check_run.build()
    print('# c4one_tau.py', ' '.join(opts), flush=True)
    for fn in files:
        cs = [c for c in json.load(gzip.open(fn, 'rt'))['cores'] if sum(len(s) == 4 for s in c['sets']) == 1]
        T = F = B = 0; ex = []
        with Pool(4) as pool:
            for t, f, b, e in pool.imap_unordered(run, [[c] for c in cs]): T += t; F += f; B += b; ex += e
        print(f'{fn}: {len(cs)} cores, total {T}, profiles with no success {F}, cores with one {B}', flush=True)
        for e in ex[:3]: print('   ', e[:300])

if __name__ == '__main__':
    main()
