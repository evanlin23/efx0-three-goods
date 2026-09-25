"""Driver for k4/c4check.c (-X): check Theorems A4, B4, B4w, A4T and A4+ of k4/c4.md on every strict profile of every
core in the given certificate files (only the core lists are used), for every insertion sequence (-i1), with envy-free
upgrades (-u2). Sums the per-core C4CHK counters (weighted by profiles) and prints every violation line (any report of
c4check.c other than FAIL, which is LB4r's own failure under these options; there should be none).
Usage: c4check_run.py FILE [FILE ...] [--jobs=J] [--n4=K] (keep only cores with exactly K four-good agents)"""
import gzip, hashlib, json, os, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4, lb4_run
SRC = os.path.join(HERE, 'c4check.c')
BIN = os.environ.get('C4CHECK_BIN') or os.path.join(
    tempfile.gettempdir(), 'k4_c4check_bin_' + hashlib.sha256(open(SRC, 'rb').read()).hexdigest()[:16])
OPTS = ['-X', '-i1', '-u2', '-o0', '-r1', '-w0', '-c0', '-f5']

def build():
    if not os.path.exists(BIN):
        subprocess.run(['gcc', '-O2', '-o', BIN, SRC], check=True, stderr=subprocess.DEVNULL)

def run(recs):
    inp = ''.join(lb4_run.encode(r['sets'], r['m'], False) for r in recs)
    p = subprocess.run([BIN] + OPTS, input=inp, capture_output=True, text=True)
    if p.returncode: raise RuntimeError(p.stderr[-2000:])
    tot = {}; viol = []
    for line in p.stderr.split('\n'):
        if line.startswith('C4CHK'):
            for kv in line.split()[1:]:
                k, v = kv.split('='); tot[k] = tot.get(k, 0) + int(v)
        elif line.startswith('FAIL'): tot['construction_fails_lines'] = tot.get('construction_fails_lines', 0) + 1
        elif line.strip(): viol.append(line)
    runs = sum(int(l.split()[1]) for l in p.stdout.strip().split('\n'))
    return tot, viol, runs

def main():
    args = sys.argv[1:]
    files = [a for a in args if not a.startswith('-')]
    jobs = int(next((a.split('=')[1] for a in args if a.startswith('--jobs=')), os.cpu_count()))
    n4 = next((int(a.split('=')[1]) for a in args if a.startswith('--n4=')), None)
    build()
    print('# c4check_run.py', ' '.join(args), 'options', ' '.join(OPTS), flush=True)
    for f in files:
        t0 = time.time()
        cores = json.load(gzip.open(f, 'rt'))['cores']
        if n4 is not None: cores = [c for c in cores if sum(len(s) == 4 for s in c['sets']) == n4]
        tasks = [cores[i:i + 4] for i in range(0, len(cores), 4)]
        tot = {}; viol = []; runs = 0
        with Pool(jobs) as pool:
            for t, v, ru in pool.imap_unordered(run, tasks):
                for k, x in t.items(): tot[k] = tot.get(k, 0) + x
                viol += v; runs += ru
        print(f"{f}: {len(cores)} cores, {runs} (run, profile) pairs, {time.time() - t0:.0f}s")
        print('  ' + ' '.join(f"{k}={v}" for k, v in tot.items()))
        print(f"  violation lines (every report other than FAIL): {len(viol)}")
        for l in viol[:10]: print('   ', l)
        sys.stdout.flush()

if __name__ == '__main__':
    main()
