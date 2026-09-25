"""Driver for k4/gap.c (compute/k4-gap; k4/gap.md): the profiles in the exposed-frozen gap of conjecture C4min.

  python3 k4/gap_run.py FILE ... [--sample=P] [--seed=S] [-D] [--rec=R] [--jobs=J] [--out=CATALOG.json.gz]

FILE: certificate files results/k4_certs_*.json.gz (their core lists). Every strict profile of every core
(check4.core_domains: one integer representative per strict balanced type), or P random ones per core (--sample).
-D: also the removal-only deficit of every min-frozen pre-allocation, compared with the configuration test.
--rec=R: keep the record of every gap profile whose index is 0 mod R, and of every hard one (R = 0: hard ones only;
default 1: every gap profile). --out: write the kept records, with the core and the values, as gzip JSON.
Prints the counters of gap.c per file (their meaning: k4/gap.md) and the command. EVIDENCE only."""
import gzip, hashlib, json, os, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4

SRC = os.path.join(HERE, 'gap.c')
SHA = hashlib.sha256(open(SRC, 'rb').read()).hexdigest()
BIN = os.path.join(tempfile.gettempdir(), 'k4_gap_' + SHA[:16])
KEYS = ('prof om1 Z small F gap gap_f1 gap_f2 catS catW catN catX defmis defover trunc cfg cfg_compl cfg_simple max '
        'max_thr2 max_notpo max_tpos h7all_G h7all_G1 h7all_L h7all_O h7max_G h7max_G1 h7max_L h7max_O exp3 exp4 expbt '
        'keys thr2prof').split()

def build():
    if not os.path.exists(BIN):
        subprocess.run(['gcc', '-O2', '-o', BIN + '.tmp', SRC], check=True)
        os.replace(BIN + '.tmp', BIN)

def block(sets, m, doms, tag, P, profs=None):
    out = [f"{len(sets)} {m} {tag}"]
    out += [f"{len(S)} {' '.join(map(str, S))}" for S in sets]
    out.append(' '.join(str(len(D)) for D in doms))
    for S, D in zip(sets, doms):
        out += [' '.join(str(d[g]) for g in S) for d in D]
    if profs is None: out.append(str(P))
    else: out.append(str(-len(profs))); out += [' '.join(map(str, p)) for p in profs]
    return '\n'.join(out) + '\n'

def parse_K(line):
    w = line.split()
    vals = [int(x) for x in w[2:] if x.lstrip('-').isdigit()]
    return dict(zip(KEYS, vals))

def run_core(task):
    tag, sets, m, P, opts = task
    doms = check4.core_domains(sets, m, False)
    r = subprocess.run([BIN] + opts, input=block(sets, m, doms, tag, P), capture_output=True, text=True)
    if r.returncode: raise RuntimeError(r.stderr)
    K, recs = None, []
    for l in r.stdout.splitlines():
        if l.startswith('K '): K = parse_K(l)
        elif l.startswith('R '):
            d = json.loads(l[2:])
            d['vals'] = [[D[p][g] for g in S] for S, D, p in zip(sets, doms, d['prof'])]
            recs.append(d)
    return tag, K, recs

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    print("command: python3 k4/gap_run.py " + ' '.join(sys.argv[1:]), flush=True)
    print(f"gap.c sha256 {SHA}", flush=True)
    build()
    P, seed, rec = int(opt.get('sample', 0)), int(opt.get('seed', 1)), int(opt.get('rec', 1))
    copts = [f'-S{seed}', f'-r{rec}'] + (['-D'] if '-D' in sys.argv[1:] else [])
    allrecs = []
    for f in args:
        t0 = time.time()
        d = json.load(gzip.open(f, 'rt'))
        cores = d['cores']
        tasks = [(k, c['sets'], c['m'], P, copts) for k, c in enumerate(cores)]
        tot = dict.fromkeys(KEYS, 0)
        with Pool(int(opt.get('jobs', os.cpu_count()))) as pool:
            for tag, K, recs in pool.imap_unordered(run_core, tasks):
                for k in KEYS: tot[k] += K[k]
                for r in recs:
                    c = cores[tag]
                    r['core'] = {'file': os.path.basename(f), 'idx': c.get('idx', tag), 'pos': tag, 'm': c['m'], 'sets': c['sets']}
                    allrecs.append(r)
        print(f"{os.path.basename(f)}: {len(cores)} cores, {'every profile' if not P else f'{P} random profiles per core'} "
              f"[{time.time() - t0:.0f} s]", flush=True)
        print('  ' + ' '.join(f"{k}={tot[k]}" for k in KEYS), flush=True)
    if 'out' in opt:
        allrecs.sort(key=lambda r: (len(r['core']['sets']), r['core']['m'], r['core']['file'], r['core']['pos'], r['prof']))
        with gzip.open(opt['out'], 'wt') as fo:
            json.dump({'command': 'python3 k4/gap_run.py ' + ' '.join(sys.argv[1:]), 'gap_c_sha256': SHA,
                       'records': allrecs}, fo, separators=(',', ':'))
        print(f"wrote {len(allrecs)} records to {opt['out']}", flush=True)

if __name__ == '__main__':
    main()
