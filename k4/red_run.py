"""Driver for k4/red.c (k4/c4min_reduce.md): runs it on every core of the given certificate files
(results/k4_certs_*.json.gz; types from k4/check4.py, as every k = 4 tool) and sums the counters.
Usage: red_run.py FILE [FILE ...] [--rand=R] [--seed=S] [--jobs=J] [-x N] [--cores=a:b] [--pots='f,f;f']
  --lil: only the local improvement lemma check (k4/c4min_reduce.md §5.3), counters lil_*; --lil-rfirst uses the
  potential (r', -t, Lambda); --lil-nom2 drops the two-agent re-pairings; --lil-narrow restricts the modified receiver and
  x's pair to Lemma R(iii) / #50 (red.c -Ln), --lil-recycle adds #50's recycling rule (red.c -Lc); --lil-anypx lets x take any pair (red.c -Lx).
  --pots: extra global potentials (features r lamU lamR mt mp mterm lx mvp mndx; lexicographic, maximized).
  --rand=R: R random profiles per core (seed S + core index); default every profile.
  -x N: print up to N example profiles per counter (in core order).
The first output line records the provenance: the sha1 of k4/red.c and the git commit of the checkout."""
import gzip, hashlib, json, os, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from check4 import core_domains

def binary():
    src = os.path.join(HERE, 'red.c')
    h = hashlib.sha1(open(src, 'rb').read()).hexdigest()[:12]
    out = os.environ.get('RED_BIN') or os.path.join(tempfile.gettempdir(), 'red_' + h)
    if not os.path.exists(out):
        subprocess.run(['gcc', '-O2', '-o', out, src], check=True)
    return out

def core_input(n, m, sets, rand, seed):
    doms = core_domains(sets, m, False)
    lines = ['%d %d' % (n, m)]
    for S, D in zip(sets, doms):
        lines.append('%d %s %d' % (len(S), ' '.join(map(str, S)), len(D)))
        for vals in D: lines.append(' '.join(str(vals[g]) for g in S))
    lines.append('%d %d' % (rand, seed))
    return '\n'.join(lines) + '\n'

LIL = '--lil' in sys.argv or '--lil-rfirst' in sys.argv
LILFLAGS = [f for o, f in (('--lil-rfirst', '-Lr'), ('--lil-nom2', '-L2'), ('--lil-narrow', '-Ln'), ('--lil-recycle', '-Lc'), ('--lil-anypx', '-Lx'))
            if o in sys.argv]

def provenance():
    src = os.path.join(HERE, 'red.c')
    h = hashlib.sha1(open(src, 'rb').read()).hexdigest()
    try:
        c = subprocess.run(['git', '-C', HERE, 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
        dirty = subprocess.run(['git', '-C', HERE, 'status', '--porcelain', '--', 'red.c'], capture_output=True, text=True).stdout.strip()
    except OSError:
        c, dirty = 'unknown', ''
    return '# source: k4/red.c sha1 %s; git HEAD %s%s' % (h, c or 'unknown', ' (red.c modified)' if dirty else '')

def run(task):
    b, n, m, sets, rand, seed, nex, tag, pots = task
    p = subprocess.run([b, '-x', str(nex)] + (['-p', pots] if pots else []) + (['-L'] + LILFLAGS if LIL else []), input=core_input(n, m, sets, rand, seed), capture_output=True, text=True, check=True)
    cnt, ex = {}, []
    for line in p.stdout.splitlines():
        if line.startswith('EX '): ex.append('%s %s' % (tag, line[3:])); continue
        k, v = line.split(); cnt[k] = int(v)
    return cnt, ex

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    nex = 0
    if '-x' in sys.argv: nex = int(sys.argv[sys.argv.index('-x') + 1]); args = [a for a in args if a != str(nex)]
    rand = int(opt.get('rand', 0)); seed = int(opt.get('seed', 1)); jobs = int(opt.get('jobs', os.cpu_count()))
    print(provenance(), flush=True)
    b = binary(); tasks = []
    for f in args:
        data = json.load(gzip.open(f, 'rt'))
        cores = data['cores']
        lo, hi = 0, len(cores)
        if 'cores' in opt: lo, hi = map(int, opt['cores'].split(':'))
        for ci in range(lo, min(hi, len(cores))):
            c = cores[ci]
            tasks.append((b, c['n'], c['m'], c['sets'], rand, seed + ci, nex, '%s#%d' % (os.path.basename(f), ci), opt.get('pots', '')))
    tot = {}; t0 = time.time(); shown = {}
    with Pool(jobs) as pool:
        for cnt, ex in pool.imap(run, tasks):
            for k, v in cnt.items(): tot[k] = tot.get(k, 0) + v
            for e in ex:
                tag = e.split()[1]
                if shown.get(tag, 0) < nex: shown[tag] = shown.get(tag, 0) + 1; print(e)
    print('# files: %s  rand=%d seed=%d  cores=%d  time=%.1fs' % (' '.join(args), rand, seed, len(tasks), time.time() - t0))
    for k in sorted(tot): print('%-36s %d' % (k, tot[k]))
    fails = {k: v for k, v in tot.items() if k.startswith('FAIL') and v}
    print('# failures:', fails if fails else 'none')

if __name__ == '__main__':
    main()
