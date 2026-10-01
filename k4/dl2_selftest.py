"""Self-test of k4/dl2.c's build variants (compute/k4-dl2): 32- and 64-bit masks (-DWIDE), and the hashed neighbour
search forced on every class (-DBIGPP=5) against the plain scan. Input: every complete suite instance with n <= 9
(H_2 included) and seeded random profiles of seven cores (three n = 3 cores with k* = 3 profiles among them). The four
outputs (-w -r1: every P, every record, the T/A tables) must be identical. Exit status nonzero otherwise.
  python3 k4/dl2_selftest.py"""
import sys, json, glob, gzip, subprocess, tempfile, time, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
os.chdir(os.path.join(HERE, '..'))
import dl2_run as DR, check4

print('# command: python3 k4/dl2_selftest.py', flush=True)
print(f'# dl2.c sha256 {DR.SHA}', flush=True)
src = DR.SRC
SP = tempfile.mkdtemp() + '/'
variants = {'n': [], 'h': ['-DBIGPP=5'], 'w': ['-DWIDE'], 'wh': ['-DWIDE', '-DBIGPP=5']}
for k, fl in variants.items():
    subprocess.run(['gcc', '-O2', '-Wall', '-Wextra'] + fl + ['-o', SP + 'eq_' + k, src], check=True)

out = []; k = 0
for fn in sorted(glob.glob('k4/suite/instances/*.json')):
    d = json.load(open(fn))
    if 'kind' in d or len(d['sets']) > int(os.environ.get('MAXN', 9)): continue
    doms = [[dict(zip(S, V))] for S, V in zip(d['sets'], d['vals'])]
    out.append(DR.block(d['sets'], d['m'], doms, k, 0)); k += 1
for f, ks, P in [('results/k4_certs_3.json.gz', [44, 49, 50, 28], 300), ('results/k4_certs_4_pure.json.gz', [100, 183, 210], 100),
                 ('results/k4_certs_4_n4_2.json.gz', [306, 12], 200)]:
    cores = json.load(gzip.open(f, 'rt'))['cores']
    for c in ks:
        C = cores[c]; doms = check4.core_domains(C['sets'], C['m'], False)
        out.append(DR.block(C['sets'], C['m'], doms, k, P)); k += 1
inp = ''.join(out)
print(k, 'blocks')


def norm(txt):
    res, blk = [], []
    for l in txt.splitlines():
        if l.startswith('D '):
            d = json.loads(l[2:])
            for P in d['P']:
                if 'avail' in P: P['avail'] = sorted(P['avail'])
            l = 'D ' + json.dumps(d, sort_keys=True)
        if l.startswith('T ') or l.startswith('A '): blk.append(l); continue
        if blk: res += sorted(blk); blk = []
        res.append(l)
    return res + sorted(blk)


outs = {}
for k in variants:
    t0 = time.time()
    r = subprocess.run([SP + 'eq_' + k, '-w', '-r1', '-S3'], input=inp, capture_output=True, text=True, check=True)
    outs[k] = norm(r.stdout)
    print(k, f'{time.time() - t0:.1f} s', len(outs[k]), 'lines')
bad = 0
for k in ['h', 'w', 'wh']:
    same = outs[k] == outs['n']; bad += not same
    print(k, 'identical to n' if same else 'DIFFERENT')
    if not same:
        for i, (p, q) in enumerate(zip(outs['n'], outs[k])):
            if p != q: print('  first diff', i, '\n  ', p[:300], '\n  ', q[:300]); break
K = [l for l in outs['n'] if l.startswith('K ')]
tot = {}
for l in K:
    w = l.split()
    for a, b in zip(w[2::2], w[3::2]): tot[a] = tot.get(a, 0) + int(b)
print({a: tot[a] for a in ['prof', 'om1', 'kstar0', 'kstar1', 'kstar2', 'kstar3', 'kstar4', 'kstarinf', 'kstarn', 'kiso', 'ktrap', 'piso', 'ptrap']})
sys.exit(1 if bad else 0)
