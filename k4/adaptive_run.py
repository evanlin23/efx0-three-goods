"""Driver for k4/adaptive.c (k4/adaptive.md): LB4r with an adaptive insertion rule, on every strict profile of every core
of the given certificate files (results/k4_certs_*.json.gz; core lists loaded as in k4/check4.py), in parallel over
cores; or on single profiles (--profiles=FILE, one JSON object {"sets": [...], "vals": [...]} per line, or the tagged
lines of the logs of k4/gm4_*.py / k4/adaptive_*.py: "... sets=[[..]] vals=[[..]] ...").
Usage: adaptive_run.py FILE [FILE ...] [--jobs=J] [--show=N] [--m=M] [--n4=K] [--first=N] [C options: -A2 -r2 -S100 ...]
       adaptive_run.py --profiles=FILE [C options]
Sums the per-core result lines: total profiles (or runs), fails, and the histogram (rotations 0 .. R) of the fewest rotations LB4r needs
on the rule's insertion sequence (over the three upgrade policies), and prints every FAIL line (up to --show)."""
import gzip, hashlib, json, os, re, subprocess, sys, tempfile, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check4

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, 'adaptive.c')
SHA = hashlib.sha256(open(SRC, 'rb').read()).hexdigest()[:16]
BIN = os.environ.get('ADAPTIVE_BIN') or os.path.join(tempfile.gettempdir(), 'k4_adaptive_' + SHA)

def build():
    if not os.path.exists(BIN):
        tmp = BIN + f'.tmp{os.getpid()}'
        subprocess.run(['gcc', '-O2', '-o', tmp, SRC], check=True, stderr=subprocess.DEVNULL)
        os.replace(tmp, BIN)

def encode_core(sets, m):
    doms = check4.core_domains(sets, m, False)
    out = [f"{len(sets)} {m}"]
    for S, dom in zip(sets, doms):
        out.append(f"{len(S)} {' '.join(map(str, S))} {len(dom)}")
        out += [' '.join(str(v[g]) for g in S) for v in dom]
    return '\n'.join(out) + '\n'

def encode_profile(sets, vals):
    m = 1 + max(g for S in sets for g in S)
    out = [f"{len(sets)} {m}"]
    for S, V in zip(sets, vals):
        out.append(f"{len(S)} {' '.join(map(str, S))} 1"); out.append(' '.join(map(str, V)))
    return '\n'.join(out) + '\n'

def run(task):
    inp, opts, k = task
    p = subprocess.run([BIN] + opts, input=inp, capture_output=True, text=True)
    if p.returncode: raise RuntimeError(p.stdout[-1000:] + p.stderr[-2000:])
    lines = p.stdout.strip().split('\n')
    res = [l for l in lines if l.startswith('total ') or l.startswith('single ') or l.startswith('MINE ')]
    other = [l for l in lines if not (l.startswith('total ') or l.startswith('single ') or l.startswith('MINE '))]
    if len(res) != k: raise RuntimeError(f"{len(res)} result lines for {k} inputs")
    return res, other

def parse(line):
    """'total T leaves L runs R fails F rawfails W rot r0 r1 .. pol p0 p1 p2 [uncov U covviol V covchk C]' -> dict"""
    t = line.split(); d = {}
    d['total'] = int(t[1]); d['fails'] = int(t[7]); d['rawfails'] = int(t[9])
    i = t.index('rot'); j = t.index('pol')
    d['rot'] = list(map(int, t[i + 1:j])); d['pol'] = list(map(int, t[j + 1:j + 4]))
    d['uncov'] = int(t[t.index('uncov') + 1]) if 'uncov' in t else 0
    d['covviol'] = int(t[t.index('covviol') + 1]) if 'covviol' in t else 0
    d['covchk'] = int(t[t.index('covchk') + 1]) if 'covchk' in t else 0
    return d

def load_profiles(path):
    out = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith('#'): continue
        if line.startswith('{'):
            o = json.loads(line); out.append((o['sets'], o['vals'])); continue
        if ' # m=' in line and 'sets=' in line and 'vals=' not in line:   # k4/gm4_*.py lines: TAG v0 v1 .. | .. # m= sets=
            body, meta = line.split(' # ')
            vals = [list(map(int, t.split(','))) for t in body.split(' | ')[0].split()[1:]]
            out.append((json.loads(meta.split('sets=')[1]), vals)); continue
        ms = re.search(r'sets=(\[\[.*?\]\])', line); mv = re.search(r'vals=(\[\[.*?\]\])', line)
        if ms and mv: out.append((json.loads(ms.group(1)), json.loads(mv.group(1))))
    return out

def main():
    args = sys.argv[1:]
    files = [a for a in args if not a.startswith('-')]
    jobs = int(next((a.split('=')[1] for a in args if a.startswith('--jobs=')), os.cpu_count()))
    show = int(next((a.split('=')[1] for a in args if a.startswith('--show=')), 20))
    monly = next((int(a.split('=')[1]) for a in args if a.startswith('--m=')), None)
    n4 = next((int(a.split('=')[1]) for a in args if a.startswith('--n4=')), None)
    first = next((int(a.split('=')[1]) for a in args if a.startswith('--first=')), None)
    prof = next((a.split('=', 1)[1] for a in args if a.startswith('--profiles=')), None)
    opts = [a for a in args if a.startswith('-') and not a.startswith('--')]
    build()
    print('#', 'adaptive_run.py', ' '.join(args), '# adaptive.c sha256', SHA, flush=True)
    if prof:
        P = load_profiles(prof)
        t0 = time.time()
        tasks = [(encode_profile(s, v), opts + (['-T1'] if '-M' not in opts and not any(o.startswith('-T') for o in opts) else []), 1) for s, v in P]
        hist = {}; nfail = 0; shown = 0
        with Pool(jobs) as pool:
            for (res, other), (s, v) in zip(pool.imap(run, tasks), P):
                for l in other:
                    if l.startswith('RUN fail') or l.startswith('RAWFAIL') or '-v' in opts:
                        if shown < show: print(l); shown += 1
                line = res[0]
                if line.startswith('MINE'):
                    print(line, '#', json.dumps(s), json.dumps(v)); continue
                for tok in line.split()[3:]:
                    k, x = tok.split('='); hist[k] = hist.get(k, 0) + int(x)
        print(f"{prof}: profiles={len(P)}", ' '.join(f"{k}={v}" for k, v in hist.items()), f"time {time.time() - t0:.0f}s", flush=True)
        return
    grand = None
    for f in files:
        t0 = time.time()
        data = json.load(gzip.open(f, 'rt'))
        cores = [c for c in data['cores'] if (monly is None or c['m'] == monly)
                 and (n4 is None or sum(len(S) == 4 for S in c['sets']) == n4)]
        if first: cores = cores[:first]
        chunk = max(1, min(8, len(cores) // (4 * jobs) or 1))
        tasks = [(''.join(encode_core(c['sets'], c['m']) for c in cores[i:i + chunk]), opts, len(cores[i:i + chunk]))
                 for i in range(0, len(cores), chunk)]
        tot = None; shown = 0; badcores = 0
        with Pool(jobs) as pool:
            for res, other in pool.imap_unordered(run, tasks):
                for l in other:
                    if shown < show and (l.startswith('FAIL') or l.startswith('RAWFAIL') or l.startswith('HARD') or l.startswith('DEEP') or l.startswith('UNCOV') or 'VIOL' in l):
                        print(l); shown += 1
                for line in res:
                    d = parse(line)
                    if d['fails'] or d['rawfails']: badcores += 1
                    if tot is None: tot = d
                    else:
                        for k in ('total', 'fails', 'rawfails', 'uncov', 'covviol', 'covchk'): tot[k] += d[k]
                        tot['rot'] = [a + b for a, b in zip(tot['rot'], d['rot'])]
                        tot['pol'] = [a + b for a, b in zip(tot['pol'], d['pol'])]
        chk = f" covchk={tot['covchk']}" if tot['covchk'] else ''
        print(f"{os.path.basename(f)}{'' if n4 is None else f' n4={n4}'}{'' if monly is None else f' m={monly}'}: cores={len(cores)} "
              f"total={tot['total']} fails={tot['fails']} rawfails={tot['rawfails']} badcores={badcores} "
              f"rot={tot['rot']} (rotations 0..R) pol={tot['pol']} uncov={tot['uncov']} covviol={tot['covviol']}{chk} time {time.time() - t0:.0f}s", flush=True)

if __name__ == '__main__':
    main()
