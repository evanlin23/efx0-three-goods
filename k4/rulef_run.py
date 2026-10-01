"""Driver for k4/rulef.c (k4/rulef.md): rule F data and explicit first-agent rules on every strict profile of every core
of the given certificate files (core lists loaded as in k4/check4.py), or on random profiles (-SN), or on single
profiles (--profiles=FILE, as k4/adaptive_run.py).

Usage: rulef_run.py FILE [FILE ...] [--jobs=J] [--n4=K] [--m=M] [--first=N] [--data=OUT] [C options]
  default C options: -A40 -C3 -r1 (every first agent: fewest rotations up to one, coverage with A4+N, deficits)
  --data=OUT  append the DATA lines of k4/rulef.c (-D1: the profiles where no first agent's run is covered;
              -D2: those needing a rotation under every first agent) to OUT
Prints, per file, the RULEF line summed over cores: total profiles, profiles with no covered first-agent run
('allunc'), the histogram of rule F's fewest rotations (0, 1, fails with one), the same on allunc, and per explicit rule
(k4/rulef.c rulef_rules, index 0..NRULES-1): 'rel' = profiles where the rule's first agent needs more rotations than
rule F's, 'abs' = profiles where it fails with at most one rotation; 'urel', 'uabs' the same on allunc.
One worker by default (--jobs=1): the machine is shared."""
import gzip, hashlib, json, os, subprocess, sys, tempfile, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_run as AR

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, 'rulef.c')
SHA = hashlib.sha256(open(SRC, 'rb').read()).hexdigest()[:16]
BIN = os.environ.get('RULEF_BIN') or os.path.join(tempfile.gettempdir(), 'k4_rulef_' + SHA)
RULES = ['index', 'F', 'firstcov', 'minA4N', 'minA4o', 'minA4+', 'minHN', 'minH', 'cov|minH', 'minomegaN',
         'minH,frz', '4good', 'minHN,e4', 'minUN', 'minU', 'cov|minU']


def build():
    if not os.path.exists(BIN):
        tmp = BIN + f'.tmp{os.getpid()}'
        subprocess.run(['gcc', '-O2', '-o', tmp, SRC], check=True)
        os.replace(tmp, BIN)


def run(task):
    inp, opts, k = task
    p = subprocess.run([BIN] + opts, input=inp, capture_output=True, text=True)
    if p.returncode: raise RuntimeError(p.stdout[-1000:] + p.stderr[-2000:])
    lines = p.stdout.strip().split('\n')
    rf = [l for l in lines if l.startswith('RULEF ')]
    tot = [l for l in lines if l.startswith('total ') or l.startswith('single ')]
    data = [l for l in lines if l.startswith('DATA ')]
    other = [l for l in lines if not (l.startswith('RULEF ') or l.startswith('total ') or l.startswith('DATA ') or l.startswith('single '))]
    return rf, tot, data, other


def parse_rf(line):
    t = line.split()
    d = {'total': int(t[2]), 'allunc': int(t[4])}
    keys = ['min', 'umin', 'rel', 'urel', 'abs', 'uabs']
    idx = {k: t.index(k) for k in keys}
    order = sorted(keys, key=lambda k: idx[k])
    for a, k in enumerate(order):
        end = idx[order[a + 1]] if a + 1 < len(order) else len(t)
        d[k] = list(map(int, t[idx[k] + 1:end]))
    return d


def add(a, b):
    if a is None: return b
    for k in b:
        a[k] = a[k] + b[k] if isinstance(b[k], int) else [x + y for x, y in zip(a[k], b[k])]
    return a


def main():
    args = sys.argv[1:]
    files = [a for a in args if not a.startswith('-')]
    jobs = int(next((a.split('=')[1] for a in args if a.startswith('--jobs=')), 1))
    monly = next((int(a.split('=')[1]) for a in args if a.startswith('--m=')), None)
    n4 = next((int(a.split('=')[1]) for a in args if a.startswith('--n4=')), None)
    first = next((int(a.split('=')[1]) for a in args if a.startswith('--first=')), None)
    out = next((a.split('=', 1)[1] for a in args if a.startswith('--data=')), None)
    prof = next((a.split('=', 1)[1] for a in args if a.startswith('--profiles=')), None)
    opts = [a for a in args if a.startswith('-') and not a.startswith('--')] or ['-A40', '-C3', '-r1']
    build()
    print('#', 'rulef_run.py', ' '.join(args), '# rulef.c sha256', SHA, flush=True)
    print('# rules:', ' '.join(f'{i}={r}' for i, r in enumerate(RULES)), flush=True)
    fo = open(out, 'a') if out else None
    if prof:
        P = AR.load_profiles(prof)
        tasks = [(AR.encode_profile(s, v), opts + ['-T1'], 1) for s, v in P]
        tot = None
        with Pool(jobs) as pool:
            for rf, tl, data, other in pool.imap(run, tasks):
                for l in other: print(l)
                if fo:
                    for l in data: fo.write(l + '\n')
                for l in rf: tot = add(tot, parse_rf(l))
        print(f"{prof}: profiles={len(P)} RULEF {json.dumps(tot)}", flush=True)
        return
    for f in files:
        t0 = time.time()
        data_ = json.load(gzip.open(f, 'rt'))
        cores = [c for c in data_['cores'] if (monly is None or c['m'] == monly)
                 and (n4 is None or sum(len(S) == 4 for S in c['sets']) == n4)]
        if first: cores = cores[:first]
        tasks = [(AR.encode_core(c['sets'], c['m']), opts, 1) for c in cores]
        tot = None; fails = 0; shown = 0
        with Pool(jobs) as pool:
            for rf, tl, data, other in pool.imap_unordered(run, tasks):
                for l in other:
                    if shown < 20 and (l.startswith('FAIL') or 'VIOL' in l or l.startswith('RAWFAIL')): print(l); shown += 1
                if fo:
                    for l in data: fo.write(l + '\n')
                for l in rf: tot = add(tot, parse_rf(l))
                for l in tl: fails += AR.parse(l)['fails']
        lab = os.path.basename(f) + ('' if n4 is None else f' n4={n4}') + ('' if monly is None else f' m={monly}')
        print(f"{lab}: cores={len(cores)} fails(rule -Q)={fails} time {time.time() - t0:.0f}s", flush=True)
        if tot:
            print(f"  total={tot['total']} allunc={tot['allunc']} ruleF min-rotations={tot['min']} on allunc={tot['umin']}")
            for i in range(len(RULES)):
                print(f"  rule {i:2d} {RULES[i]:12s} worse-than-F={tot['rel'][i]:>12d} fails-with-<=1={tot['abs'][i]:>12d}"
                      f"   on allunc: worse={tot['urel'][i]:>10d} fails={tot['uabs'][i]:>10d}")
        sys.stdout.flush()
    if fo: fo.close()


if __name__ == '__main__':
    main()
