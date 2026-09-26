"""The (k, p) = (4, 3) class: k = 4 cores in which every good is valued by at most 3 agents (compute/k4-nsw; k4/nsw.md).
Bounded LB4r with index insertion (k4/lb4.md section 5: -i0 -u3 -r3 -w1 -c1), EVIDENCE only.

  filter FILE ... --out=DIR   write DIR/<name>_p3.json.gz: the cores of each certificate file with every good of degree
                              <= 3 (core lists only; run k4/lb4_run.py on them for every strict profile)
  sample FILE ... --profiles=P [--seed=S] [--jobs=J]
                              for every core of the files with every good of degree <= 3, P random strict profiles, run
                              as in random mode below (least R = 0..3 per profile)
  random --n=6,7 --cores=C --profiles=P [--seed=S] [--p4=0.5] [--maxpriv=2] [--jobs=J]
                              random (4, 3) cores (every shared good has degree 2 or 3; agents of degree 3 or 4 with at
                              most d - 2 private goods; connected; checked by check4.is_core), P random strict profiles
                              each; LB4r with index insertion and at most R nested rotations for R = 0, 1, 2, 3 on each
                              profile (k4/lb4_nsw.c without -N, i.e. k4/c4_lb4w.c: 64-bit masks, up to 32 agents); counts
                              the least R that works (a failure at R = 3 is LB4r failing) and prints failing profiles.
Usage: see above."""
import gzip, hashlib, json, os, random, re, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4

SRC = os.path.join(HERE, 'lb4_nsw.c')
BIN = os.path.join(tempfile.gettempdir(), 'k4_lb4_nsw_' + hashlib.sha256(open(SRC, 'rb').read()).hexdigest()[:16])
OPTS = ['-i0', '-u3', '-w1', '-c1']

def pmax(sets, m):
    return max(sum(g in S for S in sets) for g in range(m))

def do_filter(files, out):
    os.makedirs(out, exist_ok=True)
    for f in files:
        d = json.load(gzip.open(f, 'rt'))
        keep = [r for r in d['cores'] if pmax(r['sets'], r['m']) <= 3]
        o = dict(d); o['cores'] = [{'m': r['m'], 'idx': r.get('idx', 0), 'sets': r['sets'], 'allocs': []} for r in keep]
        name = os.path.basename(f).replace('.json.gz', '_p3.json.gz')
        with gzip.open(os.path.join(out, name), 'wt') as fo: json.dump(o, fo)
        print(f"{os.path.basename(f)}: {len(d['cores'])} cores, every good of degree <= 3: {len(keep)} -> {name}", flush=True)

MAXPRIV = 2
def random_core43(rng, n, p4, tries=20000):
    for _ in range(tries):
        d = [4 if rng.random() < p4 else 3 for _ in range(n)]
        if 4 not in d: d[rng.randrange(n)] = 4
        p = [rng.randrange(min(di - 2, MAXPRIV) + 1) for di in d]   # 0 .. min(d - 2, --maxpriv) private goods
        slots = sum(di - pi for di, pi in zip(d, p))
        lo, hi = -(-slots // 3), slots // 2                 # shared goods ms with 2 ms <= slots <= 3 ms
        if lo > hi: continue
        ms = rng.randint(lo, hi)
        three = rng.sample(range(ms), slots - 2 * ms)       # these get a third valuer
        pool = [g for g in range(ms) for _ in range(2 + (g in three))]
        rng.shuffle(pool)
        sets, k, nxt, ok = [], 0, ms, True
        for i in range(n):
            S = pool[k:k + d[i] - p[i]]; k += d[i] - p[i]
            if len(set(S)) != len(S): ok = False; break
            sets.append(sorted(S + list(range(nxt, nxt + p[i])))); nxt += p[i]
        if not ok: continue
        m = nxt
        if check4.is_core(n, m, sets, all(x == 4 for x in d))[0] and pmax(sets, m) <= 3: return m, sets
    return None

def encode_profile(sets, m, vals):
    out = [f"{len(sets)} {m}"]
    for S, v in zip(sets, vals):
        out.append(f"{len(S)} {' '.join(map(str, S))} 1")
        out.append(' '.join(str(v[g]) for g in S))
    return '\n'.join(out) + '\n'

def run_random(task):
    n, p4, seed, P = task[:4]
    rng = random.Random(seed)
    rc = task[4] if len(task) > 4 else random_core43(rng, n, p4)
    if rc is None: return None
    m, sets = rc
    doms = check4.core_domains(sets, m, False)
    profs = [[rng.choice(D) for D in doms] for _ in range(P)]
    inp = ''.join(encode_profile(sets, m, v) for v in profs)
    fails = {}
    for R in range(4):
        r = subprocess.run([BIN] + OPTS + [f'-r{R}', '-b', '-f0'], input=inp, capture_output=True, text=True)
        fails[R] = [int(re.search(r' fails (\d+)', l).group(1)) for l in r.stdout.splitlines() if l.startswith('total')]
        raw = sum(int(re.search(r' rawfails (\d+)', l).group(1)) for l in r.stdout.splitlines() if l.startswith('total'))
        if raw: fails['raw'] = raw
    least = [next((R for R in range(4) if not fails[R][k]), 4) for k in range(P)]
    bad = [(sets, m, [[v[g] for g in S] for S, v in zip(sets, profs[k])]) for k in range(P) if least[k] == 4]
    return {'n': n, 'm': m, 'sets': sets, 'least': [least.count(R) for R in range(5)], 'raw': fails.get('raw', 0), 'bad': bad[:3]}

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    print("command: python3 k4/p3_run.py " + ' '.join(sys.argv[1:]), flush=True)
    if args[0] == 'filter': return do_filter(args[1:], opt['out'])
    global MAXPRIV
    MAXPRIV = int(opt.get('maxpriv', 2))
    if not os.path.exists(BIN): subprocess.run(['gcc', '-O2', '-o', BIN, SRC], check=True, stderr=subprocess.DEVNULL)
    print(f"binary: {BIN} (sha256 of k4/lb4_nsw.c: {hashlib.sha256(open(SRC, 'rb').read()).hexdigest()}), options {' '.join(OPTS)} -rR -b", flush=True)
    ns = [int(x) for x in opt.get('n', '6').split(',')]
    C, P, seed, p4 = int(opt.get('cores', 50)), int(opt.get('profiles', 200)), int(opt.get('seed', 1)), float(opt.get('p4', 0.5))
    t0 = time.time()
    groups = []
    if args[0] == 'sample':
        for f in args[1:]:
            d = json.load(gzip.open(f, 'rt'))
            cs = [r for r in d['cores'] if pmax(r['sets'], r['m']) <= 3]
            groups.append((os.path.basename(f), d['n'], [(d['n'], p4, seed * 1000003 + k, P, (r['m'], r['sets'])) for k, r in enumerate(cs)]))
    else:
        for n in ns: groups.append((f"random n={n}", n, [(n, p4, seed * 1000003 + n * 10007 + k, P) for k in range(C)]))
    for label, n, tasks in groups:
        tot, raw, cores, ms = [0] * 5, 0, 0, []
        with Pool(int(opt.get('jobs', os.cpu_count()))) as pool:
            for res in pool.imap_unordered(run_random, tasks):
                if res is None: continue
                cores += 1; ms.append(res['m']); raw += res['raw']
                tot = [a + b for a, b in zip(tot, res['least'])]
                for sets, m, vals in res['bad']: print(f"  LB4r FAILS (R = 3): n={n} m={m} sets={sets} values={vals}", flush=True)
        print(f"{label}: {cores} (4, 3) cores (m {min(ms)}..{max(ms)}), {cores * P} random profiles; least number of nested "
              f"rotations that works, R = 0, 1, 2, 3: {tot[:4]}; LB4r (R <= 3) fails: {tot[4]}; raw EFX0/D2 failures: {raw} "
              f"[{time.time() - t0:.0f} s]", flush=True)

if __name__ == '__main__':
    main()
