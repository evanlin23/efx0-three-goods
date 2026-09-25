"""Driver for k4/lb4_nsw.c (NSW-guided unbounded rotations; k4/nsw.md): builds the binary (named by the source's hash),
feeds it profiles, runs in parallel, and sums the per-core result lines.

Sources of profiles (any combination):
  FILE ...        certificate files (results/k4_certs_*.json.gz; only the core lists are used): every strict profile of
                  every core (--exhaustive), or --sample=S random draws per core (--seed=X; profiles drawn uniformly
                  with replacement, so a profile can repeat); --m=5,6 keeps only the cores with these m;
  --h=1,2,3       the cores H_t of k4/c4.md section 7 with their profile (one profile each);
  --gm4           the named instances of k4/gm4_counterexample.py (A-H, P, Q, S; one profile each).
Types are check4.core_domains' representatives (the smallest integer vector of each type in [1, 16]^d); NSW compares
products of values, which depend on the representative, so the results are for these values.
Every run of the binary must exit with status 0 and report exactly the profiles it was given (the product of the
domain sizes, the number of draws, or 1); otherwise the driver stops.
Usage: nsw_run.py [FILE ...] [--exhaustive | --sample=S --seed=X] [--m=M,..] [--h=..] [--gm4] [--jobs=J] [--show=N]
                  [C options, e.g. -N1 -P0 -i0 -w1 -c1 -L50000]"""
import gzip, hashlib, json, os, random, re, subprocess, sys, tempfile, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check4

SRC = os.path.join(HERE, 'lb4_nsw.c')
BIN = os.path.join(tempfile.gettempdir(), 'k4_lb4_nsw_' + hashlib.sha256(open(SRC, 'rb').read()).hexdigest()[:16])

def build():
    if not os.path.exists(BIN):
        subprocess.run(['gcc', '-O2', '-o', BIN, SRC], check=True, stderr=subprocess.DEVNULL)

def encode_all(sets, m):
    doms = check4.core_domains(sets, m, False)
    out = [f"{len(sets)} {m}"]
    for S, dom in zip(sets, doms):
        out.append(f"{len(S)} {' '.join(map(str, S))} {len(dom)}")
        out += [' '.join(str(v[g]) for g in S) for v in dom]
    return '\n'.join(out) + '\n'

def encode_profile(sets, m, vals):
    """vals[i]: dict good -> value for agent i (one type per agent)."""
    out = [f"{len(sets)} {m}"]
    for S, v in zip(sets, vals):
        out.append(f"{len(S)} {' '.join(map(str, S))} 1")
        out.append(' '.join(str(v[g]) for g in S))
    return '\n'.join(out) + '\n'

def hcore(t):
    """H_t of k4/c4.md section 7: goods g_1..g_t, z, u, u', then a, b, c of each gadget; agents l, then per gadget
    x_{j,1..3}, y_j (the same indexing as k4/c4_verify_H/hcore.py)."""
    goods = [f"g{j}" for j in range(1, t + 1)] + ["z", "u", "u'"]
    for j in range(1, t + 1):
        for i in range(1, 4): goods += [f"a{j}{i}", f"b{j}{i}", f"c{j}{i}"]
    gi = {g: k for k, g in enumerate(goods)}
    vals = [{"g1": 8, "z": 6, "u": 5, "u'": 4}]
    for j in range(1, t + 1):
        for i in range(1, 4): vals.append({f"a{j}{i}": 8, f"b{j}{i}": 6, f"c{j}{i}": 4, f"g{j}": 3})
        vals.append({f"a{j}1": 8, f"a{j}2": 6, f"a{j}3": 4, (f"g{j + 1}" if j < t else "z"): 3})
    vals = [{gi[g]: x for g, x in v.items()} for v in vals]
    sets = [sorted(v) for v in vals]
    return sets, len(goods), vals

def run(task):
    label, inp, opts, expect = task
    r = subprocess.run([BIN] + opts, input=inp, capture_output=True, text=True)
    if r.returncode: raise RuntimeError(f"{label}: exit status {r.returncode}: {r.stderr[-2000:]}")
    got = sum(int(mm.group(3)) for mm in map(LINE.match, r.stdout.splitlines()) if mm)
    if got != expect: raise RuntimeError(f"{label}: {got} profiles reported, {expect} given")
    return label, r.stdout, r.stderr

LINE = re.compile(r"nsw N(\d+) P(\d+) profiles (\d+) all_policies_fail (\d+) \(with a no-improving-rotation dead end (\d+)\)(.*)")
POL = re.compile(r"u(\d) ok (\d+) norot (\d+) noimprove (\d+) undecided (\d+) rawfail (\d+) maxmoves (\d+) moves:([\d,]+)")

def add(tot, line):
    mm = LINE.match(line)
    if not mm: return False
    tot['profiles'] += int(mm.group(3)); tot['allfail'] += int(mm.group(4)); tot['allfail_nsw'] += int(mm.group(5))
    tot['trunc'] |= 'TRUNCATED' in line
    for p in POL.finditer(mm.group(6)):
        q = tot['pol'].setdefault(p.group(1), {'ok': 0, 'norot': 0, 'noimprove': 0, 'undecided': 0, 'rawfail': 0, 'maxmoves': 0, 'moves': [0] * 8})
        for k, g in (('ok', 2), ('norot', 3), ('noimprove', 4), ('undecided', 5), ('rawfail', 6)): q[k] += int(p.group(g))
        q['maxmoves'] = max(q['maxmoves'], int(p.group(7)))
        q['moves'] = [a + int(b) for a, b in zip(q['moves'], p.group(8).split(','))]
    return True

def fmt(name, tot):
    s = [f"{name}: profiles {tot['profiles']}, all three policies fail {tot['allfail']} "
         f"(of which with a no-improving-rotation dead end {tot['allfail_nsw']}){' CANDIDATES_TRUNCATED' if tot['trunc'] else ''}"]
    for u in ('1', '2', '0'):
        q = tot['pol'].get(u)
        if q: s.append(f"    u{u}: ok {q['ok']}, dead end without a valid rotation {q['norot']}, without an improving one "
                       f"{q['noimprove']}, undecided {q['undecided']}, raw failures {q['rawfail']}; rotations used "
                       f"(0..6, 7+) {q['moves']}, max {q['maxmoves']}")
    return '\n'.join(s)

def main():
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    copts = [a for a in sys.argv[1:] if a.startswith('-') and not a.startswith('--')]
    files = [a for a in sys.argv[1:] if not a.startswith('-')]
    build()
    print("command: python3 k4/nsw_run.py " + ' '.join(sys.argv[1:]), flush=True)
    print(f"binary: {BIN} (sha256 of k4/lb4_nsw.c: {hashlib.sha256(open(SRC, 'rb').read()).hexdigest()})", flush=True)
    rng = random.Random(int(opt.get('seed', 1)))
    tasks = []
    for fn in files:
        data = json.load(gzip.open(fn, 'rt'))
        for r in data['cores']:
            if 'm' in opt and r['m'] not in [int(x) for x in opt['m'].split(',')]: continue
            if 'exhaustive' in opt:
                expect = 1
                for D in check4.core_domains(r['sets'], r['m'], False): expect *= len(D)
                tasks.append((os.path.basename(fn), encode_all(r['sets'], r['m']), copts, expect))
            else:
                doms = check4.core_domains(r['sets'], r['m'], False)
                S = int(opt.get('sample', 100))
                inp = ''.join(encode_profile(r['sets'], r['m'], [rng.choice(D) for D in doms]) for _ in range(S))
                tasks.append((os.path.basename(fn), inp, copts, S))
    for t in ([int(x) for x in opt['h'].split(',')] if 'h' in opt else []):
        sets, m, vals = hcore(t)
        tasks.append((f"H_{t}", encode_profile(sets, m, vals), copts, 1))
    if 'gm4' in opt:
        import gm4_counterexample as G
        for label, vals, _, _ in G.INSTANCES:
            m = 1 + max(g for v in vals for g in v)
            tasks.append((f"GM4 {label.split(':')[0]}", encode_profile([sorted(v) for v in vals], m, vals), copts, 1))
    t0, tots, shown = time.time(), {}, 0
    with Pool(int(opt.get('jobs', os.cpu_count()))) as pool:
        for label, out, err in pool.imap_unordered(run, tasks):
            tot = tots.setdefault(label, {'profiles': 0, 'allfail': 0, 'allfail_nsw': 0, 'trunc': False, 'pol': {}})
            for line in out.splitlines():
                if not add(tot, line): print("  ?", line)
            for line in err.splitlines():
                if shown < int(opt.get('show', 5)): print("  " + line[:400], flush=True); shown += 1
    for name in sorted(tots): print(fmt(name, tots[name]), flush=True)
    print(f"[{time.time() - t0:.0f} s]", flush=True)

if __name__ == '__main__':
    main()
