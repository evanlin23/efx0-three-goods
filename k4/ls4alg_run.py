"""Driver for ls4alg.c (Algorithm LS4, k4/local_search4.md) on the cores of k = 4 certificate files.

Cores and type domains come from k4/check4.py (core lists complete by orbit counting there; one integer representative
per strict balanced type; an agent with two private goods keeps only p + q < s + t).  With --ties every balanced weak
type (check4's tied domain) is covered: the run on a tied profile equals the run on the strict profile of its
perturbation 32 v + w (w = 2^position), so each tied type is attached as a preimage to the strict representative of
its perturbed type, and ls4alg.c checks the output against it with the raw definition.
Usage: ls4alg_run.py CERTFILE [...] [--sample=K] [--ties] [--jobs=J] [--only=IDX] [--cores=A:B] [--maxm=M] [--defs='-DNOX']
(--prog=ls4_deadend: dead ends of Pareto local search, attempts/k4-ls-dead-end.md)
(--prog=ls4_allstates: check conjecture TP4 on every stable state, not only reached ones;
 --defs=-DNOX: no exchange cycles; --defs=-DBADDUMP: unchecked dump; both are sensitivity tests that must fail)
"""
import gzip, itertools, json, os, subprocess, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from check4 import core_domains

def build(defs='', prog='ls4alg'):
    d = os.path.expanduser('~/.cache/ls4'); os.makedirs(d, exist_ok=True)
    exe, src = os.path.join(d, prog + defs.replace(' ', '').replace('-D', '_')), os.path.join(HERE, prog + '.c')
    newest = max(os.path.getmtime(src), os.path.getmtime(os.path.join(HERE, 'ls4alg.c')))
    if not os.path.exists(exe) or os.path.getmtime(exe) < newest:
        subprocess.run(['gcc', '-O2', '-march=native'] + defs.split() + ['-o', exe, src], check=True)
    return exe

def key(vals):
    """strict type of 32 v + w: dense ranking of all nonempty subset sums"""
    V = [32 * x + (1 << t) for t, x in enumerate(vals)]
    sums = [sum(V[t] for t in range(len(V)) if S >> t & 1) for S in range(1, 1 << len(V))]
    order = sorted(set(sums))
    assert len(order) == len(sums)
    return tuple(order.index(s) for s in sums)

def task_text(n, m, sets, ties, sample, seed):
    strict = core_domains(sets, m, False)
    tied = core_domains(sets, m, True) if ties else None
    lines = [f"{n} {m}"] + [" ".join(map(str, [len(S)] + list(S))) for S in sets]
    for i, S in enumerate(sets):
        reps = [[vals[g] for g in S] for vals in strict[i]]
        idx = {key(r): k for k, r in enumerate(reps)}
        assert len(idx) == len(reps)
        pre = [[] for _ in reps]
        if ties:
            for vals in tied[i]:
                v = [vals[g] for g in S]
                pre[idx[key(v)]].append(v)          # KeyError would mean a tied type outside the strict domain
            assert sum(map(len, pre)) == len(tied[i])
        lines.append(str(len(reps)))
        for r, P in zip(reps, pre):
            lines.append(" ".join(map(str, [len(P)] + r)))
            lines += [" ".join(map(str, v)) for v in P]
    lines.append(f"{1 if sample else 0} {sample or 0} {seed}")
    return "\n".join(lines) + "\n"

def work(args):
    exe, n, m, sets, ties, sample, seed = args
    t0 = time.time()
    out = subprocess.run([exe], input=task_text(n, m, sets, ties, sample, seed), capture_output=True, text=True)
    return sets, m, out.returncode, out.stdout, time.time() - t0

def main():
    files = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], '1') for a in sys.argv[1:] if a.startswith('--'))
    sample, ties, jobs = int(opt.get('sample', 0)), 'ties' in opt, int(opt.get('jobs', os.cpu_count()))
    exe = build(opt.get('defs', ''), opt.get('prog', 'ls4alg'))
    print('# ' + ' '.join(sys.argv), flush=True)
    tasks = []
    for f in files:
        data = json.load(gzip.open(f, 'rt'))
        recs = data['cores']
        lo, hi = map(int, opt['cores'].split(':')) if 'cores' in opt else (0, len(recs))
        for k, rec in enumerate(recs[lo:hi], lo):
            if 'only' in opt and k != int(opt['only']): continue
            if 'maxm' in opt and rec['m'] > int(opt['maxm']): continue
            if 'minm' in opt and rec['m'] < int(opt['minm']): continue
            tasks.append((exe, data['n'], rec['m'], rec['sets'], ties, sample, k + 1))
    tot, ncores, bad, t0 = {}, 0, 0, time.time()
    with Pool(jobs) as pool:
        for sets, m, rc, out, dt in pool.imap_unordered(work, tasks):
            ncores += 1
            for line in out.splitlines():
                if line.startswith('RESULT'):
                    kv = dict(x.split('=') for x in line.split()[1:])
                    for k, v in kv.items():
                        tot[k] = max(tot.get(k, 0), int(v)) if k.startswith('max') else tot.get(k, 0) + int(v)
                    if int(kv.get('deadprof', 0)): print(sets, 'm =', m, line, flush=True)
                elif line.startswith('FAIL') or line.startswith('DEADEND'): print(sets, line, flush=True)
            if rc != 0 or 'RESULT' not in out: bad += 1; print('BAD', sets, 'rc', rc, out[-500:], flush=True)
    print(f"TOTAL cores={ncores} badcores={bad} " + ' '.join(f"{k}={v}" for k, v in tot.items()) + f" wall={time.time() - t0:.0f}s", flush=True)
    sys.exit(1 if bad or tot.get('fail', 0) else 0)

if __name__ == '__main__':
    main()
