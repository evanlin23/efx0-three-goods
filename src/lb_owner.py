"""Driver for lb_owner.c (construction LB's last step, ledger S2.LB, proofs/lb_last_step.md): runs it on every
connected core with n agents and the given numbers of goods m (default: every m from 3 to 2n), all ranking profiles,
in parallel, and sums the counters it prints. Examples ("ex" lines) are printed with their core.
Usage: lb_owner.py n [m ...] [--jobs=N] [--bin=NAME] [--mode=M --seed=S --reps=R] [--ex=E]
  NAME.c in src/ (default lb_owner); --mode/--seed/--reps are passed to the program after its header (lbplus.c).
  "BAD" lines (assertion or raw-check failures, lbplus.c) are always printed.
  --random=COUNT[:SEED]  instead of the cores: COUNT random instances per (n, m) in which every agent values a
                         uniformly random set of 3 of the m goods (not cores: goods may be valued by nobody or be
                         private to anyone; evidence only)"""
import sys, os, subprocess, time, multiprocessing
from frontier import options
from cores_nauty import gen_cores_nauty

HERE = os.path.dirname(os.path.abspath(__file__))

def compile_c(name):
    src, out = os.path.join(HERE, name + '.c'), os.path.join(HERE, name)
    deps = [src, os.path.join(HERE, 'construct.c'), os.path.join(HERE, 'lb_common.h')]
    if not os.path.exists(out) or os.path.getmtime(out) < max(map(os.path.getmtime, deps)):
        subprocess.run(['gcc', '-O2', '-o', out, src], check=True, cwd=HERE)
    return out

def run_chunk(task):
    binp, n, m, chunk, extra = task
    inp = f"{n} {m} {len(chunk)} {extra}\n" + "\n".join(" ".join(str(g) for S in sets for g in S) for _, sets in chunk) + "\n"
    out = subprocess.run([binp], input=inp, capture_output=True, text=True, check=True).stdout
    names, res, exs = None, [], []
    for line in out.split('\n'):
        t = line.split()
        if not t: continue
        if t[0] == 'names': names = t[1:]
        elif t[0] == 'core': res.append(list(map(int, t[3:])))
        elif t[0] == 'ex': exs.append((chunk[len(res)][1], line[3:]))
        elif t[0] == 'BAD': exs.append((chunk[len(res)][1], line))
    return names, res, exs

if __name__ == '__main__':
    args, opts = options(sys.argv[1:])
    n = args[0]; ms = args[1:] or list(range(3, 2 * n + 1))
    jobs = int(opts.get('jobs', os.cpu_count())); binp = compile_c(opts.get('bin', 'lb_owner'))
    extra = " ".join(opts[k] for k in ('mode', 'seed', 'reps') if k in opts)
    t0 = time.time(); log = lambda s: print(f"[{time.time() - t0:7.0f}s] {s}", flush=True)
    with multiprocessing.Pool(jobs) as pool:
        for m in ms:
            if 'random' in opts:
                import random
                cnt, _, sd = opts['random'].partition(':')
                rng = random.Random(f"{sd or 0}:{n}:{m}")
                cores = [(0, [sorted(rng.sample(range(m), 3)) for _ in range(n)]) for _ in range(int(cnt))]
            else:
                cores = gen_cores_nauty(n, m)
            if not cores: continue
            size = max(1, min(200, len(cores) // (4 * jobs) or 1))
            chunks = [cores[i:i + size] for i in range(0, len(cores), size)]
            outs = pool.map(run_chunk, [(binp, n, m, ch, extra) for ch in chunks])
            names = next((o[0] for o in outs if o[0]), None)
            tot = [0] * len(outs[0][1][0]) if outs[0][1] else []
            lab = names or [str(i) for i in range(len(tot))]
            for _, res, _ in outs:
                for r in res: tot = [max(a, b) if l.startswith('max') else a + b for l, a, b in zip(lab, tot, r)]
            log(f"n={n} m={m}: {len(cores)} cores; " + ", ".join(f"{a} {b}" for a, b in zip(lab, tot)))
            k = 0
            for _, _, exs in outs:
                for sets, e in exs:
                    if e.startswith('BAD') or k < int(opts.get('ex', 5)): log(f"   ex {sets}: {e}"); k += 1
    log("done")
