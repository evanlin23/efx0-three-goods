"""Driver for lb_owner.c (construction LB's last step, ledger S2.LB, proofs/lb_last_step.md): runs it on every
connected core with n agents and the given numbers of goods m (default: every m from 3 to 2n), all ranking profiles,
in parallel, and sums the counters it prints. Examples ("ex" lines) are printed with their core.
Usage: lb_owner.py n [m ...] [--jobs=N] [--bin=NAME]   (NAME.c in src/, default lb_owner)"""
import sys, os, subprocess, time, multiprocessing
from frontier import options
from cores_nauty import gen_cores_nauty

HERE = os.path.dirname(os.path.abspath(__file__))

def compile_c(name):
    src, out = os.path.join(HERE, name + '.c'), os.path.join(HERE, name)
    deps = [src, os.path.join(HERE, 'construct.c')]
    if not os.path.exists(out) or os.path.getmtime(out) < max(map(os.path.getmtime, deps)):
        subprocess.run(['gcc', '-O2', '-o', out, src], check=True, cwd=HERE)
    return out

def run_chunk(task):
    binp, n, m, chunk = task
    inp = f"{n} {m} {len(chunk)}\n" + "\n".join(" ".join(str(g) for S in sets for g in S) for _, sets in chunk) + "\n"
    out = subprocess.run([binp], input=inp, capture_output=True, text=True, check=True).stdout
    names, res, exs = None, [], []
    for line in out.split('\n'):
        t = line.split()
        if not t: continue
        if t[0] == 'names': names = t[1:]
        elif t[0] == 'core': res.append(list(map(int, t[3:])))
        elif t[0] == 'ex': exs.append((chunk[len(res)][1], line[3:]))
    return names, res, exs

if __name__ == '__main__':
    args, opts = options(sys.argv[1:])
    n = args[0]; ms = args[1:] or list(range(3, 2 * n + 1))
    jobs = int(opts.get('jobs', os.cpu_count())); binp = compile_c(opts.get('bin', 'lb_owner'))
    t0 = time.time(); log = lambda s: print(f"[{time.time() - t0:7.0f}s] {s}", flush=True)
    with multiprocessing.Pool(jobs) as pool:
        for m in ms:
            cores = gen_cores_nauty(n, m)
            if not cores: continue
            size = max(1, min(200, len(cores) // (4 * jobs) or 1))
            chunks = [cores[i:i + size] for i in range(0, len(cores), size)]
            outs = pool.map(run_chunk, [(binp, n, m, ch) for ch in chunks])
            names = next((o[0] for o in outs if o[0]), None)
            tot = [0] * len(outs[0][1][0]) if outs[0][1] else []
            for _, res, _ in outs:
                for r in res: tot = [a + b for a, b in zip(tot, r)]
            lab = names or [str(i) for i in range(len(tot))]
            log(f"n={n} m={m}: {len(cores)} cores; " + ", ".join(f"{a} {b}" for a, b in zip(lab, tot)))
            k = 0
            for _, _, exs in outs:
                for sets, e in exs:
                    if k < int(opts.get('ex', 5)): log(f"   ex {sets}: {e}"); k += 1
    log("done")
