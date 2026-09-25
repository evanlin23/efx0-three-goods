"""EVIDENCE only (random profiles, PROMPT.md §5 rule 3): k = 4 cores with n agents, R uniformly random strict
profiles each; for each, is there an EFX₀ allocation with at most one bundle of more than 2 goods (D2), else any?
Usage: sample5.py n R [--pure] [--jobs=J] [--seed=S]"""
import os, random, sys, time
from multiprocessing import Pool
import search4 as S4

def run(task):
    n, m, idx, sets, R, seed = task
    C, rng = S4.Core(n, m, sets), random.Random(seed)
    sol2, x2, z2 = C.inner(2, 1)
    solA = None
    fails2, cex = [], []
    for _ in range(R):
        prof = [rng.randrange(len(D)) for D in C.dom]
        if C.allocation(sol2, x2, z2, prof) is not None: continue
        fails2.append([list(C.dom[i][t]) for i, t in enumerate(prof)])
        if solA is None: solA = C.inner(None, None)
        if C.allocation(*solA, prof) is None: cex.append(fails2[-1])
    return m, sets, fails2, cex

if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) if '=' in a else (a[2:], True) for a in sys.argv[1:] if a.startswith('--'))
    n, R, pure = int(args[0]), int(args[1]), 'pure' in opt
    seed = int(opt.get('seed', 1))
    tasks = [(n, m, idx, sets, R, hash((seed, m, idx)) & 0xffffffff)
             for m in range(4, 3 * n + 1) for idx, sets in enumerate(S4.cores(n, m, pure))]
    print(f"n={n}{' pure' if pure else ''}: {len(tasks)} cores x {R} random strict profiles (EVIDENCE)", flush=True)
    t0, per_m = time.time(), {}
    with Pool(int(opt.get('jobs', os.cpu_count()))) as pool:
        for m, sets, f2, cex in pool.imap_unordered(run, tasks, chunksize=4):
            st = per_m.setdefault(m, [0, 0, 0, 0])
            st[0] += 1; st[1] += len(f2); st[2] += bool(f2); st[3] += len(cex)
            if f2: print(f"  D2 fails: m={m} sets={sets} profile={f2[0]}", flush=True)
            if cex: print(f"  NO EFX0 ALLOCATION: m={m} sets={sets} profile={cex[0]}", flush=True)
    for m, st in sorted(per_m.items()):
        print(f"  m={m}: {st[0]} cores, {st[0] * R} profiles; D2 fails on {st[1]} profiles in {st[2]} cores; "
              f"no EFX0 allocation: {st[3]}", flush=True)
    print(f"  [{time.time() - t0:.0f}s]", flush=True)
