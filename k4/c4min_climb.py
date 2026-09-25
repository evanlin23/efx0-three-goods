#!/usr/bin/env python3
"""Adversarial search for C4min (k4/c4min_hunt.md §3): hill-climbing of strict profiles with k4/c4min_hunt.c -H.

Objective (maximized): (d*, -good) or, with --order=1, (-good, d*), where d* is the least deficit over the
pre-allocations with the fewest frozen agents and good the number of them with deficit <= 0; C4min fails at a
profile iff good = 0 iff d* > 0. Every profile with d* > 0 found by the climber (CEX) is re-evaluated with
k4/c4x.c (-1s -R -a) and, when small enough, with the brute force k4/c4min_brute.py, and printed.

Core sources (several allowed):
  --file=PATH[:K]          the cores of a certificate file (K: a random sample of K cores)
  --random=N:M:N4:COUNT    COUNT random connected k = 4 cores (N agents, N4 with 4 goods, M goods)
  --family=NAME:A[:B]      a structured family of k4/c4min_families.py (ht, ht2, htx, htc, grid, chain, cycle, tree)
options: --iters=I --restarts=R --stale=T --order=0|1 --seed=S --jobs=J --start=paper (families ht*: the first
restart starts from §7's values) --top=K (print the K tightest cores)."""
import json, random, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
import c4min_common as cc
import c4min_families as F
import c4min_brute


def parse_profile(line, sets):
    """values [g:v,..] per agent from a CEX/BEST line -> list of dicts"""
    part = line.split(' values ')[1]
    vals = []
    for blk in part.split('] ['):
        blk = blk.strip('[] \n')
        vals.append({int(a): int(b) for a, b in (x.split(':') for x in blk.split(','))})
    return vals


def run_core(args):
    tag, sets, m, opts, start = args
    doms = cc.domains(sets, m)
    if any(len(D) == 0 for D in doms): return tag, sets, m, None, [], 0.0
    inp = cc.input_all(sets, m, doms)
    extra = []
    if start is not None:
        idx = []
        for i, (S, D) in enumerate(zip(sets, doms)):
            want = tuple(start[i])
            ts = [t for t, v in enumerate(D) if tuple(v[g] for g in S) == want]
            if not ts: idx = None; break
            idx.append(ts[0])
        if idx is not None:
            inp += ' '.join(map(str, idx)) + '\n'; extra = ['-P']
    t = time.time()
    out = subprocess.run([cc.hunt_binary(), '-H', *opts, *extra], input=inp, capture_output=True, text=True, check=True).stdout
    best, cex = None, []
    for line in out.splitlines():
        if line.startswith('BEST'):
            w = line.split()
            best = {'dstar': int(w[2]), 'good': int(w[4]), 'fstar': int(w[6]), 'evals': int(w[8]), 'line': line}
        elif line.startswith('CEX'): cex.append(line)
    return tag, sets, m, best, cex, time.time() - t


def confirm(sets, m, line):
    vals = parse_profile(line, sets)
    res = {'hunt': cc.hunt_one(sets, m, vals)}
    try: res['c4x'] = cc.c4x_one(sets, m, vals)
    except Exception as e: res['c4x'] = f'error {e}'
    if m <= 9 and len(sets) <= 4: res['brute'] = c4min_brute.brute(sets, vals, m)
    return vals, res


def main():
    srcs, iters, restarts, stale, order, seed, jobs, start, top = [], 3000, 4, 400, 0, 1, 4, None, 10
    for a in sys.argv[1:]:
        k, _, v = a.partition('=')
        if k == '--file': srcs.append(('file', v))
        elif k == '--random': srcs.append(('random', v))
        elif k == '--family': srcs.append(('family', v))
        elif k == '--iters': iters = int(v)
        elif k == '--restarts': restarts = int(v)
        elif k == '--stale': stale = int(v)
        elif k == '--order': order = int(v)
        elif k == '--seed': seed = int(v)
        elif k == '--jobs': jobs = int(v)
        elif k == '--start': start = v
        elif k == '--top': top = int(v)
        else: raise SystemExit(f'unknown option {a}')
    rng = random.Random(seed)
    cc.hunt_binary()                       # compile once before the threads start
    tasks = []
    for kind, v in srcs:
        if kind == 'file':
            path, _, K = v.partition(':')
            cores = cc.load_cores(path)
            idx = list(range(len(cores)))
            if K: idx = sorted(rng.sample(idx, min(int(K), len(idx))))
            for ci in idx: tasks.append((f'{path.split("/")[-1]}#{ci}', cores[ci]['sets'], cores[ci]['m'], None))
        elif kind == 'random':
            n, m, n4, cnt = map(int, v.split(':'))
            for r in range(cnt):
                sets = F.random_core(rng, n, m, n4)
                if sets is None: print(f'no random core for {v}'); break
                tasks.append((f'random{n},{m},{n4}#{r}', sets, m, None))
        else:
            name, *args = v.split(':')
            sets, m = F.normalize(F.family(name, args, rng))
            assert F.check_core(sets, m), f'{v} is not a k = 4 core'
            st = None
            if start == 'paper' and name == 'ht': st = F.ht_values(int(args[0]))
            tasks.append((f'{v}', sets, m, st))
    print(f'# {len(tasks)} cores; iters {iters} restarts {restarts} stale {stale} order {order} seed {seed}', flush=True)
    results, ncex, t0 = [], 0, time.time()
    hist = {}
    with ThreadPoolExecutor(jobs) as ex:
        futs = []
        for k, (tag, sets, m, st) in enumerate(tasks):
            opts = [str(iters), '-Z', str(restarts), '-T', str(stale), '-O', str(order), '-S', str(seed * 1000003 + k)]
            futs.append(ex.submit(run_core, (tag, sets, m, opts, st)))
        for fu in futs:
            tag, sets, m, best, cex, dt = fu.result()
            if best is None: print(f'{tag}: empty type domain, skipped'); continue
            results.append((best['dstar'], -best['good'], tag, sets, m, best))
            key = (best['dstar'], min(best['good'], 3))
            hist[key] = hist.get(key, 0) + 1
            for line in cex:
                ncex += 1
                vals, res = confirm(sets, m, line)
                print(f'CEX {tag} sets {json.dumps(sets)} m {m}\n  {line}\n  re-evaluated: {json.dumps(res)}', flush=True)
    results.sort(key=lambda r: (r[0], r[1]), reverse=True)
    print(f'# done in {time.time() - t0:.0f} s; cores {len(results)}; CEX lines {ncex}')
    print('# best (d*, min(good, 3)) per core: ' + ', '.join(f'{k}: {v}' for k, v in sorted(hist.items(), reverse=True)))
    for r in results[:top]:
        print(f'TIGHT {r[2]} m {r[4]} sets {json.dumps(r[3])}\n  {r[5]["line"]}')


if __name__ == '__main__':
    main()
