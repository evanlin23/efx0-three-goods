#!/usr/bin/env python3
"""Random profiles on structured families and random cores (k4/c4min_hunt.md §4): k4/c4min_hunt.c -R N solves each
profile exactly (f* and whether some min-frozen pre-allocation has deficit <= 0).

Profiles: uniform random types (--mode=uniform), or a base profile with K agents re-typed at random
(--mode=perturb:K; the base profile is §7's values for the families ht*, htc; for other families the first profile
drawn). Every FAIL line is re-evaluated with k4/c4x.c (-1s -R -a) and printed. With --verify=K, K profiles per instance
are also solved with -1q and their certificates re-checked literally by k4/c4min_brute.verify_certificate (only when
the certificate has f = 0 frozen agents or f <= sigma, where no lower bound on f* is needed).

usage: c4min_sample.py --family=NAME:A[:B] ... [--random=N:M:N4:COUNT] --profiles=N [--mode=uniform|perturb:K]
                        [--seed=S] [--jobs=J] [--verify=K]"""
import json, random, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
import c4min_common as cc
import c4min_families as F
import c4min_brute
from c4min_climb import parse_profile


def base_profile(name, args, sets, doms):
    if name not in ('ht', 'htc', 'ht2', 'htx'): return None
    want = []
    for i, S in enumerate(sets):
        v = (8, 6, 5, 4) if (name != 'htc' and i == 0) else (8, 6, 4, 3)
        want.append(v)
    idx = []
    for S, D, w in zip(sets, doms, want):
        ts = [t for t, v in enumerate(D) if tuple(v[g] for g in S) == w]
        if not ts: return None
        idx.append(ts[0])
    return idx


def run(args):
    tag, sets, m, n_prof, mode, seed, start = args
    doms = cc.domains(sets, m)
    inp = cc.input_all(sets, m, doms)
    opts = ['-R', str(n_prof), '-S', str(seed), '-x', '5']
    if mode.startswith('perturb') and start is not None:
        opts += ['-P', '-K', mode.split(':')[1]]
        inp += ' '.join(map(str, start)) + '\n'
    t = time.time()
    out = subprocess.run([cc.hunt_binary(), *opts], input=inp, capture_output=True, text=True, check=True).stdout
    return tag, sets, m, doms, out, time.time() - t


def main():
    srcs, n_prof, mode, seed, jobs, verify = [], 100, 'uniform', 1, 4, 0
    for a in sys.argv[1:]:
        k, _, v = a.partition('=')
        if k == '--family': srcs.append(('family', v))
        elif k == '--random': srcs.append(('random', v))
        elif k == '--profiles': n_prof = int(v)
        elif k == '--mode': mode = v
        elif k == '--seed': seed = int(v)
        elif k == '--jobs': jobs = int(v)
        elif k == '--verify': verify = int(v)
        else: raise SystemExit(f'unknown option {a}')
    rng = random.Random(seed)
    cc.hunt_binary()
    tasks = []
    for kind, v in srcs:
        if kind == 'family':
            name, *args = v.split(':')
            sets, m = F.normalize(F.family(name, args, rng))
            assert F.check_core(sets, m), v
            start = base_profile(name, args, sets, cc.domains(sets, m))
            tasks.append((v, sets, m, n_prof, mode, seed * 7919 + len(tasks), start))
        else:
            n, m, n4, cnt = map(int, v.split(':'))
            for r in range(cnt):
                sets = F.random_core(rng, n, m, n4)
                tasks.append((f'random{n},{m},{n4}#{r}', sets, m, n_prof, 'uniform', seed * 7919 + len(tasks), None))
    tot = fails = 0
    with ThreadPoolExecutor(jobs) as ex:
        for tag, sets, m, doms, out, dt in ex.map(run, tasks):
            for line in out.splitlines():
                if line.startswith('RANDOM'):
                    w = line.split()
                    tot += int(w[2]); fails += int(w[4])
                    print(f'{tag} (n {len(sets)}, m {m}, {mode}): {line} ({dt:.1f} s)', flush=True)
                elif line.startswith('FAIL'):
                    vals = parse_profile(line, sets)
                    try: ref = cc.c4x_one(sets, m, vals)
                    except Exception as e: ref = f'c4x error {e}'
                    print(f'FAIL {tag} sets {json.dumps(sets)} m {m}\n  {line}\n  c4x: {ref}', flush=True)
            for r in range(verify):
                vals = [rng.choice(D) for D in doms]
                inp = cc.input_one(sets, m, vals) + ' '.join('0' for _ in sets) + '\n'
                q = subprocess.run([cc.hunt_binary(), '-1q'], input=inp, capture_output=True, text=True, check=True).stdout.split()
                f, holds, sigma = int(q[2]), int(q[4]), int(q[6])
                if not holds: print(f'  verify: FAIL at a random profile of {tag}', flush=True); continue
                owner = int(q[8]); k = q.index('bases')
                C = [int(x) for x in q[10:k]]
                bases = [[int(g) for g in b.strip('{}').split(',') if g] for b in q[k + 1:]]
                fc = c4min_brute.verify_certificate(sets, vals, m, bases, None if owner < 0 else owner, C)
                assert fc == f, (fc, f)
                if f != 0 and f > sigma: print(f'  verify: certificate re-checked but f = {f} > 0 needs the lower bound', flush=True)
            if verify: print(f'  verify: {verify} certificates of {tag} re-checked literally', flush=True)
    print(f'TOTAL profiles {tot} fails {fails}')


if __name__ == '__main__':
    main()
