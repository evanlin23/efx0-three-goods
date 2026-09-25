#!/usr/bin/env python3
"""Cross-check of the three C4min implementations on random strict profiles (k4/c4min_hunt.md §1):
k4/c4min_hunt.c -1 (this workstream), k4/c4x.c -1s -R -a (PR #36) and the brute force k4/c4min_brute.py (only where
it is fast enough: m <= MAXM_BRUTE). Compared per profile: f*, d* (least deficit over the min-frozen pre-allocations,
'inf' when no owner and C work), the number of valid pre-allocations, of min-frozen ones, and of min-frozen ones with
deficit <= 0; with the brute force also 'some min-frozen P is completable'.

usage: c4min_crosscheck.py FILE [FILE ...] [--per-core=K] [--seed=S] [--brute-m=M] [--w0] [--no-c4x]"""
import random, sys
import c4min_common as cc
import c4min_brute

INF_HUNT, INF_C4X = 10 ** 6, 1 << 20


def norm(r):
    r = dict(r)
    if r.get('dstar') in (INF_HUNT, INF_C4X, c4min_brute.INF): r['dstar'] = 'inf'
    return r


def main():
    files, per, seed, bm, w0, use_c4x = [], 3, 1, 8, False, True
    for a in sys.argv[1:]:
        if a.startswith('--per-core='): per = int(a[11:])
        elif a.startswith('--seed='): seed = int(a[7:])
        elif a.startswith('--brute-m='): bm = int(a[10:])
        elif a == '--w0': w0 = True
        elif a == '--no-c4x': use_c4x = False
        else: files.append(a)
    rng = random.Random(seed)
    opts = ['-w0'] if w0 else []
    tot = mism = nb = 0
    for f in files:
        cores = cc.load_cores(f)
        for ci, c in enumerate(cores):
            doms = cc.domains(c['sets'], c['m'])
            for _ in range(per):
                vals = [rng.choice(D) for D in doms]
                h = norm(cc.hunt_one(c['sets'], c['m'], vals, opts))
                keys = ('fstar', 'dstar', 'valid', 'minfrozen', 'good')
                refs = []
                if use_c4x: refs.append(('c4x', norm(cc.c4x_one(c['sets'], c['m'], vals, opts))))
                if c['m'] <= bm and len(c['sets']) <= 4:
                    refs.append(('brute', norm(c4min_brute.brute(c['sets'], vals, c['m'], base=w0)))); nb += 1
                tot += 1
                for name, r in refs:
                    ks = keys + (('completable',) if name == 'brute' else ())
                    if any(h[k] != r[k] for k in ks):
                        mism += 1
                        print('MISMATCH', name, f, ci, c['sets'], [[v[g] for g in S] for S, v in zip(c['sets'], vals)],
                              {k: h[k] for k in ks}, {k: r[k] for k in ks}, flush=True)
        print(f'FILE {f} profiles so far {tot} mismatches {mism} (brute-force comparisons {nb})', flush=True)
    print(f'TOTAL profiles {tot} mismatches {mism} brute {nb}')


if __name__ == '__main__':
    main()
