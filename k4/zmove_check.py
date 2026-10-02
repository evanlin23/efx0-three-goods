#!/usr/bin/env python3
"""Theorem ZMOVE on data (workstream proof/k4-zmove-hall; k4/zmove_hall.md). EVIDENCE tooling.

For every profile of the inputs with ω >= 1 and every key κ with def*(κ) > 0, it lists the Z′-maxima (configurations
maximizing (r′, Λ′), k4/sx.md §2 and §6) by their states P_Q, and at each the (T3⁺) moves with at most one helper from
P_Q to a min-frozen state of deficit <= 0 (k4/zmh_lib.py), and the (T4) edges of κ to keys with smaller def*.
ZMOVE holds at κ iff some P_Q has such a move or κ has such a (T4) edge.

usage: python3 k4/zmove_check.py [--max=N] [--every=E] [--part=i/N] [--fmin=F] [--out=OUT.jsonl.gz] INPUT ...
INPUT: gzip JSON lines or a JSON list of {sets, vals, m}. Prints a summary; with --out one JSON line per key."""
import collections, gzip, json, os, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zmh_lib import Prof, load_inputs, show, pc


def run(argv):
    opts = {}; ins = []
    for a in argv:
        if a.startswith('--'):
            k, _, v = a[2:].partition('='); opts[k] = v
        else: ins.append(a)
    mx = int(opts.get('max', 10 ** 9)); every = int(opts.get('every', 1))
    part = opts.get('part'); pi, pn = (map(int, part.split('/')) if part else (0, 1))
    fmin = int(opts.get('fmin', 1))
    out = gzip.open(opts['out'], 'wt') if 'out' in opts else None
    cnt = collections.Counter()
    seen = set()
    t0 = time.time()
    idx = 0
    for path in ins:
        for rec in load_inputs(path):
            idx += 1
            if (idx - 1) % every or ((idx - 1) // every) % pn != pi: continue
            sig = json.dumps([rec['sets'], rec['vals'], rec.get('m')])
            if sig in seen: continue
            seen.add(sig)
            if cnt['profiles'] >= mx: break
            pr = Prof(rec['sets'], rec['vals'], rec.get('m'))
            cnt['profiles'] += 1
            if pr.omega < 1 or pr.f < fmin: continue
            cnt['profiles with f >= %d, omega >= 1' % fmin] += 1
            for key, ds in pr.dstar.items():
                if ds <= 0: continue
                cnt['keys def*>0'] += 1
                cnt['keys def*>0, f=%d' % pr.f] += 1
                res, t4, best = pr.zmove(key)
                nz = sum(1 for P, mv in res if mv)
                ok = nz > 0 or bool(t4)
                cnt['Z-maxima'] += len(res)
                cnt['Z-maxima with a move'] += nz
                if nz == len(res) and res: cnt['keys: every Z-max has a move'] += 1
                if nz: cnt['keys ZMOVE by a move'] += 1
                elif t4: cnt['keys ZMOVE by a T4 edge only'] += 1
                if not ok:
                    cnt['keys ZMOVE FAILS'] += 1
                    print('ZMOVE FAILS', json.dumps({'sets': rec['sets'], 'vals': rec['vals'], 'm': pr.m}),
                          'key', [None if b is None else sorted(bits_(b)) for b in key], 'def*', ds, flush=True)
                kinds = collections.Counter()
                for P, mv in res:
                    for Q, w, Y, t3, x, z in mv:
                        kinds[('W%d' % w, 'h' if Y else '-')] += 1
                for kk in kinds: cnt['moves %s%s' % kk] += kinds[kk]
                if out:
                    out.write(json.dumps({'sets': rec['sets'], 'vals': rec['vals'], 'm': pr.m, 'f': pr.f,
                                          'omega': pr.omega, 'key': [None if b is None else sorted(bits_(b)) for b in key],
                                          'dstar': ds, 'pot': best,
                                          'zmax': [[show(P), pr.D[P], [[show(Q), pr.D[Q], w, list(Y), x, z]
                                                                       for Q, w, Y, t3, x, z in mv]] for P, mv in res],
                                          't4': len(t4)}) + '\n')
    if out: out.close()
    print('time %.1fs' % (time.time() - t0))
    for k in sorted(cnt): print('%-50s %d' % (k, cnt[k]))
    return cnt


def bits_(b):
    g = 0
    while b:
        if b & 1: yield g
        b >>= 1; g += 1


if __name__ == '__main__':
    run(sys.argv[1:])
