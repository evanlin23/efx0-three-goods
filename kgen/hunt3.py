"""Random hunt for failures of OC1 and its variants with n = 3 agents and any k (brute force, kgen/oc3.c).

Per instance and order (6 orders): OC1 as tested in k4/sdc (CODE: one chain with t >= 0, one absorber), OC1 with
t >= 1 (STRICT), OC (FREEOC: free completion), MD, and SD-C (some order whose picks extend freely).  Prints every
failing instance (JSON values, the order, the picks).

    python3 kgen/hunt3.py SEED N MMIN MMAX [kinds,comma,separated]"""
import sys, random, collections, time, json, os, multiprocessing as mp
from oc3lib import brute, picks, ORD
from gen3 import gen, strict

KINDS = ['klim:3', 'klim:4', 'klim:5', 'klim:8', 'general', 'zeros', 'ident', 'junk', 'ties']


def job(args):
    seed, kind, m = args
    if kind.startswith('klim'): m = min(m, 3 * int(kind.split(':')[1]))
    rng = random.Random(seed); v = gen(kind, m, rng); r = brute(v)
    return seed, kind, m, v, r


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5])
    kinds = sys.argv[5].split(',') if len(sys.argv) > 5 else KINDS
    print('$ python3 kgen/hunt3.py', *sys.argv[1:], flush=True)
    rng = random.Random(seed); t0 = time.time(); C = collections.Counter()
    tasks = [(seed * 1000003 + t, kinds[t % len(kinds)], rng.randint(lo, hi)) for t in range(N)]
    with mp.Pool(os.cpu_count()) as pool:
        for s, kind, m, v, r in pool.imap_unordered(job, tasks, chunksize=4):
            tag = kind + ('' if strict(v) else '(nonstrict)')
            C['instances %s' % kind] += 1
            if r[0]['EFX'] == 0:
                C['NO EFX0 ALLOCATION'] += 1; print('NO EFX0', json.dumps(v), flush=True); continue
            for o, d in enumerate(r):
                C['orders'] += 1
                C['orders: chains needed %s' % (0 if d['NONE'] else (1 if d['CODE'] else 'FAIL'))] += 1
                for key in ['CODE', 'STRICT', 'FREEOC', 'MD']:
                    if d[key] == 0:
                        C['FAIL %s %s' % (key, tag)] += 1
                        if C['shown %s %s' % (key, tag)] < 5:
                            C['shown %s %s' % (key, tag)] += 1
                            print('FAIL', key, tag, 'm', m, json.dumps(v), 'order', ORD[o], 'picks', picks(v, ORD[o]),
                                  flush=True)
            if not any(d['FREE0'] for d in r):
                C['FAIL SD-C %s' % tag] += 1; print('FAIL SD-C', tag, json.dumps(v), flush=True)
    for k in sorted(C):
        if not k.startswith('shown'): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
