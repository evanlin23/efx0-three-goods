"""Tests of the LB4 tester k4/lb4.c (results/k4_lb4_test.log).
(a) Sensitivity: with -s the construction ignores the owner constraint (all junk to r). The raw EFX0 check must then
    report failures, at n = 2 and n = 3; without -s it reports none.
(b) Lazy type branching vs brute force: for a variant that fails (-i0 -u1 -o2 -r1), for LB4 itself, and for nested
    rotations (-i0 -u3 -r3 -w1 -c1, whose rotation depth must be reset after a type split), the numbers of failing
    profiles and of raw-check failures per core must be the same when every profile is its own leaf (-b), on every core
    with n <= 3.
(c) The rejected variants of attempts/lb4-*.md reproduce (attempts/lb4_variants.py).
Usage: python3 k4/test_lb4.py"""
import gzip, json, os, subprocess, sys
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lb4_run

LB4 = '-i2 -u1 -r1 -w1 -c1'

def per_core(task):
    rec, opts = task
    p = subprocess.run([lb4_run.BIN] + opts.split() + ['-f0'], input=lb4_run.encode(rec['sets'], rec['m'], False),
                       capture_output=True, text=True, check=True)
    t = p.stdout.split()
    return dict(zip(t[0:22:2], map(int, t[1:22:2])))

def cores(n):
    return json.load(gzip.open(os.path.join(HERE, '..', 'results', f'k4_certs_{n}.json.gz'), 'rt'))['cores']

def main():
    lb4_run.build()
    ok = True
    with Pool(os.cpu_count()) as pool:
        for n in (2, 3):
            s = pool.map(per_core, [(r, LB4 + ' -s') for r in cores(n)])
            t = pool.map(per_core, [(r, LB4) for r in cores(n)])
            rs, rt = sum(x['rawfails'] for x in s), sum(x['rawfails'] + x['fails'] for x in t)
            print(f"(a) n={n}: -s (owner constraint ignored): {rs} profiles fail the raw check; LB4: {rt} fail")
            ok &= rs > 0 and rt == 0
        for opts in ('-i0 -u1 -o2 -r1', LB4, '-i0 -u3 -r3 -w1 -c1'):
            for n in (2, 3):
                lazy = pool.map(per_core, [(r, opts) for r in cores(n)])
                brute = pool.map(per_core, [(r, opts + ' -b') for r in cores(n)])
                same = all(a['fails'] == b['fails'] and a['total'] == b['total'] and a['rawfails'] == b['rawfails'] == 0
                           for a, b in zip(lazy, brute))      # rawfails must be 0 too: every output is EFX0 and D2
                print(f"(b) {opts}, n={n}: lazy fails {sum(a['fails'] for a in lazy)} of {sum(a['total'] for a in lazy)}, "
                      f"brute fails {sum(b['fails'] for b in brute)} of {sum(b['total'] for b in brute)}; "
                      f"equal per core: {same}")
                ok &= same
    r = subprocess.run([sys.executable, os.path.join(HERE, '..', 'attempts', 'lb4_variants.py')], capture_output=True, text=True)
    print('(c) attempts/lb4_variants.py:', r.stdout.strip().split('\n')[-1])
    ok &= r.returncode == 0
    print('ALL OK' if ok else 'FAILED')
    sys.exit(0 if ok else 1)

if __name__ == '__main__':
    main()
