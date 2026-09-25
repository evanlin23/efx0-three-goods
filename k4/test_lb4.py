"""Tests of the LB4 tester k4/lb4.c (results/k4_lb4_test.log).
(a) Sensitivity: with -s the construction ignores the owner constraint (all junk to r). The raw EFX0 check must then
    report failures, at n = 2 and n = 3; without -s it reports none.
(b) Lazy type branching vs brute force: for a variant that fails (-i0 -u1 -o2 -r1), for LB4 itself, and for nested
    rotations (-i0 -u3 -r3 -w1 -c1, whose rotation depth must be reset after a type split), the numbers of failing
    profiles and of raw-check failures per core must be the same when every profile is its own leaf (-b), on every core
    with n <= 3.
(c) The rejected variants of attempts/lb4-*.md reproduce (attempts/lb4_variants.py).
(d) LB4r's tools (k4/lb4.md §5): iterative deepening (-d1, -d2) gives the same failures, per core, as the plain
    rotation bound, for a failing variant and for LB4r with every insertion order, n <= 3; random profiles with every
    insertion order (-i1 -S) find the failures of need-shrinking upgrades only (n = 2), none for LB4r, and stop with a
    raw-check failure (exit 2) when the owner constraint is ignored (-s); hill-climbing (-H, with -P1's check that LB4r
    succeeds whenever some policy does) runs clean on n = 3; a rotation bound above 3 (-r4, depth-first, every
    insertion order, n = 3) runs clean under AddressSanitizer and fills the histogram entry rot4, and -r9 is rejected.
Usage: python3 k4/test_lb4.py [d]      (d: part (d) only)"""
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
    t = next(l for l in p.stdout.split('\n') if l.startswith('total ')).split()   # skip the histogram line 'H ...'
    return dict(zip(t[0:22:2], map(int, t[1:22:2])))

def cores(n):
    return json.load(gzip.open(os.path.join(HERE, '..', 'results', f'k4_certs_{n}.json.gz'), 'rt'))['cores']

def part_d(pool):
    ok = True
    for opts in ('-i0 -u3 -r1 -w1 -c1', '-i1 -u3 -r3 -w1 -c1'):
        for n in (2, 3):
            res = [pool.map(per_core, [(r, opts + d) for r in cores(n)]) for d in ('', ' -d1', ' -d2')]
            same = all(a['fails'] == b['fails'] == c['fails'] and a['total'] == b['total'] == c['total']
                       and a['rawfails'] == b['rawfails'] == c['rawfails'] == 0 for a, b, c in zip(*res))
            print(f"(d) {opts}, n={n}: fails {[sum(x['fails'] for x in r) for r in res]} (plain, -d1, -d2); "
                  f"equal per core: {same}")
            ok &= same
    c2 = {'m': 5, 'sets': [[0, 2, 3, 4], [1, 2, 3, 4]]}
    a = per_core((c2, '-i1 -u1 -r3 -w1 -c1 -S20000')); b = per_core((c2, '-i1 -u3 -r3 -w1 -c1 -S20000'))
    print(f"(d) -i1 -S20000 on {c2['sets']}: need-shrinking only fails {a['fails']}, LB4r fails {b['fails']}")
    ok &= a['fails'] > 0 and b['fails'] == 0
    inp = ''.join(lb4_run.encode(r['sets'], r['m'], False) for r in cores(3))
    p = subprocess.run([lb4_run.BIN] + '-i1 -u3 -r3 -w1 -c1 -s -S200'.split(), input=inp, capture_output=True, text=True)
    print(f"(d) -i1 -S200 -s (owner constraint ignored), n=3: exit {p.returncode} ({p.stderr.split(' ')[0]})")
    ok &= p.returncode == 2 and p.stderr.startswith('RAWFAIL')
    h = pool.map(per_core, [(r, '-i1 -u3 -r3 -w1 -c1 -d1 -P1 -H500') for r in cores(3)])
    print(f"(d) -i1 -d1 -P1 -H500, n=3: {sum(x['total'] for x in h)} profiles, fails {sum(x['fails'] for x in h)}")
    ok &= sum(x['fails'] + x['rawfails'] for x in h) == 0
    import tempfile
    asan = os.path.join(tempfile.gettempdir(), 'k4_lb4_asan')
    b = subprocess.run(['gcc', '-O1', '-fsanitize=address', '-o', asan, lb4_run.SRC], capture_output=True)
    if b.returncode == 0:
        p = subprocess.run([asan] + '-i1 -u3 -r4 -w1 -c1'.split(), input=inp, capture_output=True, text=True)
        h = [list(map(int, l.split()[1:])) for l in p.stdout.split('\n') if l.startswith('H ')]
        r4 = sum(x[7] for x in h if len(x) > 7)
        print(f"(d) -r4 under AddressSanitizer, n=3: exit {p.returncode}, sanitizer reports {p.stderr.count('AddressSanitizer')}, rot4 {r4}")
        ok &= p.returncode == 0 and 'AddressSanitizer' not in p.stderr and r4 > 0
    else: print('(d) -r4 under AddressSanitizer: skipped (no -fsanitize=address)')
    p = subprocess.run([lb4_run.BIN, '-r9'], input='', capture_output=True, text=True)
    print(f"(d) -r9 rejected: {p.returncode != 0}"); ok &= p.returncode != 0
    return ok

def main():
    lb4_run.build()
    ok = True
    if sys.argv[1:] == ['d']:
        with Pool(os.cpu_count()) as pool: ok = part_d(pool)
        print('ALL OK' if ok else 'FAILED'); sys.exit(0 if ok else 1)
    with Pool(os.cpu_count()) as pool:
        ok &= part_d(pool)
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
