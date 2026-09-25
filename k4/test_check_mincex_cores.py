"""Sensitivity test of k4/check_mincex_cores.py: corrupted inputs must make it fail (nonzero exit status).
Usage (from k4/): python3 test_check_mincex_cores.py"""
import json, gzip, subprocess, sys, os, copy, tempfile

CERT, FAIL = '../results/k4_min_cex_cores_3.json.gz', '../results/k4_min_cex_px_fail.json'
cert, fail = json.load(gzip.open(CERT, 'rt')), json.load(open(FAIL))
tmp = tempfile.mkdtemp()


def run(c, f):
    pc, pf = os.path.join(tmp, 'c.json.gz'), os.path.join(tmp, 'f.json')
    with gzip.open(pc, 'wt') as h: json.dump(c, h)
    json.dump(f, open(pf, 'w'))
    return subprocess.run([sys.executable, 'check_mincex_cores.py', '3', pc, pf], capture_output=True, text=True)


tests = []
big = max(range(len(cert)), key=lambda i: len(cert[i]['allocs']))
c = copy.deepcopy(cert); c[big]['allocs'] = c[big]['allocs'][:-1]; tests.append(('an allocation deleted', c, fail))
c = copy.deepcopy(cert); del c[0]; tests.append(('a core deleted', c, fail))
c = copy.deepcopy(cert); A = c[0]['allocs'][0]; c[0]['allocs'][0] = [A[0]] * len(A)
tests.append(('an allocation replaced by all goods to one agent', c, fail))
import itertools
T3 = list(itertools.permutations((4, 3, 2)))
f = copy.deepcopy(fail)
f['px-Q3-closed'] = [{'e': dict(zip(('g', 'y', 'b'), te)), 'f': dict(zip(('g', 'y', 'pf'), tf))} for te in T3 for tf in T3]
tests.append(('px-Q3-closed failing set: all 36 profiles', cert, f))
ok = True
r0 = run(cert, fail)
print('unmodified inputs: exit %d' % r0.returncode)
ok &= r0.returncode == 0
for what, c, f in tests:
    r = run(c, f)
    print('%-50s exit %d (%s)' % (what, r.returncode, 'rejected' if r.returncode else 'NOT REJECTED'))
    ok &= r.returncode != 0
print('RESULT: %s' % ('OK' if ok else 'FAILED'))
sys.exit(0 if ok else 1)
