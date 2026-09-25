"""Sensitivity test of k4/check_mincex_cores.py: corrupted inputs must make it fail (nonzero exit status).
Each run gets a temporary reductions log recording the SHA-256 of the uncovered-profile file it is given, except the
truncated-file test, which keeps the real log. Usage (from k4/): python3 test_check_mincex_cores.py"""
import json, gzip, subprocess, sys, os, copy, tempfile, hashlib, itertools

CERT, UNC = '../results/k4_min_cex_cores_3.json.gz', '../results/k4_min_cex_px_uncovered.json'
LOG = '../results/k4_check_min_cex_reductions.log'
cert, raw = json.load(gzip.open(CERT, 'rt')), open(UNC, 'rb').read()
unc = json.loads(raw)
tmp = tempfile.mkdtemp()


def run(c, data, real_log=False):
    pc, pu, pl = os.path.join(tmp, 'c.json.gz'), os.path.join(tmp, 'k4_min_cex_px_uncovered.json'), os.path.join(tmp, 'l.log')
    with gzip.open(pc, 'wt') as h: json.dump(c, h)
    open(pu, 'wb').write(data)
    open(pl, 'w').write('written to %s (sha256 %s)\n' % (pu, hashlib.sha256(data).hexdigest()))
    return subprocess.run([sys.executable, 'check_mincex_cores.py', '3', pc, pu, '--reductions-log=' + (LOG if real_log else pl)],
                          capture_output=True, text=True)


tests = []
big = max(range(len(cert)), key=lambda i: len(cert[i]['allocs']))
c = copy.deepcopy(cert); c[big]['allocs'] = c[big]['allocs'][:-1]; tests.append(('an allocation deleted', c, raw, False))
c = copy.deepcopy(cert); del c[0]; tests.append(('a core deleted', c, raw, False))
c = copy.deepcopy(cert); A = c[0]['allocs'][0]; c[0]['allocs'][0] = [A[0]] * len(A)
tests.append(('an allocation replaced by all goods to one agent', c, raw, False))
c = copy.deepcopy(cert); m = c[0]['m']; c[0]['allocs'].append([0 if g < m // 2 else 1 for g in range(m)])
tests.append(('a non-D2 allocation added (two bundles of > 2 goods)', c, raw, False))
T3 = list(itertools.permutations((4, 3, 2)))
u = copy.deepcopy(unc)
u['px-Q3-closed'] = [{'e': dict(zip(('g', 'y', 'b'), te)), 'f': dict(zip(('g', 'y', 'pf'), tf))} for te in T3 for tf in T3]
tests.append(('px-Q3-closed uncovered set: all 36 profiles', cert, json.dumps(u).encode(), False))
u = copy.deepcopy(unc); u['px-P4'] = u['px-P4'][:5]
tests.append(('uncovered file truncated (real reductions log)', cert, json.dumps(u, separators=(',', ':'), sort_keys=True).encode(), True))
ok = True
r0 = run(cert, raw, real_log=True)
print('unmodified inputs (real reductions log): exit %d' % r0.returncode)
ok &= r0.returncode == 0
for what, c, data, real in tests:
    r = run(c, data, real)
    print('%-55s exit %d (%s)' % (what, r.returncode, 'rejected' if r.returncode else 'NOT REJECTED'))
    ok &= r.returncode != 0
print('RESULT: %s' % ('OK' if ok else 'FAILED'))
sys.exit(0 if ok else 1)
