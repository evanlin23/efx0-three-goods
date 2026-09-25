"""Sensitivity test of k4/check_mincex_cores4.py, on the beta = 3 data (seconds per run): corrupted inputs must make it
fail. Usage (from k4/): python3 test_check_mincex_cores4.py"""
import json, gzip, subprocess, sys, os, copy, tempfile, hashlib

CERT, UNC = '../results/k4_min_cex_cores_3.json.gz', '../results/k4_min_cex_px_uncovered.json'
cert, raw = json.load(gzip.open(CERT, 'rt')), open(UNC, 'rb').read()
tmp = tempfile.mkdtemp()


def run(c, data, extra=(), real_log=True):
    pc, pu, pl = os.path.join(tmp, 'c.json.gz'), os.path.join(tmp, 'k4_min_cex_px_uncovered.json'), os.path.join(tmp, 'l.log')
    with gzip.open(pc, 'wt') as h: json.dump(c, h)
    open(pu, 'wb').write(data)
    open(pl, 'w').write('written to %s (sha256 %s)\n' % (pu, hashlib.sha256(data).hexdigest()))
    log = '../results/k4_check_min_cex_reductions.log' if real_log else pl
    return subprocess.run([sys.executable, 'check_mincex_cores4.py', '3', pc, pu, '--jobs=2', '--reductions-log=' + log]
                          + list(extra), capture_output=True, text=True)


tests = []
big = max(range(len(cert)), key=lambda i: len(cert[i]['allocs']))
c = copy.deepcopy(cert); c[big]['allocs'] = c[big]['allocs'][:-1]; tests.append(('an allocation deleted', c, raw, ()))
c = copy.deepcopy(cert); del c[0]; tests.append(('a core deleted', c, raw, ()))
c = copy.deepcopy(cert); m = c[0]['m']; c[0]['allocs'].append([0 if g < m // 2 else 1 for g in range(m)])
tests.append(('a non-D2 allocation added', c, raw, ()))
u = json.loads(raw); u['px-P4'] = u['px-P4'][:3]
tests.append(('uncovered file truncated', cert, json.dumps(u, separators=(',', ':'), sort_keys=True).encode(), ()))
c = copy.deepcopy(cert); del c[big]['allocs']; c[big]['timeout'] = 1
tests.append(('a non-graphical core without allocations, --allow-graphical', c, raw, ('--allow-graphical',)))
ok = True
r0 = run(cert, raw)
print('unmodified inputs: exit %d; summary lines of that run:' % r0.returncode)
for line in r0.stdout.splitlines():
    if line.startswith(('beta =', 'checked', 'every allocation', 'RESULT')): print('    ' + line)
ok &= r0.returncode == 0
for what, c, data, extra in tests:
    r = run(c, data, extra)
    print('%-62s exit %d (%s)' % (what, r.returncode, 'rejected' if r.returncode else 'NOT REJECTED'))
    ok &= r.returncode != 0
print('RESULT: %s' % ('OK' if ok else 'FAILED'))
sys.exit(0 if ok else 1)
