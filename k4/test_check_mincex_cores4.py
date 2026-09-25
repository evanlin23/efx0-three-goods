"""Sensitivity test of k4/check_mincex_cores4.py, on the beta = 3 data (seconds per run): each corrupted input must make
it fail, and for the expected reason (the message it prints), so a crash does not count as a rejection.
Usage (from k4/): python3 test_check_mincex_cores4.py"""
import json, gzip, subprocess, sys, os, copy, tempfile, hashlib, itertools

CERT, UNC = '../results/k4_min_cex_cores_3.json.gz', '../results/k4_min_cex_px_uncovered.json'
cert, raw = json.load(gzip.open(CERT, 'rt')), open(UNC, 'rb').read()
tmp = tempfile.mkdtemp()
EXPECT = ['--expect=9', '--expect-n=5:2,6:7', '--expect-graphical=0']


def run(c, data, extra=(), real_log=True):
    pc, pu, pl = os.path.join(tmp, 'c.json.gz'), os.path.join(tmp, 'k4_min_cex_px_uncovered.json'), os.path.join(tmp, 'l.log')
    with gzip.open(pc, 'wt') as h: json.dump(c, h)
    open(pu, 'wb').write(data)
    open(pl, 'w').write('written to %s (sha256 %s)\n' % (pu, hashlib.sha256(data).hexdigest()))
    log = '../results/k4_check_min_cex_reductions.log' if real_log else pl
    return subprocess.run([sys.executable, 'check_mincex_cores4.py', '3', pc, pu, '--jobs=2', '--reductions-log=' + log]
                          + list(extra), capture_output=True, text=True)


tests = []                                                  # (what, certificate, uncovered file, extra args, real log, message)
big = max(range(len(cert)), key=lambda i: len(cert[i]['allocs']))
c = copy.deepcopy(cert); c[big]['allocs'] = c[big]['allocs'][:-1]
tests.append(('an allocation deleted', c, raw, EXPECT, True, 'UNCOVERED profiles'))
c = copy.deepcopy(cert); del c[0]
tests.append(('a core deleted', c, raw, [], True, 'no isomorphic core in the certificate'))
c = copy.deepcopy(cert); m = c[0]['m']; c[0]['allocs'].append([0 if g < m // 2 else 1 for g in range(m)])
tests.append(('a non-D2 allocation added', c, raw, EXPECT, True, '(D2): False'))
u = json.loads(raw); u['px-P4'] = u['px-P4'][:3]
tests.append(('uncovered file truncated (real reductions log)', cert, json.dumps(u, separators=(',', ':'), sort_keys=True).encode(),
              [], True, 'DOES NOT MATCH'))
c = copy.deepcopy(cert); del c[big]['allocs']; c[big]['timeout'] = 1
tests.append(('a non-graphical core without allocations, --allow-graphical', c, raw, ['--allow-graphical'], True,
              'not certified (timeout)'))
T3 = list(itertools.permutations((4, 3, 2)))
u = json.loads(raw)
u['px-Q3-closed'] = [{'e': dict(zip(('g', 'y', 'b'), te)), 'f': dict(zip(('g', 'y', 'pf'), tf))} for te in T3 for tf in T3]
tests.append(('px-Q3-closed uncovered set enlarged (matching SHA-256)', cert, json.dumps(u).encode(), [], False,
              'no isomorphic core in the certificate'))
# an allocation that is EFX (the removed good must be valued by the envier) but not EFX0 for the 40-profile core:
# found by searching single-good moves from its certified allocation (every agent EFX-safe under every type of its
# domain, some agent-type not EFX0-safe)
c = copy.deepcopy(cert); k40 = next(i for i, r in enumerate(c) if r['profiles'] == 40)
c[k40]['allocs'] = [[0, 0, 3, 0, 2, 1, 4, 0, 3, 2, 5]]
tests.append(('an allocation list that is EFX but not EFX0', c, raw, [], True, 'UNCOVERED profiles'))
c = copy.deepcopy(cert); c[0]['allocs'][0] = [c[0]['n']] + c[0]['allocs'][0][1:]
tests.append(('a record with an owner index >= n', c, raw, [], True, 'MALFORMED certificate record'))
ok = True
r0 = run(cert, raw, EXPECT)
print('unmodified inputs (%s): exit %d; summary lines of that run:' % (' '.join(EXPECT), r0.returncode))
for line in r0.stdout.splitlines():
    if line.startswith(('beta =', 'left per n', 'checked', 'every allocation', 'RESULT')): print('    ' + line)
ok &= r0.returncode == 0
for what, c, data, extra, real, msg in tests:
    r = run(c, data, extra, real)
    hit = msg in r.stdout and 'Traceback' not in r.stderr
    print('%-62s exit %d, %s' % (what, r.returncode, ('rejected: "%s"' % msg) if r.returncode and hit else
                                 'NOT REJECTED AS EXPECTED'))
    ok &= r.returncode != 0 and hit
print('RESULT: %s' % ('OK' if ok else 'FAILED'))
sys.exit(0 if ok else 1)
