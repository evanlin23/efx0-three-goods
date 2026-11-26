"""Conjecture W (k4/haxell.md §6) on the exhaustive n = 2 grids of ht_n2k3.py: every pair of relevant sets (every good
relevant to someone, m <= 2K), every value vector from VALS (ties allowed), through gstar_measure.c with steps of at
most two moves and rotations (for n = 2 a rotation is a trade).  Reports the stuck states per measure.

    python3 k4/haxell/ht_n2w.py [K=4] [VALS=1,2,4,7]"""
import sys, os, itertools, subprocess, collections, time
HERE = os.path.dirname(os.path.abspath(__file__))
args = dict(a.split('=') for a in sys.argv[1:] if '=' in a)
K = int(args.get('K', '4')); VALS = [int(x) for x in args.get('VALS', '1,2,4,7').split(',')]
print('$ python3 k4/haxell/ht_n2w.py', *sys.argv[1:], flush=True)
t0 = time.time(); lines = []; meta = []
for m in range(2, 2 * K + 1):
    for k0 in range(1, K + 1):
        for k1 in range(1, K + 1):
            R0 = tuple(range(k0))
            for R1 in itertools.combinations(range(m), k1):
                if set(R0) | set(R1) != set(range(m)):
                    continue
                for v0 in itertools.product(VALS, repeat=k0):
                    for v1 in itertools.product(VALS, repeat=k1):
                        lines.append(' '.join(['2', str(m), str(k0)] + ['%d %d' % gv for gv in zip(R0, v0)] +
                                              [str(k1)] + ['%d %d' % gv for gv in zip(R1, v1)]))
                        meta.append((m, R0, R1, v0, v1))
print('instances', len(lines), flush=True)
# split across processes
P = os.cpu_count() or 1; chunks = [lines[i::P] for i in range(P)]; mchunks = [meta[i::P] for i in range(P)]
procs = [subprocess.Popen([os.path.join(HERE, 'gstar_measure'), '2', '1'], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          text=True) for _ in range(P)]
outs = [p.communicate('\n'.join(c) + '\n')[0] for p, c in zip(procs, chunks)]
C = collections.Counter(); shown = collections.Counter()
for out, mc in zip(outs, mchunks):
    for ln, md in zip(out.strip().split('\n'), mc):
        w = ln.split(); d = {w[2 * t + 4]: int(w[2 * t + 5]) for t in range(19)}
        C['instances'] += 1; C['partial EFX0 states'] += int(w[3])
        for key in ('phi0', 'phi1', 'phi2', 'phi5'):
            C['stuck states ' + key] += d[key]; C['instances with a stuck state ' + key] += d[key] > 0
            if d[key] and key in ('phi1', 'phi2') and shown[key] < 5:
                shown[key] += 1; print('STUCK', key, md, ln, flush=True)
for k in sorted(C):
    print(k, C[k])
print('time %.0f s' % (time.time() - t0))
