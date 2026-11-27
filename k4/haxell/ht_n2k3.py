"""CONN_1 at n = 2, k <= 3 (k4/haxell.md §4): every relevant-set shape of two agents with at most three relevant
goods each and m <= 6 goods (every good relevant to someone), with every value vector drawn from VALS^|R_i|, through
the C census gstar.c (traps of G*).  Exhaustive over the listed values, so evidence over a finite value grid only.

    python3 k4/haxell/ht_n2k3.py [K=3] [VALS=1,2,3,5,8,13]"""
import sys, os, itertools, subprocess, collections, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
args = dict(a.split('=') for a in sys.argv[1:] if '=' in a)
K = int(args.get('K', '3')); VALS = [int(x) for x in args.get('VALS', '1,2,3,5,8,13').split(',')]
print('$ python3 k4/haxell/ht_n2k3.py', *sys.argv[1:], flush=True)
t0 = time.time(); C = collections.Counter(); lines = []; meta = []
for m in range(2, 2 * K + 1):
    for k0 in range(1, K + 1):
        for k1 in range(1, K + 1):
            R0 = tuple(range(k0))                      # agent 0 values goods 0..k0-1 (WLOG)
            for R1 in itertools.combinations(range(m), k1):
                if set(R0) | set(R1) != set(range(m)):
                    continue
                for v0 in itertools.product(VALS, repeat=k0):
                    for v1 in itertools.product(VALS, repeat=k1):
                        parts = ['2', str(m), str(k0)] + [f'{g} {x}' for g, x in zip(R0, v0)] + \
                                [str(k1)] + [f'{g} {x}' for g, x in zip(R1, v1)]
                        lines.append(' '.join(parts)); meta.append((m, R0, R1, v0, v1))
print('instances', len(lines), flush=True)
out = subprocess.run([os.path.join(HERE, 'gstar')], input='\n'.join(lines) + '\n', capture_output=True, text=True).stdout
shown = 0
for ln, md in zip(out.strip().split('\n'), meta):
    w = ln.split(); d = dict(zip(w[2:12:2], map(int, w[3:12:2])))
    C['instances'] += 1; C['traps'] += d['traps']; C['instances with a trap'] += d['traps'] > 0
    C['radius-2 traps'] += d['radius2traps']; C['no complete EFX0'] += d['complete'] == 0
    if d['traps'] and shown < 10:
        shown += 1; print('TRAP', md, ln, flush=True)
for k in sorted(C):
    print(k, C[k])
print('time %.0f s' % (time.time() - t0))
