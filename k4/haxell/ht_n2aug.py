"""The n = 2 grid of ht_n2w.py, scanned for states where no composite of at most two moves (set moves, k4/haxell.md §6)
shrinks the pool (phi0 of gstar_measure 2 1 0 1): prints the first SHOW such instances with a state.  Used for the n = 2
proof attempt (k4/haxell.md §6): which instances need a non-augmenting step at all.

    python3 k4/haxell/ht_n2aug.py [K=4] [VALS=1,2,4,7] [SHOW=12] [PROCS=2]"""
import sys, os, itertools, subprocess, collections, time, threading
HERE = os.path.dirname(os.path.abspath(__file__))
args = dict(a.split('=') for a in sys.argv[1:] if '=' in a)
K = int(args.get('K', '4')); VALS = [int(x) for x in args.get('VALS', '1,2,4,7').split(',')]
SHOW = int(args.get('SHOW', '12')); P = int(args.get('PROCS', '2'))
print('$ python3 k4/haxell/ht_n2aug.py', *sys.argv[1:], flush=True)
t0 = time.time()
procs = [subprocess.Popen([os.path.join(HERE, 'gstar_measure'), '2', '1', '0', '1'], stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE, text=True, bufsize=1 << 16) for _ in range(P)]
sent = [collections.deque() for _ in range(P)]; lock = threading.Lock(); C = collections.Counter(); shown = [0]
def reader(k):
    for ln in procs[k].stdout:
        w = ln.split()
        with lock:
            src = sent[k].popleft(); C['instances'] += 1; C['states'] += int(w[3])
            s0 = int(w[5]); C['phi0 stuck states'] += s0; C['phi0 instances'] += s0 > 0
            if s0 and shown[0] < SHOW:
                shown[0] += 1; print('AUGSTUCK', src, '|', ln.strip(), flush=True)
ths = [threading.Thread(target=reader, args=(k,)) for k in range(P)]
for th in ths:
    th.start()
t = 0
for m in range(2, 2 * K + 1):
    for k0 in range(1, K + 1):
        for k1 in range(1, K + 1):
            R0 = tuple(range(k0))
            for R1 in itertools.combinations(range(m), k1):
                if set(R0) | set(R1) != set(range(m)):
                    continue
                for v0 in itertools.product(VALS, repeat=k0):
                    for v1 in itertools.product(VALS, repeat=k1):
                        ln = ' '.join(['2', str(m), str(k0)] + ['%d %d' % gv for gv in zip(R0, v0)] +
                                      [str(k1)] + ['%d %d' % gv for gv in zip(R1, v1)])
                        k = t % P
                        with lock:
                            sent[k].append(ln)
                        procs[k].stdin.write(ln + '\n'); t += 1
for p in procs:
    p.stdin.close()
for th in ths:
    th.join()
for key in sorted(C):
    print(key, C[key])
print('time %.0f s' % (time.time() - t0))
