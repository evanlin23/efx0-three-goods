"""The Pareto form of the set-move lemma (P^sub, k4/haxell.md §6) at n = 3 over every strict type profile.

P^sub is ordinal: pool-shrinking and "no agent worse, some agent strictly better" compare, for each agent, two sets of
its goods, which a strict type decides.  So running every strict type profile once (its integer representatives as
values) is a complete check for strict values.

Shapes are those of ht_n3grid.py: a multiset of patterns (the set of agents valuing a good), every agent valuing 1..K
goods, up to agent permutations.  A profile gives each agent a strict type on its goods.  Goods of one pattern are
interchangeable; the first agent of the pattern values them distinctly, so every orbit has exactly one profile in which
that agent's values increase along the pattern's goods, and only those are run (agent permutations fixing the shape are
not factored out: extra work, not missing work).  Each instance goes to gstar_measure RADIUS 1 19 1 (Pareto, set moves).

    python3 k4/haxell/ht_n3types.py [K=3] [MMIN=2] [MMAX=9] [RADIUS=2] [PROCS=2] [MEASURE=19] [SAMPLE=0] [SEED=1] [NEED4=0]
SAMPLE=N runs N uniformly random profiles per shape instead of every orbit (each one an exact test of its profile; the
sample is what makes it evidence).  NEED4=1 skips the shapes in which no agent values four goods.  MEASURE=20 is
measure Q of gstar_measure (a Pareto step within two moves, or a smaller pool within RADIUS)."""
import sys, os, json, itertools, subprocess, collections, threading, time, random
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.join(HERE, '..', '..')
ARGV = sys.argv[1:]; args = dict(a.split('=') for a in ARGV if '=' in a)
K = int(args.get('K', '3')); MMIN = int(args.get('MMIN', '2')); MMAX = int(args.get('MMAX', '9'))
RADIUS = args.get('RADIUS', '2'); P = int(args.get('PROCS', '2')); MEAS = args.get('MEASURE', '19')
SAMPLE = int(args.get('SAMPLE', '0')); SEED = int(args.get('SEED', '1')); NEED4 = int(args.get('NEED4', '0'))
OT = json.load(open(os.path.join(ROOT, 'k4', 'order_types.json')))
TYPES = {1: [(1,)], 2: [(1, 2), (2, 1)]}
for k in (3, 4):
    TYPES[k] = [tuple(t['rep']) for t in OT[str(k)]['types'] if t['strict']]
sys.argv = ['x', 'K=%d' % K, 'MMIN=%d' % MMIN, 'MMAX=%d' % MMAX]
sys.path.insert(0, HERE)
import ht_n3grid as G          # shapes() (reads K, MMIN, MMAX from the argv set above)


RNG = random.Random(SEED)


def instances(m, key):
    R = [[g for g, p in enumerate(key) if a in p] for a in range(3)]
    firsts = collections.defaultdict(list)          # pattern -> its goods; the first agent of the pattern orders them
    for g, p in enumerate(key):
        firsts[p].append(g)
    if SAMPLE:
        profs = ([RNG.choice(TYPES[len(Ri)]) for Ri in R] for _ in range(SAMPLE))
    else:
        profs = itertools.product(*[TYPES[len(Ri)] for Ri in R])
    for prof in profs:
        val = [dict(zip(Ri, t)) for Ri, t in zip(R, prof)]
        if SAMPLE or all(all(val[p[0]][x] < val[p[0]][y] for x, y in zip(gs, gs[1:])) for p, gs in firsts.items()):
            parts = ['3', str(m)]
            for a in range(3):
                parts.append(str(len(R[a])))
                for g in R[a]:
                    parts += [str(g), str(val[a][g])]
            yield ' '.join(parts)


if __name__ == '__main__':
    print('$ python3 k4/haxell/ht_n3types.py', *ARGV, flush=True)
    t0 = time.time(); C = collections.Counter(); lock = threading.Lock()
    procs = [subprocess.Popen([os.path.join(HERE, 'gstar_measure'), RADIUS, '1', MEAS, '1'], stdin=subprocess.PIPE,
                              stdout=subprocess.PIPE, text=True, bufsize=1 << 16) for _ in range(P)]
    sent = [collections.deque() for _ in range(P)]

    def reader(k):
        for ln in procs[k].stdout:
            w = ln.split()
            with lock:
                src = sent[k].popleft(); C['instances'] += 1; C['instances m=%s' % w[1]] += 1
                C['partial EFX0 states'] += int(w[3])
                d = {w[i]: int(w[i + 1]) for i in range(4, len(w) - 1, 2) if w[i].startswith('phi')}
                C['phi0 stuck states'] += d['phi0']; C['phi%s stuck states' % MEAS] += d['phi' + MEAS]
                C['instances with a phi%s-stuck state' % MEAS] += d['phi' + MEAS] > 0
                if d['phi' + MEAS] and C['shown'] < 20:
                    C['shown'] += 1; print('STUCK', src, '|', ln.strip(), flush=True)
    ths = [threading.Thread(target=reader, args=(k,)) for k in range(P)]
    for th in ths:
        th.start()
    t = 0; ns = 0
    for m, key in G.shapes():
        if NEED4 and max(sum(a in p for p in key) for a in range(3)) < 4:
            continue
        ns += 1
        for ln in instances(m, key):
            k = t % P
            with lock:
                sent[k].append(ln)
            procs[k].stdin.write(ln + '\n'); t += 1
    for p in procs:
        p.stdin.close()
    for th in ths:
        th.join()
    print('shapes', ns, 'instances sent', t, 'return codes', [p.wait() for p in procs])
    for key in sorted(C):
        if key != 'shown':
            print(key, C[key])
    print('time %.0f s' % (time.time() - t0))
