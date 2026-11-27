"""Adversarial search for a counterexample to W^sub (k4/haxell.md §6): hill-climbing over instances, scored by the
checker (gstar_measure with SLACK, every partial EFX0 state with a nonempty pool of the instance).

Score of an instance (smaller is harder): (0, s) if some state has no improving single move, s the least number of
improving two-move composites at such a state; (1, r) otherwise, r the least number of improving single moves at a
state.  Score (0, 0) is a state with no W^sub step: a counterexample, which is then printed and re-checked by
gstar_measure without SLACK (phi1 > 0).  "Improving" is W^sub's notion: smaller pool, or same pool and larger welfare
(MEASURE=2: leximin).

Climb: a random instance (n agents, m goods, every agent valuing 1..k goods, every good valued by someone, values
1..VMAX); a step changes one value, or moves one good into or out of an agent's relevant set; a step is kept if the
score does not get worse; RESTART steps without strict improvement start a new instance.

    python3 k4/haxell/ht_wclimb.py n m k [STEPS=2000] [CLIMBERS=4] [VMAX=60] [RESTART=300] [SEED=1] [SUB=1] [MEASURE=1]
                                     [OFF=0]   (OFF: move kinds switched off, the bitmask of gstar_measure.c)
                                     [START="n m d g v ..."]   (every climb starts and restarts from this instance)"""
import sys, os, random, subprocess, time
import multiprocessing as mpc
HERE = os.path.dirname(os.path.abspath(__file__))


def rand_inst(rng, n, m, k, vmax):
    while True:
        R = [sorted(rng.sample(range(m), rng.randint(max(1, k - 1), k))) for _ in range(n)]
        if set().union(*map(set, R)) == set(range(m)):
            return {(i, g): rng.randint(1, vmax) for i in range(n) for g in R[i]}


def valid(V, n, m, k):
    cnt = [sum(1 for (i, g) in V if i == a) for a in range(n)]
    return all(1 <= c <= k for c in cnt) and {g for (_, g) in V} == set(range(m))


def line(V, n, m):
    parts = [str(n), str(m)]
    for i in range(n):
        gl = sorted(g for (a, g) in V if a == i)
        parts.append(str(len(gl)))
        for g in gl:
            parts += [str(g), str(V[(i, g)])]
    return ' '.join(parts)


def mutate(rng, V, n, m, k, vmax):
    while True:
        W = dict(V); r = rng.random()
        if r < 0.7:
            key = rng.choice(sorted(W))
            W[key] = max(1, min(vmax, W[key] + rng.choice([-1, 1]) * rng.choice([1, 1, 2, 5, 10]))) \
                if rng.random() < 0.6 else rng.randint(1, vmax)
        elif r < 0.85:
            i, g = rng.randrange(n), rng.randrange(m)
            if (i, g) in W:
                continue
            W[(i, g)] = rng.randint(1, vmax)
        else:
            key = rng.choice(sorted(W)); del W[key]
        if valid(W, n, m, k):
            return W


def climber(args):
    n, m, k, steps, vmax, restart, seed, sub, measure, off, start = args
    rng = random.Random(seed)
    P = subprocess.Popen([os.path.join(HERE, 'gstar_measure'), '2', '1', str(measure), str(sub), '1', '1', str(off)],
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)

    def score(V):
        P.stdin.write(line(V, n, m) + '\n'); P.stdin.flush()
        w = P.stdout.readline().split(); j = w.index('slack')
        r1min, smin = int(w[j + 1]), int(w[j + 2])
        return ((0, smin) if smin >= 0 else (1, r1min)), w
    best_overall = None; found = []
    fresh = (lambda: dict(start)) if start else (lambda: rand_inst(rng, n, m, k, vmax))
    V = fresh(); sc, _ = score(V); since = 0
    for t in range(steps):
        W = mutate(rng, V, n, m, k, vmax); sw, w = score(W)
        if sw <= sc:
            if sw < sc:
                since = 0
            V, sc = W, sw
            if sc == (0, 0):
                found.append((line(V, n, m), ' '.join(w))); best_overall = (sc, line(V, n, m))
                V = fresh(); sc, _ = score(V)
        since += 1
        if best_overall is None or sc < best_overall[0]:
            best_overall = (sc, line(V, n, m))
        if since > restart:
            V = fresh(); sc, _ = score(V); since = 0
    P.stdin.close(); P.wait()
    return seed, best_overall, found


if __name__ == '__main__':
    n, m, k = map(int, sys.argv[1:4])
    a = dict(x.split('=') for x in sys.argv[4:] if '=' in x)
    steps = int(a.get('STEPS', '2000')); C = int(a.get('CLIMBERS', '4')); vmax = int(a.get('VMAX', '60'))
    restart = int(a.get('RESTART', '300')); seed = int(a.get('SEED', '1')); sub = int(a.get('SUB', '1'))
    measure = int(a.get('MEASURE', '1')); off = int(a.get('OFF', '0'))
    start = None
    if 'START' in a:       # an instance line "n m d g v ...": every climb starts (and restarts) from it
        w = list(map(int, a['START'].split())); assert (w[0], w[1]) == (n, m); start = {}; t = 2
        for i in range(n):
            d = w[t]; t += 1
            for _ in range(d):
                start[(i, w[t])] = w[t + 1]; t += 2
        assert valid(start, n, m, k)
    print('$ python3 k4/haxell/ht_wclimb.py', *sys.argv[1:], flush=True)
    t0 = time.time(); allfound = []
    with mpc.Pool(min(C, os.cpu_count() or 1)) as pool:
        for s, best, found in pool.imap_unordered(climber, [(n, m, k, steps, vmax, restart, seed * 1000 + c, sub,
                                                               measure, off, start) for c in range(C)]):
            print('climber', s, 'hardest score', best[0], 'instance', best[1], flush=True)
            for f in found:
                print('COUNTEREXAMPLE', f[0], '|', f[1], flush=True)
            allfound += found
    for inst, _ in allfound[:5]:      # re-check without SLACK
        out = subprocess.run([os.path.join(HERE, 'gstar_measure'), '2', '1', str(measure), str(sub), '0', '0', str(off)],
                             input=inst + '\n',
                             capture_output=True, text=True).stdout.split()
        print('recheck', inst, 'phi%d stuck states' % measure, out[out.index('phi%d' % measure) + 1])
    print('counterexamples', len(allfound), 'time %.0f s' % (time.time() - t0))
