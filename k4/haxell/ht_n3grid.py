"""Exhaustive n = 3 value grids for the one-step lemmas (k4/haxell.md §6), through gstar_measure.c.

A good's *pattern* is the set of agents that value it (a nonempty subset of {0, 1, 2}).  A *shape* is a multiset of
patterns, m goods in all, every agent valuing between 1 and K goods; shapes are taken up to permutations of the agents.
An instance of a shape gives every (agent, relevant good) pair a value from VALS.  Goods of the same pattern are
interchangeable, so an instance is a multiset of value tuples per pattern; and two instances that an agent permutation
fixing the shape maps onto each other are the same instance up to isomorphism, so only the lexicographically least
image is kept.  Every instance is then sent to gstar_measure, which checks every partial EFX0 allocation with a
nonempty pool.

    python3 k4/haxell/ht_n3grid.py [K=3] [MMIN=2] [MMAX=6] [VALS=1,2,4,7] [MARGS=2,1,1,1] [PROCS=4]
MARGS are gstar_measure's arguments RADIUS, ROT, ONLY, SUB: 2,1,1,1 is W^sub (welfare, phi1); 2,1,2,1 is W^sub with
leximin (phi2); 2,1,1,0 is W; 3,1,1,0 is W_3.  phi0 counts the states with no augmenting step at all."""
import sys, os, itertools, subprocess, collections, time, threading
HERE = os.path.dirname(os.path.abspath(__file__))
args = dict(a.split('=') for a in sys.argv[1:] if '=' in a)
K = int(args.get('K', '3')); MMIN = int(args.get('MMIN', '2')); MMAX = int(args.get('MMAX', '6'))
VALS = [int(x) for x in args.get('VALS', '1,2,4,7').split(',')]
MARGS = args.get('MARGS', '2,1,1,1').split(','); P = int(args.get('PROCS', '4'))
ONLY = int(MARGS[2]) if len(MARGS) > 2 else -1
PATS = [p for r in (1, 2, 3) for p in itertools.combinations(range(3), r)]
PERMS = list(itertools.permutations(range(3)))


def canon_shape(pats):
    return min(tuple(sorted(tuple(sorted(perm[a] for a in p)) for p in pats)) for perm in PERMS)


def shapes():
    seen = set()
    for m in range(MMIN, MMAX + 1):
        for combo in itertools.combinations_with_replacement(range(len(PATS)), m):
            deg = [sum(1 for c in combo if a in PATS[c]) for a in range(3)]
            if not all(1 <= d <= K for d in deg):
                continue
            key = canon_shape([PATS[c] for c in combo])
            if key in seen:
                continue
            seen.add(key)
            yield m, key


def instances(key):
    """yields (goods, line): goods is the sorted tuple of (pattern, value tuple in pattern order)"""
    classes = sorted(collections.Counter(key).items())
    autos = [perm for perm in PERMS if canon_shape(key) == tuple(sorted(tuple(sorted(perm[a] for a in p)) for p in key))]
    autos = [perm for perm in autos if perm != (0, 1, 2)]
    per_class = [list(itertools.combinations_with_replacement(list(itertools.product(VALS, repeat=len(p))), c))
                 for p, c in classes]
    for choice in itertools.product(*per_class):
        goods = tuple((p, vt) for (p, c), vts in zip(classes, choice) for vt in vts)
        ok = True
        for perm in autos:
            img = []
            for p, vt in goods:
                q = tuple(sorted(perm[a] for a in p)); d = {perm[a]: x for a, x in zip(p, vt)}
                img.append((q, tuple(d[a] for a in q)))
            if tuple(sorted(img)) < goods:
                ok = False; break
        if not ok:
            continue
        parts = ['3', str(len(goods))]
        for a in range(3):
            gl = [(g, vt[p.index(a)]) for g, (p, vt) in enumerate(goods) if a in p]
            parts.append(str(len(gl)))
            for g, x in gl:
                parts += [str(g), str(x)]
        yield goods, ' '.join(parts)


if __name__ == '__main__':
    print('$ python3 k4/haxell/ht_n3grid.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); examples = []
    phis = ['phi0'] + (['phi%d' % ONLY] if ONLY > 0 else ['phi1', 'phi2'])
    procs = [subprocess.Popen([os.path.join(HERE, 'gstar_measure')] + MARGS, stdin=subprocess.PIPE,
                              stdout=subprocess.PIPE, text=True, bufsize=1 << 16) for _ in range(P)]
    sent = [collections.deque() for _ in range(P)]
    lock = threading.Lock()

    def reader(k):
        for ln in procs[k].stdout:
            w = ln.split()
            with lock:
                src = sent[k].popleft()
            d = {w[2 * t + 4]: int(w[2 * t + 5]) for t in range(19)}
            with lock:
                C['instances'] += 1; C['partial EFX0 states'] += int(w[3]); C['instances m=%s' % w[1]] += 1
                for key in phis:
                    C['stuck states ' + key] += d[key]; C['instances with a stuck state ' + key] += d[key] > 0
                if any(d[key] for key in phis[1:]) and len(examples) < 30:
                    examples.append((src, ln.strip()))
                    print('STUCK', src, '|', ln.strip(), flush=True)
    threads = [threading.Thread(target=reader, args=(k,)) for k in range(P)]
    for th in threads:
        th.start()
    ns = 0; t = 0
    for m, key in shapes():
        ns += 1
        for goods, ln in instances(key):
            k = t % P
            with lock:
                sent[k].append(ln)
            procs[k].stdin.write(ln + '\n'); t += 1
    for p in procs:
        p.stdin.close()
    for th in threads:
        th.join()
    rc = [p.wait() for p in procs]
    print('shapes', ns, 'instances sent', t, 'return codes', rc)
    for key in sorted(C):
        print(key, C[key])
    print('time %.0f s' % (time.time() - t0))
