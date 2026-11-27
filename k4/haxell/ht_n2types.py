"""Claim A2 at n = 2 over every strict type profile (k4/haxell.md §6): with two agents, every agent valuing at most K <= 4
goods, every good valued by someone, and strict values, does every partial EFX0 allocation with a nonempty pool have a
composite of at most two moves (set transfers, swaps, the trade) that shrinks the pool?

Why types suffice.  Pool-shrinking involves no measure, and EFX0 compares an agent's own bundle with part of another
bundle: two disjoint sets of its goods.  A strict type fixes every such comparison (k4/order_types.py), so the answer
depends only on the type profile, and any realization (the types' integer representatives here) gives it.

Enumeration.  Agent A values goods 0..kA-1, agent B any kB of the m goods such that every good is valued by someone.
Goods valued only by A, by both, or only by B are interchangeable within their class, and a strict type orders single
goods strictly.  So every orbit has exactly one profile whose A-values increase on A-only goods and on shared goods,
and whose B-values increase on B-only goods; only those profiles are run.  Each instance goes to gstar_measure 2 1 0 1
(phi0: states with no pool-shrinking composite of two moves); any failure is printed.  At each failing state, a single
swap of two agents' goods that keeps EFX0 and raises both agents is searched (Theorem N2 of k4/haxell.md §6).  CHECK=N
re-runs N random instances (CHECK=-1: all) through the independent Python checker of ht_n2claim.py.

    python3 k4/haxell/ht_n2types.py [K=4] [PROCS=2] [CHECK=0] [JUNK=0]   (CHECK=-1: re-check every instance in Python;
                                                                       JUNK=j: add j goods valued by nobody)"""
import sys, os, json, itertools, subprocess, collections, threading, time, random
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.join(HERE, '..', '..')
args = dict(a.split('=') for a in sys.argv[1:] if '=' in a)
K = int(args.get('K', '4')); P = int(args.get('PROCS', '2')); CHECK = int(args.get('CHECK', '0'))
JUNK = int(args.get('JUNK', '0'))      # goods valued by nobody, added to every class (all interchangeable)
OT = json.load(open(os.path.join(ROOT, 'k4', 'order_types.json')))
TYPES = {1: [(1,)], 2: [(1, 2), (2, 1)]}
for k in (3, 4):
    TYPES[k] = [tuple(t['rep']) for t in OT[str(k)]['types'] if t['strict']]
assert [len(TYPES[k]) for k in (1, 2, 3, 4)] == [1, 2, 12, 336]


def increasing(vals):
    return all(x < y for x, y in zip(vals, vals[1:]))


def instances():
    for kA in range(1, K + 1):
        for kB in range(1, K + 1):
            for m in range(max(kA, kB), kA + kB + 1):
                shared_n = kA + kB - m
                RA = list(range(kA))
                for shared in itertools.combinations(RA, shared_n):
                    RB = sorted(set(shared) | set(range(kA, m)))
                    aonly = [g for g in RA if g not in shared]; bonly = list(range(kA, m))
                    if aonly != list(range(len(aonly))) or list(shared) != list(range(len(aonly), kA)):
                        continue        # one labelling per shape: A-only goods first, then the shared goods
                    for tA in TYPES[kA]:
                        vA = dict(zip(RA, tA))
                        if not (increasing([vA[g] for g in aonly]) and increasing([vA[g] for g in shared])):
                            continue
                        for tB in TYPES[kB]:
                            vB = dict(zip(RB, tB))
                            if not increasing([vB[g] for g in bonly]):
                                continue
                            yield m + JUNK, vA, vB


def line(m, vA, vB):
    return ' '.join(['2', str(m), str(len(vA))] + ['%d %d' % gv for gv in sorted(vA.items())] +
                    [str(len(vB))] + ['%d %d' % gv for gv in sorted(vB.items())])


if __name__ == '__main__':
    print('$ python3 k4/haxell/ht_n2types.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); lock = threading.Lock()
    procs = [subprocess.Popen([os.path.join(HERE, 'gstar_measure'), '2', '1', '0', '1'], stdin=subprocess.PIPE,
                              stdout=subprocess.PIPE, text=True, bufsize=1 << 16) for _ in range(P)]
    sent = [collections.deque() for _ in range(P)]; fails = []

    def reader(k):
        for ln in procs[k].stdout:
            w = ln.split()
            with lock:
                src = sent[k].popleft(); C['instances'] += 1; C['instances m=%s' % w[1]] += 1
                C['partial EFX0 states'] += int(w[3]); s0 = int(w[5]); C['phi0 stuck states'] += s0
                if s0:
                    fails.append(src); print('FAIL', src, '|', ln.strip(), flush=True)
    ths = [threading.Thread(target=reader, args=(k,)) for k in range(P)]
    for th in ths:
        th.start()
    allinst = []; t = 0
    for m, vA, vB in instances():
        ln = line(m, vA, vB); k = t % P
        with lock:
            sent[k].append(ln)
        procs[k].stdin.write(ln + '\n'); t += 1
        if CHECK:
            allinst.append((m, vA, vB))
    for p in procs:
        p.stdin.close()
    for th in ths:
        th.join()
    print('instances sent', t, 'return codes', [p.wait() for p in procs])
    for key in sorted(C):
        print(key, C[key])
    print('instances with a failure:', len(fails))
    # Theorem N2 (k4/haxell.md §6): at every state without a pool-shrinking composite, some single swap of two agents'
    # goods keeps EFX0 and raises both agents (type-determined: EFX0 is ordinal, and the check uses strict gains).
    sys.argv = ['x']; sys.path.insert(0, HERE)
    import ht_n2claim as H
    nstates = npareto = 0
    for src in fails:
        w = list(map(int, src.split())); m = w[1]; t = 2; v = []
        for i in range(2):
            d = w[t]; t += 1; r = {w[t + 2 * j]: w[t + 2 * j + 1] for j in range(d)}; t += 2 * d
            v.append([r.get(g, 0) for g in range(m)])
        for own in itertools.product((0, 1, -1), repeat=m):
            if -1 not in own:
                continue
            XA = [g for g in range(m) if own[g] == 0]; XB = [g for g in range(m) if own[g] == 1]
            if not H.ok(v[0], v[1], XA, XB) or H.augment(v[0], v[1], own, m) is not None:
                continue
            nstates += 1; found = None
            for a, b in itertools.product(XA, XB):
                YA = [g for g in XA if g != a] + [b]; YB = [g for g in XB if g != b] + [a]
                if H.ok(v[0], v[1], YA, YB) and v[0][b] > v[0][a] and v[1][a] > v[1][b]:
                    found = (a, b); break
            npareto += found is not None
            print('  no pool-shrinking composite:', src, 'state A', XA, 'B', XB, '| Pareto swap', found, flush=True)
    print('states without a pool-shrinking composite: %d; with a swap that keeps EFX0 and raises both agents: %d' %
          (nstates, npareto))
    if CHECK:            # independent re-check (ht_n2claim.augment, pure Python) of random instances
        sys.argv = ['x']; sys.path.insert(0, HERE)
        import ht_n2claim as H
        rng = random.Random(1); bad = 0; states = 0
        chosen = allinst if CHECK < 0 else rng.sample(allinst, min(CHECK, len(allinst)))
        for m, vA, vB in chosen:
            a = [vA.get(g, 0) for g in range(m)]; b = [vB.get(g, 0) for g in range(m)]
            for own in itertools.product((0, 1, -1), repeat=m):
                if -1 not in own:
                    continue
                XA = [g for g in range(m) if own[g] == 0]; XB = [g for g in range(m) if own[g] == 1]
                if not H.ok(a, b, XA, XB):
                    continue
                states += 1
                if H.augment(a, b, own, m) is None:
                    bad += 1; print('PYTHON FAIL', line(m, vA, vB), own, flush=True)
        print('python re-check: %d instances, %d partial EFX0 states with a nonempty pool, %d failures' %
              (len(chosen), states, bad))
    print('time %.0f s' % (time.time() - t0))
