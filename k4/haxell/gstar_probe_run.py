"""Driver for gstar_probe.c (k4/haxell.md §5): start-based test of CONN_2 on instances too large for the full census.
Starts: the serial-dictatorship picks of every order (n <= NALL) or of ORDERS sampled orders (always including the
identity and its reverse), each a partial EFX0 allocation; from each, WALK random walks of LEN EFX0-preserving single
moves add probe states.  Every probe is searched in G_2 (gstar_probe.c); a probe whose search space is exhausted
without a complete EFX0 allocation is a trap and refutes CONN_2.

    cc -O2 -o k4/haxell/gstar_probe k4/haxell/gstar_probe.c
    python3 k4/haxell/gstar_probe_run.py SRC [CAP=3000] [WALK=4] [LEN=6] [ORDERS=40] [NALL=6] [RADIUS=2]"""
import sys, os, subprocess, itertools, random, collections, json, time
import multiprocessing as mpc
from functools import partial
from ht_lib import Inst, instances, sd
from gstar_run import line
HERE = os.path.dirname(os.path.abspath(__file__))


def starts(sets, vals, m, norders, nall, rng):
    I = Inst(sets, vals, m); n = len(sets)
    if n <= nall:
        orders = itertools.permutations(range(n))
    else:
        orders = [tuple(range(n)), tuple(range(n))[::-1]]
        while len(orders) < norders:
            o = list(range(n)); rng.shuffle(o); orders.append(tuple(o))
    seen = set(); out = []
    for o in orders:
        Y = tuple(sd(I, list(o))[0])
        if Y in seen:
            continue
        seen.add(Y)
        own = [-1] * m
        for i, g in enumerate(Y):
            if g is not None:
                own[g] = i
        out.append(own)
    return out


def job(item, cap, walk, ln, norders, nall, radius):
    name, sets, vals, m = item
    rng = random.Random(hash(name) & 0xffffffff)
    S = starts(sets, vals, m, norders, nall, rng)
    inp = line(sets, vals, m) + ' S %d ' % len(S) + ' '.join(' '.join(map(str, s)) for s in S) + '\n'
    out = subprocess.run([os.path.join(HERE, 'gstar_probe'), str(cap), str(walk), str(ln), str(rng.randrange(10**6)),
                          str(radius)], input=inp, capture_output=True, text=True).stdout
    traps = [l for l in out.split('\n') if l.startswith('TRAP')]
    summ = [l for l in out.split('\n') if l.startswith('instance')]
    d = dict(zip(summ[0].split()[5::2], map(int, summ[0].split()[6::2]))) if summ else {}
    return name, sets, vals, m, len(S), d, traps


if __name__ == '__main__':
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    src = sys.argv[1]
    cap = int(args.get('CAP', '3000')); walk = int(args.get('WALK', '4')); ln = int(args.get('LEN', '6'))
    norders = int(args.get('ORDERS', '40')); nall = int(args.get('NALL', '6')); radius = int(args.get('RADIUS', '2'))
    print('$ python3 k4/haxell/gstar_probe_run.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter()
    items = instances(src)
    with mpc.Pool(os.cpu_count()) as pool:
        for name, sets, vals, m, ns, d, traps in pool.imap_unordered(
                partial(job, cap=cap, walk=walk, ln=ln, norders=norders, nall=nall, radius=radius), items):
            k = max(len(s) for s in sets)
            C['instances'] += 1; C['starts'] += ns
            for key in ('probes', 'reached', 'traps', 'cap'):
                C['probes ' + key if key != 'probes' else 'probes'] += d.get(key, 0)
            print('%-14s n %d m %2d k %d starts %3d probes %4d reached %4d traps %d cap %d max_expanded %d' % (
                name, len(sets), m, k, ns, d.get('probes', 0), d.get('reached', 0), d.get('traps', 0), d.get('cap', 0),
                d.get('max_expanded', 0)), flush=True)
            for t in traps[:3]:
                print('  TRAP', name, json.dumps((sets, vals)), t, flush=True)
    for key in sorted(C):
        print(key, C[key])
    print('time %.0f s' % (time.time() - t0))
