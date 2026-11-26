"""Driver for gstar_measure.c (k4/haxell.md §6): counts, for each candidate measure phi, the partial EFX0 allocations
with a nonempty pool from which no step of at most two local moves lowers (|pool|, phi).

    cc -O2 -o k4/haxell/gstar_measure k4/haxell/gstar_measure.c
    python3 k4/haxell/gstar_measure_run.py SRC [NMAX=4] [MMAX=7] [MAXSTATES=400000] [RADIUS=2|3] [ROT=0|1]"""
import sys, os, subprocess, collections, json, time
import multiprocessing as mpc
from ht_lib import Inst, instances, bundles
from gstar_run import line
HERE = os.path.dirname(os.path.abspath(__file__))
NPHI = 19
RADIUS = '2'
ROT = '0'


def run(item):
    name, sets, vals, m = item
    out = subprocess.run([os.path.join(HERE, 'gstar_measure'), RADIUS, ROT], input=line(sets, vals, m) + '\n',
                         capture_output=True, text=True).stdout.split()
    d = {out[2 * K + 4]: int(out[2 * K + 5]) for K in range(NPHI)}
    ex = None
    for t, w in enumerate(out):
        if w.startswith('example_phi'):
            ex = (w, [int(x) for x in out[t + 1:t + 1 + m]])
    return name, sets, vals, m, int(out[3]), d, ex


if __name__ == '__main__':
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    src = sys.argv[1]; nmax = int(args.get('NMAX', '4')); mmax = int(args.get('MMAX', '7'))
    maxst = int(args.get('MAXSTATES', '400000'))
    RADIUS = args.get('RADIUS', '2'); ROT = args.get('ROT', '0')
    print('$ python3 k4/haxell/gstar_measure_run.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); W = collections.Counter(); exs = {}
    items = [it for it in instances(src) if len(it[1]) <= nmax and it[3] <= mmax and (len(it[1]) + 1) ** it[3] <= maxst]
    with mpc.Pool(os.cpu_count()) as pool:
        for name, sets, vals, m, states, d, ex in pool.imap_unordered(run, items):
            C['instances'] += 1; C['partial EFX0 states'] += states
            for k, v in d.items():
                C['stuck states, ' + k] += v; W['instances with a stuck state, ' + k] += v > 0
                if v and k not in exs:
                    exs[k] = (name, sets, vals, m)
            if ex and ex[0] not in [e[0] for e in exs.values() if isinstance(e, tuple) and len(e) == 2]:
                pass
    for k in sorted(C):
        print(k, C[k])
    for k in sorted(W):
        print(k, W[k])
    for k in sorted(exs):
        name, sets, vals, m = exs[k]
        print('first instance with a stuck state for', k, ':', name, json.dumps((sets, vals)))
    print('time %.0f s' % (time.time() - t0))
