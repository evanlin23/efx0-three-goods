"""Driver for gstar.c (k4/haxell.md §3.4): feeds instances to the C census, optionally cross-checks every count
against the Python census ht_gstar.py (XCHECK=1, small instances only), and summarizes.

    cc -O2 -o k4/haxell/gstar k4/haxell/gstar.c
    python3 k4/haxell/gstar_run.py SRC [NMAX=5] [MMAX=9] [XCHECK=0] [MAXSTATES=3000000] [SHOW=8]"""
import sys, os, json, subprocess, collections, time
import multiprocessing as mpc
from ht_lib import Inst, instances, bundles
HERE = os.path.dirname(os.path.abspath(__file__))


def line(sets, vals, m):
    parts = [str(len(sets)), str(m)]
    for s, v in zip(sets, vals):
        parts.append(str(len(s)))
        for g, x in zip(s, v):
            parts += [str(g), str(x)]
    return ' '.join(parts)


def run_c(item):
    name, sets, vals, m = item
    out = subprocess.run([os.path.join(HERE, 'gstar')], input=line(sets, vals, m) + '\n', capture_output=True,
                         text=True).stdout.split()
    d = dict(zip(out[2:12:2], map(int, out[3:12:2])))
    ex = [int(x) for x in out[13:]] if 'example' in out else None
    return name, sets, vals, m, d, ex


if __name__ == '__main__':
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    src = sys.argv[1]; nmax = int(args.get('NMAX', '5')); mmax = int(args.get('MMAX', '9'))
    xcheck = args.get('XCHECK', '0') == '1'; maxst = int(args.get('MAXSTATES', '3000000'))
    show = int(args.get('SHOW', '8'))
    print('$ python3 k4/haxell/gstar_run.py', *sys.argv[1:], flush=True)
    t0 = time.time(); C = collections.Counter(); shown = 0
    items = [it for it in instances(src) if len(it[1]) <= nmax and it[3] <= mmax and (len(it[1]) + 1) ** it[3] <= maxst]
    C['instances skipped (size)'] = len([it for it in instances(src)]) - len(items)
    with mpc.Pool(os.cpu_count()) as pool:
        for name, sets, vals, m, d, ex in pool.imap_unordered(run_c, items):
            C['instances'] += 1; C['partial EFX0 states'] += d['states']; C['traps'] += d['traps']
            C['radius-2 traps'] += d['radius2traps']; C['instances with a trap'] += d['traps'] > 0
            C['instances with a radius-2 trap'] += d['radius2traps'] > 0
            C['instances without a complete EFX0 allocation'] += d['complete'] == 0
            C['instances n=%d' % len(sets)] += 1
            if d['traps'] > 0:
                C['instances with a trap, n=%d' % len(sets)] += 1
            if xcheck:
                from ht_gstar import traps as ptraps, radius2_traps
                I = Inst(sets, vals, m)
                S, comp, T = ptraps(I)
                T2 = radius2_traps(I, S, T) if T else set()
                same = (len(S), len(comp), len(T), len(T2)) == (d['states'], d['complete'], d['traps'], d['radius2traps'])
                C['cross-check agrees'] += same; C['cross-check DISAGREES'] += not same
                if not same:
                    print('DISAGREE', name, json.dumps((sets, vals)), (len(S), len(comp), len(T), len(T2)), d, flush=True)
            if (d['traps'] > 0 and shown < show) or d['radius2traps'] > 0 or d['complete'] == 0:
                shown += 1
                I = Inst(sets, vals, m)
                own = [x for x in ex] if ex else None
                print('RADIUS-2 TRAP' if d['radius2traps'] else 'NO EFX0' if d['complete'] == 0 else 'TRAPS', name,
                      json.dumps((sets, vals)), d, 'e.g.', bundles(I, own) if own else None,
                      'pool', [g for g in range(m) if own and own[g] < 0], flush=True)
    for k in sorted(C):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
