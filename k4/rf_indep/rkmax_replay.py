"""Replay one profile with this workstream's own code: all SD vectors, the maximum matchings, sigma, the sigma-maximal
vectors, their receivers and junk, and OC1 at each (rf_oc1.c, witness re-checked).  Default: Hall's counterexample to
plan (a), 5_pure (m 8, idx 358) of k4/oc1_hall.md section 24.14.

    python3 k4/rf_indep/rkmax_replay.py
"""
import sys, os, itertools, json, subprocess, tempfile
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rf_check as R
from rkmax_check import sigma

SETS = [[0, 1, 4, 5], [1, 3, 6, 7], [2, 3, 6, 7], [2, 4, 5, 7], [4, 5, 6, 7]]
VALS = [[17, 4, 2, 19], [13, 14, 20, 16], [2, 16, 20, 17], [5, 17, 15, 7], [20, 17, 4, 8]]

if __name__ == '__main__':
    print('$ python3 k4/rf_indep/rkmax_replay.py')
    sets, vals = SETS, VALS; m = 1 + max(max(s) for s in sets); n = len(sets); nu = R.nu_kuhn(sets)
    pref = R.prefs(sets, vals)
    vecs = sorted(set(R.sd(pref, o) for o in itertools.permutations(range(n))), key=str)
    mm = [Y for Y in vecs if sum(1 for y in Y if y is not None) == nu]
    sig = {Y: sigma(sets, vals, Y) for Y in mm}; best = max(sig.values())
    print('sets', json.dumps(sets), 'vals', json.dumps(vals), 'm', m, 'nu', nu)
    print('SD vectors %d, maximum matchings %d' % (len(vecs), len(mm)))
    for Y in mm: print('  ', Y, 'sigma', sig[Y], '<- sigma-maximal' if sig[Y] == best else '')
    binpath = os.path.join(tempfile.gettempdir(), 'rf_oc1_bin')
    subprocess.check_call(['gcc', '-O2', '-o', binpath, os.path.join(HERE, 'rf_oc1.c')])
    lines = [R.task_line('x:0:%d' % j, sets, vals, m, [[y] if y is not None else [] for y in Y])
             for j, Y in enumerate(Y for Y in mm if sig[Y] == best)]
    shards, _ = R.run_shards(lines, 1, binpath, 'replay')
    for (line, a) in R.pairs(*shards[0]):
        tid, s, v, mm_, B = R.parse_task(line)
        Y = tuple(b[0] if b else None for b in B)
        J = sorted(set(range(m)) - set(y for y in Y if y is not None))
        print('sigma-maximal', Y, 'receivers', R.receivers(sets, vals, Y), 'junk', J, 'OC1 answer', ' '.join(a))
    out, F = R.verify_shard(shards[0])
    print('witness check', {k: dict(c) for k, c in out.items()}, 'F', len(F))
