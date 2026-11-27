"""Exhaustive grids for ROUND+ and RD2+ (kgen/rounds.md §4.7): every profile with values in {1..V} (agents' rows as a
multiset; every order is tested at each), n agents, m goods; one round by Lemma RC, two rounds by Lemma RC2 (rnd.c).
    python3 kgen/rounds/grid.py n m V [n m V ...]"""
import sys, os, time, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib
a = list(map(int, sys.argv[1:]))
print('$ python3 kgen/rounds/grid.py', *a, flush=True)
for k in range(0, len(a), 3):
    n, m, V = a[k:k + 3]; t = time.time()
    p, s, f1, f2, recs = rndlib.grid(n, m, V)
    print('n %d m %d values 1..%d: profiles %d, starts %d, starts needing more than one round %d, more than two rounds %d (%.0f s)'
          % (n, m, V, p, s, f1, f2, time.time() - t), flush=True)
    for vals, picks in recs: print('   TWO-ROUND FAILURE', json.dumps(vals), 'picks', picks, flush=True)
