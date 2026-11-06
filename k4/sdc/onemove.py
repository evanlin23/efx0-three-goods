"""For every order whose SD outcome does not extend: does a single move (one agent moved to the front, or one adjacent
transposition) give an order whose SD outcome extends?"""
import sys, os, json, itertools, collections
import _paths
from sdclib import Enc
from sdc_orders import sd, completable
def analyse(sets, vals, m, r1, C):
    E = Enc(sets, vals, m); cache = {}
    def ext(order):
        Y = tuple(sd(E, order, r1)[0])
        if Y not in cache: cache[Y] = completable(E, list(Y))
        return cache[Y]
    for order in itertools.permutations(range(E.n)):
        if ext(order): continue
        C['bad orders'] += 1
        mtf = any(ext((x,) + tuple(a for a in order if a != x)) for x in order)
        adj = any(ext(order[:k] + (order[k + 1], order[k]) + order[k + 2:]) for k in range(E.n - 1))
        C['fixed by move-to-front'] += mtf; C['fixed by adjacent swap'] += adj; C['fixed by either'] += (mtf or adj)
        if not (mtf or adj) and C['shown'] < 3: C['shown'] += 1; print('UNFIXED', json.dumps((sets, vals, order)), flush=True)
if __name__ == '__main__':
    r1 = sys.argv[2] == 'r1'; C = collections.Counter()
    if sys.argv[1] == 'screen':
        os.chdir(_paths.DE4); from ss_screen import screen_set
        for name, I in screen_set():
            if I.n <= 6: analyse(I.sets, [[I.v[i][g] for g in I.sets[i]] for i in range(I.n)], I.m, r1, C)
    else:
        for line in open(sys.argv[1]):
            if 'inst' not in line: continue
            sets, vals = json.loads(line.split('inst ', 1)[1].rsplit(' time', 1)[0])
            analyse(sets, vals, 1 + max(max(s) for s in sets), r1, C)
    print(dict(C))
