"""print the starts where the best reverse-SD path needs steps > 1, with the best insertion sequences"""
import sys, itertools, collections, json
import _paths
from sdilib import Inst, sd, wanted_by
from e1_delete import load
from e2_paths import sub_completions, bottleneck
from e3_suffix import absorber
for name, sets, vals, m in load(sys.argv[1]):
    if len(sets) > 4: continue
    I = Inst(sets, vals, m)
    byY = collections.defaultdict(list)
    for o in itertools.permutations(range(I.n)): byY[tuple(sd(I, o)[0])].append(o)
    for Y, orders in byY.items():
        Y = list(Y); cache = {}
        full = sub_completions(I, Y, range(I.n), cache)
        if len(full) == 0: continue
        bn = lambda L: (lambda d: 99 if d is None else d)(bottleneck(L))
        bs = min(bn([sub_completions(I, Y, list(pi)[::-1][:k], cache) for k in range(1, I.n + 1)]) for pi in orders)
        if bs <= 1: continue
        good = [s for s in itertools.permutations(range(I.n)) if bn([sub_completions(I, Y, s[:k], cache) for k in range(1, I.n + 1)]) <= 1]
        W = wanted_by(I, Y)
        print(name, json.dumps((sets, vals)), 'picks', Y, 'wanters', W, 'suffix best', bs, 'absorbers', sorted(set(map(str, (absorber(x, I.n) for x in full)))), 'good seqs', good[:6])
