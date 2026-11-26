"""Smallest k = 4 starts where the k = 3 selection rule fails: some max rank-score DE-type chain (lift4.de_type) does
not lead to a one-absorber completion although some chain does.  Prints each such start with the max-score chains,
their descriptions and the repairing chains.
    python3 k4/k3oc1/lift4_fail.py screen|special|suite NMAX [MAX]"""
import sys, os, itertools, collections, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from lift4 import DF, Enc, instances, sd, SPECIAL, complete, de_type, rankscore, frozen
src = sys.argv[1]; NMAX = int(sys.argv[2]); MAX = int(sys.argv[3]) if len(sys.argv) > 3 else 3
items = SPECIAL if src == 'special' else instances(src)
items = sorted([it for it in items if len(it[1]) <= NMAX], key=lambda it: (len(it[1]), it[3]))
shown = 0
for name, sets, vals, m in items:
    E = Enc(sets, vals, m); seen = set()
    for o in itertools.permutations(range(len(sets))):
        Y = tuple(sd(E, list(o))[0])
        if Y in seen: continue
        seen.add(Y)
        base = [-1] * m
        for i, g in enumerate(Y):
            if g is not None: base[g] = i
        base = tuple(base)
        if complete(E, base, False): continue
        ch = list(de_type(E, base))
        if not ch: continue
        ok = {b2: complete(E, b2, False) for b2 in ch}
        rs = {b2: rankscore(E, b2) for b2 in ch}; best = max(rs.values())
        bad = [b2 for b2 in ch if rs[b2] == best and not ok[b2]]
        if not bad: continue
        shown += 1
        print('=== %s n=%d m=%d order %s picks %s junk %s frozen %s' % (name, len(sets), m, o, Y, [g for g in range(m) if base[g] < 0], frozen(E, base)))
        print('    sets', json.dumps(sets), 'vals', json.dumps(vals))
        descs = DF.moves(E, base, describe=True, all_desc=True)
        for b2 in sorted(ch, key=lambda b: -rs[b]):
            print('    %s score %d %s bases %s' % ('REPAIRS' if ok[b2] else 'fails  ', rs[b2], descs[b2][0], DF.bundles(E, b2)))
        break
    if shown >= MAX: break
