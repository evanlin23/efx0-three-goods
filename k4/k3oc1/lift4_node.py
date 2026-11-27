"""k = 4 starts where no valid DE-type chain (lift4.de_type) gives a one-absorber completion while a general improving
chain (k4/sdc.md §29) does: print the start and every repairing general chain with the reason it is not DE-type.
    python3 k4/k3oc1/lift4_node.py screen|special|suite NMAX [MAX] [comp]"""
import sys, os, itertools, collections, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import lift4
from lift4 import DF, Enc, instances, sd, SPECIAL, complete, de_type, rankscore, frozen, valid
lift4.COMP = 'comp' in sys.argv
src = sys.argv[1]; NMAX = int(sys.argv[2]); MAX = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3].isdigit() else 3
items = SPECIAL if src == 'special' else instances(src)
items = sorted([it for it in items if len(it[1]) <= NMAX], key=lambda it: (len(it[1]), it[3]))
shown = 0; C = collections.Counter()
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
        C['hard'] += 1
        if any(complete(E, b2, False) for b2 in de_type(E, base)): continue
        C['no DE-type chain repairs'] += 1
        B = DF.bundles(E, base); top = [max(E.R[i], key=lambda g: E.v[i][g]) for i in range(E.n)]
        reasons = set()
        for b2, descs in DF.moves(E, base, describe=True, all_desc=True).items():
            if not complete(E, b2, False): continue
            best = None
            for kind, path, H in descs:
                why = []
                if len(path) < 2: why.append('t = 0')
                if any(H.get(t) and B[path[t]] != [top[path[t]]] for t in range(len(path))): why.append('junk to an agent not holding its top')
                if not (lift4.valid_star if lift4.COMP else valid)(E, b2): why.append('not valid')
                if best is None or len(why) < len(best): best = why
            reasons.add(' + '.join(best))
        C['repairing chains need: ' + ' | '.join(sorted(reasons))] += 1
        if shown >= MAX: continue
        shown += 1
        B = DF.bundles(E, base); top = [max(E.R[i], key=lambda g: E.v[i][g]) for i in range(E.n)]
        print('=== %s n=%d m=%d order %s picks %s junk %s frozen %s' % (name, len(sets), m, o, Y, [g for g in range(m) if base[g] < 0], frozen(E, base)))
        print('    sets', json.dumps(sets), 'vals', json.dumps(vals))
        for b2, descs in DF.moves(E, base, describe=True, all_desc=True).items():
            if not complete(E, b2, False): continue
            kind, path, H = descs[0]
            why = []
            if len(path) < 2: why.append('t = 0 (x0 adds junk to its base)')
            if any(H.get(t) and B[path[t]] != [top[path[t]]] for t in range(len(path))): why.append('an agent not holding its top takes junk')
            if not valid(E, b2): why.append('result not valid')
            print('    REPAIRS %s bases %s; not DE-type: %s' % (descs[0], DF.bundles(E, b2), '; '.join(why)))
print(dict(C))
