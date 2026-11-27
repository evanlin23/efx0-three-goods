"""Shrink a three-agent counterexample to a class of kgen/oc3.c (default STRICT: OC1 with chains t >= 1) while it stays
one: drop goods, zero values, lower values, keeping every agent's positive values distinct (strict profile) unless
'ties' is given.  Greedy, to a local minimum of (m, number of positive values, sum of values).

    python3 kgen/shrink3.py '<json v>' [KEY] [ties]"""
import sys, json
from oc3lib import brute, picks, ORD
from gen3 import strict


def fails(v, key, allow_ties):
    if not allow_ties and not strict(v): return None
    m = len(v[0])
    if not all(any(v[a][g] > 0 for a in range(3)) for g in range(m)) or not all(any(r) for r in v): return None
    r = brute(v)
    if r[0]['EFX'] == 0: return None
    bad = [o for o in range(6) if r[o][key] == 0]
    return bad or None


def size(v):
    return (len(v[0]), sum(1 for r in v for x in r if x > 0), sum(map(sum, v)))


if __name__ == '__main__':
    v = json.loads(sys.argv[1]); key = sys.argv[2] if len(sys.argv) > 2 else 'STRICT'; ties = 'ties' in sys.argv
    assert fails(v, key, ties), 'not a counterexample'
    improved = True
    while improved:
        improved = False
        cands = []
        m = len(v[0])
        for g in range(m): cands.append([r[:g] + r[g + 1:] for r in v])
        for i in range(3):
            for g in range(m):
                if v[i][g] > 0:
                    w = [list(r) for r in v]; w[i][g] = 0; cands.append(w)
                    for d in (v[i][g] // 2, v[i][g] - 1):
                        if 0 < d < v[i][g]:
                            w = [list(r) for r in v]; w[i][g] = d; cands.append(w)
        for w in cands:
            if size(w) < size(v) and fails(w, key, ties):
                v = w; improved = True; break
    bad = fails(v, key, ties)
    print('shrunk', json.dumps(v), 'size (m, positive values, sum)', size(v), 'k', max(sum(1 for x in r if x > 0) for r in v))
    for o in bad: print('  fails at order', ORD[o], 'picks', picks(v, ORD[o]))
