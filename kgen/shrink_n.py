"""Shrink an n-agent counterexample to a class of kgen/ocn.c (default CODE = OC1 with t >= 0) while it stays one:
lower k (positive values per agent) first, then m, the number of positive values, the sum.  Strict values kept unless
'ties'.  Greedy local search.

    python3 kgen/shrink_n.py '<json v>' [KEY] [ties]"""
import sys, json
from ocnlib import brute_n


def fails(v, key, ties):
    n, m = len(v), len(v[0])
    if not all(any(v[a][g] > 0 for a in range(n)) for g in range(m)) or not all(any(r) for r in v): return None
    if not ties and any(len(set(x for x in r if x > 0)) < sum(1 for x in r if x > 0) for r in v): return None
    orders, r = brute_n(v)
    if r[0]['EFX'] == 0: return None
    bad = [(orders[k], r[k]['picks']) for k in range(len(r)) if r[k][key] == 0]
    return bad or None


def size(v):
    return (max(sum(1 for x in r if x > 0) for r in v), len(v[0]), sum(1 for r in v for x in r if x > 0), sum(map(sum, v)))


if __name__ == '__main__':
    v = json.loads(sys.argv[1]); key = sys.argv[2] if len(sys.argv) > 2 else 'CODE'; ties = 'ties' in sys.argv
    assert fails(v, key, ties)
    imp = True
    while imp:
        imp = False; n, m = len(v), len(v[0]); c = [[r[:g] + r[g + 1:] for r in v] for g in range(m)]
        for i in range(n):
            for g in range(m):
                if v[i][g]:
                    for d in (0, v[i][g] // 2, v[i][g] - 1):
                        if d < v[i][g]:
                            w = [list(r) for r in v]; w[i][g] = d; c.append(w)
        c.sort(key=size)
        for w in c:
            if size(w) < size(v) and fails(w, key, ties): v = w; imp = True; break
    print('shrunk', json.dumps(v), 'size (k, m, positives, sum)', size(v))
    for o, y in fails(v, key, ties): print('  fails at order', o, 'picks', y)
