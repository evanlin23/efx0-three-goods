"""Shrink a three-agent PD counterexample (a partial EFX0 allocation no complete one value-dominates; kgen/pd3.c)
while it stays one: zero values, lower values, drop goods; optionally down to at most K positively valued goods per agent.
Each step re-checked by pd3.c; the final instance is replayed by pd3_hunt.verify (pure Python).

    python3 kgen/pd3_shrink.py '<json v>' [K]"""
import sys, json
from pd3_hunt import pd, verify


def ok(v):
    m = len(v[0])
    if not all(any(v[a][g] > 0 for a in range(3)) for g in range(m)) or not all(any(r) for r in v): return None
    nb, X, cnt = pd(v)
    return X if nb else None


def size(v, K):
    over = sum(max(0, sum(1 for x in r if x > 0) - K) for r in v) if K else 0
    return (over, len(v[0]), sum(1 for r in v for x in r if x > 0), sum(map(sum, v)))


if __name__ == '__main__':
    v = json.loads(sys.argv[1]); K = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    assert ok(v)
    imp = True
    while imp:
        imp = False; m = len(v[0]); c = [[r[:g] + r[g + 1:] for r in v] for g in range(m)]
        for i in range(3):
            for g in range(m):
                if v[i][g]:
                    for d in (0, v[i][g] // 2, v[i][g] - 1):
                        w = [list(r) for r in v]; w[i][g] = d; c.append(w)
        for w in c:
            if size(w, K) < size(v, K) and ok(w): v = w; imp = True; break
    X = ok(v)
    print('shrunk', json.dumps(v), 'k', max(sum(1 for x in r if x > 0) for r in v), 'size', size(v, K))
    print('undominated partial EFX0 allocation', X[:3], 'unallocated', X[3], 'pure-python replay', verify(v, X))
