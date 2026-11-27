"""n = 3, positive values: for every start whose picks do not extend, which agents (by ORDER POSITION: 0 = first
picker, 1, 2 = last) form the repairing chain (kgen/rounds.md §5.2).  Shapes as in n3shapes.py, with positions:
H(p0>p1) hand-off from position p0 to p1; S{p,q} swap; P3(p0>p1>p2); R3(p0>p1>p2).  Reports which single position
patterns cover every hard start.
    python3 kgen/rounds/n3roles.py rand T SEED mmin mmax | file LOGS..."""
import sys, os, json, random, re, collections, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, families
from n3shapes import efx


def patterns(V, X, y, order):
    pos = {a: k for k, a in enumerate(order)}
    m = len(V[0]); own = [None] * m
    for i, B in enumerate(X):
        for g in B: own[g] = i
    J = set(range(m)) - set(y); loc = [own[y[a]] for a in range(3)]
    vj = [sum(V[i][g] for g in X[i] if g in J) for i in range(3)]
    out = set()
    for x0, x1 in itertools.permutations(range(3), 2):
        z = 3 - x0 - x1
        if loc[x0] != x1 or loc[z] != z or not (V[x1][y[x0]] + vj[x1] > V[x1][y[x1]]): continue
        ring = loc[x1] == x0
        if vj[x0] + (V[x0][y[x1]] if ring else 0) > V[x0][y[x0]]:
            out.add(('S{%d,%d}' % tuple(sorted((pos[x0], pos[x1])))) if ring else 'H(%d>%d)' % (pos[x0], pos[x1]))
    for x0, x1, x2 in itertools.permutations(range(3), 3):
        if loc[x0] != x1 or loc[x1] != x2: continue
        if not (V[x1][y[x0]] + vj[x1] > V[x1][y[x1]] and V[x2][y[x1]] + vj[x2] > V[x2][y[x2]]): continue
        ring = loc[x2] == x0
        if vj[x0] + (V[x0][y[x2]] if ring else 0) > V[x0][y[x0]]:
            out.add(('R3' if ring else 'P3') + '(%d>%d>%d)' % (pos[x0], pos[x1], pos[x2]))
    return out


def hard_starts(V):
    L, _ = rndlib.list_efx(V); m = len(V[0])
    Xs = [[[g for g in range(m) if own[g] == i] for i in range(3)] for own in L]
    res, _ = rndlib.analyze(V)
    for r in res:
        if r['counts']['EXTF'] > 0: continue
        y = list(r['picks']); P = set()
        for X in Xs: P |= patterns(V, X, y, r['order'])
        yield r['order'], P


def main():
    if sys.argv[1] == 'rand':
        T, seed, mmin, mmax = map(int, sys.argv[2:6]); rng = random.Random(seed)
        insts = [families.gen(families.KINDS[t % len(families.KINDS)], 3, rng.randint(mmin, mmax), rng) for t in range(T)]
    else:
        insts = []
        for f in sys.argv[2:]:
            for line in open(f):
                mm = re.search(r'vals (\[\[.*?\]\])', line)
                if mm and len(json.loads(mm.group(1))) == 3: insts.append(json.loads(mm.group(1)))
    C = collections.Counter(); covers = collections.Counter(); H = 0; allp = set(); ex = {}
    for V in insts:
        for o, P in hard_starts(V):
            H += 1; allp |= P
            for p in P: C[p] += 1
            key = tuple(sorted(P)); covers[key] += 1; ex.setdefault(key, (V, o))
    print('hard starts', H)
    for p in sorted(allp): print('  pattern %-12s repairs %d of %d' % (p, C[p], H))
    print('distinct pattern sets:', len(covers))
    for k, c in covers.most_common(12): print('  ', c, k)
    FAM = {'last receives (H(0>2), H(1>2), S{0,2}, S{1,2})': {'H(0>2)', 'H(1>2)', 'S{0,2}', 'S{1,2}'},
           'two-agent move with the last picker (incl. H(2>.))': {'H(0>2)', 'H(1>2)', 'S{0,2}', 'S{1,2}', 'H(2>0)', 'H(2>1)'},
           'any two-agent move': {p for p in allp if p[0] in 'HS'},
           'last receives, or a rotation': {'H(0>2)', 'H(1>2)', 'S{0,2}', 'S{1,2}'} | {p for p in allp if p.startswith('R3')}}
    for name, F in FAM.items():
        miss = [k for k in covers if not (set(k) & F)]
        print('cover "%s": misses %d starts' % (name, sum(covers[k] for k in miss)))
        for k in miss[:3]: print('     missed pattern set', k, 'example', json.dumps(ex[k][0]), 'order', ex[k][1])
    singles = [k for k in covers if len(k) == 1]
    for k in singles: print('only', k, 'example', json.dumps(ex[k][0]), 'order', ex[k][1])


if __name__ == '__main__':
    print('$ python3 kgen/rounds/n3roles.py', *sys.argv[1:]); main()
