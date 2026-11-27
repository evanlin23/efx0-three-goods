"""Validates the symmetry reduction of ht_n3grid.py: on the n = 3, K = 3, m <= 4, values {1, 2, 3} grid, the reduced
enumeration and the full product (every value on every (agent, good) pair) give the same isomorphism classes, and
every class gets the same verdict (a state with no augmenting step within one move, phi0 of gstar_measure 1 0 1 0).

    python3 k4/haxell/ht_n3grid_check.py"""
import sys, os, itertools, subprocess, collections
sys.argv = ['x', 'K=3', 'MMAX=4', 'VALS=1,2,3']
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ht_n3grid as G
HERE = os.path.dirname(os.path.abspath(__file__))
def run(lines):
    out = subprocess.run([os.path.join(HERE, 'gstar_measure'), '1', '0', '1', '0'], input='\n'.join(lines) + '\n',
                         capture_output=True, text=True).stdout.strip().split('\n')
    return [int(o.split()[5]) for o in out]
def canon(goods):
    best = None
    for perm in G.PERMS:
        img = []
        for p, vt in goods:
            q = tuple(sorted(perm[a] for a in p)); d = {perm[a]: x for a, x in zip(p, vt)}
            img.append((q, tuple(d[a] for a in q)))
        img = tuple(sorted(img))
        best = img if best is None or img < best else best
    return best
red, full = {}, {}
for m, key in G.shapes():
    L = list(G.instances(key))
    st = run([l for _, l in L])
    for (goods, _), s in zip(L, st):
        c = canon(goods); assert c not in red; red[c] = s > 0
    # full: every value per (agent, good) pair
    nv = sum(len(p) for p in key)
    lines, gl = [], []
    for vals in itertools.product(G.VALS, repeat=nv):
        it = iter(vals); goods = tuple((p, tuple(next(it) for _ in p)) for p in key)
        parts = ['3', str(len(goods))]
        for a in range(3):
            l = [(g, vt[p.index(a)]) for g, (p, vt) in enumerate(goods) if a in p]
            parts.append(str(len(l)))
            for g, x in l: parts += [str(g), str(x)]
        lines.append(' '.join(parts)); gl.append(goods)
    for goods, s in zip(gl, run(lines)):
        c = canon(goods)
        if c in full: assert full[c] == (s > 0), c
        full[c] = s > 0
print('reduced', len(red), 'full classes', len(full), 'equal sets', set(red) == set(full),
      'agree', all(red[c] == full[c] for c in red), 'stuck classes', sum(red.values()))
