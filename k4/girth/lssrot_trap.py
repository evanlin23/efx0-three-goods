"""Targeted search against Conjecture LR (k4/girth.md section 4): random linear instances grown around the trap of
attempts/k4-girth-linear-pl.md (leftover e = {i, j}; r envies i and holds f in j; s envies j and holds h in i), with
random extra agents and goods, degree <= 4; LSS-ROT with every vertex 0 and random labelings, then parking.

    python3 k4/girth/lssrot_trap.py SEED SECONDS
"""
import collections
import itertools
import random
import sys
import time

from lss import Inst, labels, random_labels, lss_rot, park_any_state, two_cycles, is_efx0


def grow(rng):
    # agents 0=i 1=j 2=r 3=s; goods e{i,j}, x_i{i,r}, x_j{j,s}, f{r,j}, h{s,i}
    edges = [[0, 1], [0, 2], [1, 3], [2, 1], [3, 0]]
    n = 4 + rng.randint(0, 4)
    deg = [0] * n
    for e in edges:
        for a in e:
            deg[a] += 1
    pairs = {tuple(sorted(p)) for e in edges for p in itertools.combinations(e, 2)}
    for _ in range(rng.randint(2, 14)):
        s = rng.choice([1, 1, 2, 2, 3])
        free = [a for a in range(n) if deg[a] < 4]
        if len(free) < s:
            continue
        e = sorted(rng.sample(free, s))
        if any(tuple(p) in pairs for p in itertools.combinations(e, 2)):
            continue
        edges.append(e)
        for a in e:
            deg[a] += 1
        pairs |= {tuple(p) for p in itertools.combinations(e, 2)}
    sets = [[g for g, e in enumerate(edges) if a in e] for a in range(n)]
    if any(not S for S in sets):
        return None
    vals = []
    for a, S in enumerate(sets):
        vals.append([rng.randint(1, 30) for _ in S])
    return Inst(sets, vals, len(edges))


def main():
    seed, secs = int(sys.argv[1]), float(sys.argv[2])
    rng = random.Random(seed)
    C = collections.Counter()
    t0 = time.time()
    print('$ python3 k4/girth/lssrot_trap.py', *sys.argv[1:], flush=True)
    while time.time() - t0 < secs:
        I = grow(rng)
        if I is None:
            continue
        assert not two_cycles(I)
        C['instances'] += 1
        for z in range(I.n):
            for rep in range(3):
                lab = labels(I, z) if rep == 0 else random_labels(I, z, rng)
                r = lss_rot(I, lab)
                assert r.first_break is None
                C['runs'] += 1
                Z = park_any_state(I, r.X, r.U)
                if Z is None:
                    C['FAIL'] += 1
                    print('FAIL', I, 'labels', lab, 'state', [sorted(b) for b in r.X], 'U', sorted(r.U), flush=True)
        if C['instances'] % 5000 == 0:
            print(dict(C), flush=True)
    print(dict(C), flush=True)


if __name__ == '__main__':
    main()
