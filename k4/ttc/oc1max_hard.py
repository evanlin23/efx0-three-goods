"""The hardest OC1^max starts of the n = 6 sweep (k4/ttc/oc1max_n6.py), taken apart (k4/ttc.md §13).

For each start printed under "hardest starts" in a sweep log: the frozen agents and who freezes them (an agent valuing
the frozen agent's pick above its own base), the dangerous agents with their junk sets, the receivers (unfrozen
agents), why the picks have no completion, and every repairing move (path and new bases) with a one-absorber
completion after it.  Completions are found by brute force over every way to hand out the junk, checked against the
raw EFX0 definition (v_i(X_i) >= v_i(X_j minus g) for all i, j and every g in X_j), with no SAT; the count of
repairing moves is recomputed with oc_absorb.extends_A as a cross-check.

    python3 k4/ttc/oc1max_hard.py LOG [LIMIT]"""
import sys, json, itertools
import ttclib as T


def efx0(v, X):
    n = len(X)
    for i in range(n):
        vi = sum(v[i].get(g, 0) for g in X[i])
        for j in range(n):
            if i == j:
                continue
            tot = sum(v[i].get(g, 0) for g in X[j])
            for g in X[j]:
                if tot - v[i].get(g, 0) > vi:
                    return False
    return True


def completions(E, base, absorbers=1):
    """every complete allocation keeping the bases, with at most `absorbers` agents receiving two or more junk goods,
    that is EFX0 (brute force)"""
    J = [g for g in range(E.m) if base[g] < 0]
    for a in itertools.product(range(E.n), repeat=len(J)):
        cnt = [a.count(i) for i in range(E.n)]
        if sum(1 for c in cnt if c >= 2) > absorbers:
            continue
        X = [[g for g in range(E.m) if base[g] == i] for i in range(E.n)]
        for g, i in zip(J, a):
            X[i].append(g)
        if efx0(E.v, X):
            yield X


def free_completion(E, base):
    return next(completions(E, base, E.n), None)


def analyse(d):
    sets, vals, m, Y = d['sets'], d['vals'], d['m'], d['picks']
    E = T.Enc(sets, vals, m); base = T.base_of(E, Y); B = T.bundles(E, base)
    J = [g for g in range(m) if base[g] < 0]
    F = T.frozen_set(E, base); D = T.dangerous_set(E, base)
    print('sets', sets, 'vals', vals, 'picks', Y, 'junk', J)
    for j in range(E.n):
        wanters = [i for i in range(E.n) if i != j and len(B[j]) == 1
                   and E.v[i].get(B[j][0], 0) > T.val(E, i, B[i])]
        js = [g for g in J if E.v[j].get(g, 0) > 0]
        tag = 'frozen by %s' % wanters if j in F else 'RECEIVER'
        print('  agent %d: pick %s (%d), %s, junk it values %s' % (
            j, Y[j], E.v[j].get(Y[j], 0), tag, {g: E.v[j][g] for g in js}))
    R = [j for j in range(E.n) if j not in F]
    # why the picks fail: every way to give the junk to the receivers, and the first violation
    print('  receivers', R, '; the picks: one-absorber completion', next(completions(E, base), None) is not None,
          ', free completion', free_completion(E, base) is not None)
    for a in itertools.product(R, repeat=len(J)):
        X = [list(B[i]) for i in range(E.n)]
        for g, i in zip(J, a):
            X[i].append(g)
        why = None
        for i in range(E.n):
            vi = T.val(E, i, X[i])
            for j in range(E.n):
                if i != j:
                    for g in X[j]:
                        if T.val(E, i, X[j]) - E.v[i].get(g, 0) > vi:
                            why = why or 'agent %d envies %s minus %d (%d > %d)' % (
                                i, X[j], g, T.val(E, i, X[j]) - E.v[i].get(g, 0), vi)
        print('    junk to', dict(zip(J, a)), ':', why or 'EFX0')
    nmoves = 0; rep = []; sat = 0; seen = set()
    for b2, path in T.iter_chains_path(E, base):
        if b2 in seen:
            continue
        seen.add(b2); nmoves += 1
        X = next(completions(E, b2), None)
        sat += T.extends_A(E, b2, 1)
        if X is not None:
            rep.append((path, b2, X))
    print('  %d distinct moves, %d repairing (SAT count %d)' % (nmoves, len(rep), sat))
    for path, b2, X in rep:
        nb = T.bundles(E, b2)
        print('    path', path, 'new bases', {i: nb[i] for i in range(E.n) if nb[i] != B[i]}, 'completion', X)
    return len(rep), sat


if __name__ == '__main__':
    lim = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    print('$ python3 k4/ttc/oc1max_hard.py', *sys.argv[1:])
    k = 0
    for line in open(sys.argv[1]):
        if 'repairing moves {' in line:
            a = line.index('{'); e = line.index('} {') + 1 if '} {' in line else line.rindex('}') + 1
            d = json.loads(line[a:e])
            r, s = analyse(d)
            assert r == s, (r, s)
            k += 1
            if k >= lim:
                break
