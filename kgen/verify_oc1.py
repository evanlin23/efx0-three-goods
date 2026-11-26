"""Independent replay of OC1 at a given start, n = 3, for both chain conventions, from the definitions alone.

Pure Python, no code shared with kgen/oc3.c: it enumerates every complete allocation (raw EFX0 test), then every
improving chain EXPLICITLY (every x0, ..., x_t, every choice of the sets H_i as subsets of the allowed goods), and for
every state reached asks whether some EFX0 allocation is a one-absorber completion of it (keeps every base, at most
one agent receives two or more goods outside its base).  Chains as in k4/sdc/de_free.py:
  x0 takes H0 (subset of J, plus B_{x_t} if t >= 1; t = 0: added to x0's base), each x_i (i >= 1) takes B_{x_{i-1}}
  plus H_i (subset of J); every H inside the receiver's positively valued goods; strict gains; t <= 2.
Also the second check through k4/sdc's SAT code (oc_absorb.extends_A; chains of de_free.iter_chains, unbounded sets),
with the t >= 1 restriction applied by discarding states in which only one agent's base changed.

    python3 kgen/verify_oc1.py '<json v>' [order like 0,1,2]   (all orders if omitted)"""
import sys, os, json, itertools

HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)


def efx0(v, X):
    for i in range(3):
        own = sum(v[i][g] for g in X[i])
        for j in range(3):
            if j != i and len(X[j]) >= 2 and sum(v[i][g] for g in X[j]) - min(v[i][g] for g in X[j]) > own:
                return False
    return True


def all_efx(v):
    m = len(v[0]); out = []
    for asg in itertools.product(range(3), repeat=m):
        X = [frozenset(g for g in range(m) if asg[g] == i) for i in range(3)]
        if efx0(v, X): out.append(X)
    return out


def sd(v, order):
    m = len(v[0]); left = set(range(m)); y = [None] * 3
    for i in order:
        av = [g for g in left if v[i][g] > 0]
        if av:
            g = max(av, key=lambda h: (v[i][h], -h)); y[i] = g; left.discard(g)
    return y


def subsets(xs):
    xs = list(xs)
    for r in range(len(xs) + 1):
        yield from itertools.combinations(xs, r)


def chain_states(v, B, J):
    """yield (t, new bases) for every improving chain from bases B (list of frozensets), junk J"""
    val = lambda i, S: sum(v[i][g] for g in S)
    for t in range(0, 3):
        for path in itertools.permutations(range(3), t + 1):
            if any(not B[path[i]] for i in range(t)): continue     # passing an empty base is not a move
            def rec(i, used, newB):
                if i > t:
                    x0, xt = path[0], path[-1]
                    pool = [g for g in J if g not in used and v[x0][g] > 0]
                    if t >= 1: pool += [g for g in B[xt] if v[x0][g] > 0]
                    for H0 in subsets(pool):
                        if not H0: continue
                        nb0 = (B[x0] | frozenset(H0)) if t == 0 else frozenset(H0)
                        if val(x0, nb0) <= val(x0, B[x0]): continue
                        nb = list(newB); nb[x0] = nb0
                        yield t, nb
                    return
                xi, prev = path[i], path[i - 1]
                free = [g for g in J if g not in used and v[xi][g] > 0]
                for H in subsets(free):
                    nbi = B[prev] | frozenset(H)
                    if val(xi, nbi) <= val(xi, B[xi]): continue
                    nb = list(newB); nb[xi] = nbi
                    yield from rec(i + 1, used | set(H), nb)
            yield from rec(1, frozenset(), list(B))


def one_absorber(Xs, B):
    for X in Xs:
        if all(B[i] <= X[i] for i in range(3)) and sum(1 for i in range(3) if len(X[i] - B[i]) >= 2) <= 1:
            return X
    return None


def replay(v, order, Xs=None):
    m = len(v[0]); Xs = Xs if Xs is not None else all_efx(v)
    y = sd(v, order); B = [frozenset([y[i]]) if y[i] is not None else frozenset() for i in range(3)]
    J = [g for g in range(m) if g not in y]
    res = {'picks': y, 'EFX0 allocations': len(Xs)}
    X = one_absorber(Xs, B)
    res['picks: one-absorber completion'] = [sorted(b) for b in X] if X else None
    wit = {0: None, 1: None}; nstates = {0: 0, 1: 0}
    for t, nb in chain_states(v, B, J):
        key = 1 if t >= 1 else 0
        nstates[key] += 1
        if wit[key] is None:
            X = one_absorber(Xs, nb)
            if X: wit[key] = ([sorted(b) for b in nb], [sorted(b) for b in X], t)
    res['chain states t=0'] = nstates[0]; res['chain states t>=1'] = nstates[1]
    res['repair with t>=1'] = wit[1]; res['repair with t=0'] = wit[0]
    res['OC1 (t>=1) holds'] = res['picks: one-absorber completion'] is not None or wit[1] is not None
    res['OC1 (t>=0) holds'] = res['OC1 (t>=1) holds'] or wit[0] is not None
    return res


def sat_replay(v, order):
    sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
    import _paths  # noqa
    import de_free as DF
    from sdclib import Enc
    from oc_absorb import extends_A
    from sdc_orders import sd as sd2
    m = len(v[0]); DF.CHAIN_ONLY = True; DF.HMAX = m; DF.BMAX = m
    sets = [[g for g in range(m) if v[i][g] > 0] for i in range(3)]
    E = Enc(sets, [[v[i][g] for g in sets[i]] for i in range(3)], m)
    Y = sd2(E, list(order))[0]
    base = [-1] * m
    for i, g in enumerate(Y):
        if g is not None: base[g] = i
    base = tuple(base)
    if extends_A(E, base, 1): return {'sat: picks': True}
    r = {'sat: picks': False, 'sat: t>=1': False, 'sat: t=0': False}
    for b2 in set(DF.iter_chains(E, base)):
        changed = {i for i in range(3) if {g for g in range(m) if b2[g] == i} != {g for g in range(m) if base[g] == i}}
        key = 'sat: t>=1' if len(changed) >= 2 else 'sat: t=0'
        if not r[key] and extends_A(E, b2, 1): r[key] = True
    return r


if __name__ == '__main__':
    v = json.loads(sys.argv[1])
    orders = [tuple(map(int, sys.argv[2].split(',')))] if len(sys.argv) > 2 else list(itertools.permutations(range(3)))
    Xs = all_efx(v)
    for o in orders:
        r = replay(v, o, Xs); r.update(sat_replay(v, o))
        print('order', o, json.dumps(r, default=str))
