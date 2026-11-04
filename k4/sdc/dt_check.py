"""Theorem DT (k4/sdc.md §6): the construction of the proof, run literally, with the raw EFX0 check.

Instance: every agent values at most four goods, tops pairwise distinct (any values, ties broken by good index).
Construction: every agent holds its top; an owner o (every choice is tried); a matching M of other agents to their own
unallocated goods, built by the moves of the proof:
  (m1) an agent i != o, unmatched, with a danger set inside X_o: match i to a good of that set in L;
  (m2) an agent i != o, matched to a good d with {a_i, d} not robust, with {b_i, c_i} inside X_o: rematch i to one of
       b_i, c_i that lies in L;
until neither applies; L = unmatched unallocated goods, all given to o.  The script asserts: the moves stop, the final
allocation is EFX0 (raw definition), o is unenvied, and at most one bundle has more than two goods.

    python3 k4/sdc/dt_check.py SEED N n"""
import sys, random, itertools, collections


def ranked(v, i):
    return sorted(v[i], key=lambda g: (-v[i][g], g))


def val(v, i, S):
    return sum(v[i].get(g, 0) for g in S)


def raw_efx0(n, v, B):
    for i in range(n):
        mine = val(v, i, B[i])
        for j in range(n):
            if j != i:
                for h in B[j]:
                    if val(v, i, [g for g in B[j] if g != h]) > mine:
                        return False
    return True


def construct(n, m, v, o):
    tops = [ranked(v, i)[0] if v[i] else None for i in range(n)]
    junk = [g for g in range(m) if g not in tops]
    match = {}                                          # agent -> good

    def L():
        used = set(match.values())
        return [g for g in junk if g not in used]

    def Xo():
        return ([tops[o]] if tops[o] is not None else []) + L()

    def robust(i, S):
        return 2 * val(v, i, S) >= val(v, i, v[i])

    def danger_inside(i, X):
        """A set T of i's goods outside i's holding, T subset of X, with v_i(T) > v_i(holding)."""
        hold = [tops[i]] + ([match[i]] if i in match else [])
        t = val(v, i, hold)
        own = [g for g in X if g in v[i] and g not in hold]
        for r in range(2, len(own) + 1):
            for T in itertools.combinations(own, r):
                if val(v, i, T) > t:
                    return T
        return None
    steps = 0
    while True:
        steps += 1
        assert steps < 10 * (n + m) + 10, 'moves do not stop'
        moved = False
        for i in range(n):
            if i == o or tops[i] is None:
                continue
            hold = [tops[i]] + ([match[i]] if i in match else [])
            if robust(i, hold):
                continue
            T = danger_inside(i, Xo())
            if T is None:
                continue
            free = [g for g in T if g in L()]
            assert free, 'a danger set inside X_o has a good of L'
            if i not in match:                                         # (m1)
                match[i] = free[0]
            else:                                                      # (m2)
                R = ranked(v, i)
                assert len(R) == 4 and match[i] == R[3], (i, R, match[i])
                assert set(T) <= {R[1], R[2]} | {R[3]}
                p = [g for g in (R[1], R[2]) if g in L()]
                assert p
                match[i] = p[0]
            moved = True
            break
        if not moved:
            break
    B = [[] for _ in range(n)]
    for i in range(n):
        if tops[i] is not None:
            B[i].append(tops[i])
        if i in match and i != o:
            B[i].append(match[i])
    for g in junk:
        if not any(g in b for b in B):
            B[o].append(g)
    return B, steps


if __name__ == '__main__':
    seed, N, n = map(int, sys.argv[1:4]); rng = random.Random(seed); C = collections.Counter()
    print('$ python3 k4/sdc/dt_check.py', *sys.argv[1:])
    while C['instances'] < N:
        m = rng.randint(n, 3 * n + 2)
        v = []
        for i in range(n):
            k = rng.choice([1, 2, 3, 4, 4, 4])
            S = rng.sample(range(m), min(k, m))
            vals = [rng.randint(1, 12) for _ in S]
            v.append(dict(zip(S, vals)))
        tops = [ranked(v, i)[0] for i in range(n)]
        if len(set(tops)) < n:
            continue
        C['instances'] += 1
        for o in range(n):
            B, steps = construct(n, m, v, o)
            assert raw_efx0(n, v, B), (v, o, B)
            assert all(val(v, i, B[i]) >= val(v, i, B[o]) for i in range(n) if i != o), 'owner envied'
            assert sum(1 for b in B if len(b) > 2) <= 1
            C['runs'] += 1; C['max moves'] = max(C['max moves'], steps - 1)
    print(dict(C), '-- every run EFX0, owner unenvied, at most one bundle of more than two goods')
