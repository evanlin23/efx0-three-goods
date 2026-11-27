"""Independent re-check of the dead ends written by deadends.py (second implementation, for the refutation).

Self-contained: it imports nothing from this workstream (no bplib) or from k4/.  Goods are Python sets, values dicts,
and every test is written again from the raw definitions:
  * EFX0: for agents a != b and every good g of X_b, v_a(X_a) >= v_a(X_b - g);
  * a dangerous agent holds one good that another present agent values above its own bundle, and values a junk good;
  * a settlement: k dangerous, a chain k = x0, x1, .., xt of present agents, each x_l valuing x_{l-1}'s single good
    above its own, T inside the junk plus x_t's good, inside R_k, worth more than k's good; a round is one or two
    settlements with disjoint chains and disjoint T, applied at once;
  * admissible: no T threatens another agent present at the round's start at its value after the round, nor an earlier
    phantom at v(T_phantom); the reduced state is SD of some order (brute force over all orders and SD itself, ties
    broken by the smaller good);
  * one-absorber completion: one present owner takes any junk, every other present agent at most one junk good;
  * official move (k4/sdc.md section 29): any chain of >= 2 distinct present agents, x0 taking a set inside the junk
    plus the end's good (relevant to x0, improving), each later x_l taking x_{l-1}'s bundle plus relevant junk and
    gaining.

For every dead-end record it checks: the path of rounds is admissible from the start and reaches the stored state;
the state has no one-absorber completion, no admissible round and no official move followed by a one-absorber
completion; and the stored feasibility (some EFX0 allocation keeps every phantom's set) by enumerating every
allocation of the present goods to the present agents.

    python3 k4/base_phantom/check_deadends.py results/k4_base_phantom/deadends_NAME.jsonl.gz [STRIDE]
"""
import sys, json, gzip, itertools, collections


class Instance:
    def __init__(self, sets, vals):
        self.n = len(sets)
        self.goods = sorted(set(g for s in sets for g in s))
        self.v = [dict(zip(s, x)) for s, x in zip(sets, vals)]

    def val(self, a, S):
        return sum(self.v[a].get(g, 0) for g in S)

    def threatens(self, S, a, t):
        return any(self.val(a, set(S) - {g}) > t for g in S)

    def efx0(self, X):
        for a in range(self.n):
            va = self.val(a, X[a])
            for b in range(self.n):
                if a != b and self.threatens(X[b], a, va):
                    return False
        return True

    def sd(self, order, goods):
        left = set(goods)
        out = {}
        for a in order:
            mine = [g for g in left if self.v[a].get(g, 0) > 0]
            if mine:
                g = max(mine, key=lambda h: (self.v[a][h], -h))
                out[a] = g
                left.discard(g)
        return out


def present_goods(I, X, alive):
    dead = [a for a in range(I.n) if a not in alive]
    return set(I.goods) - set(g for a in dead for g in X[a])


def junk_of(I, X, alive):
    return present_goods(I, X, alive) - set(g for a in alive for g in X[a])


def one_absorber(I, X, alive):
    J = sorted(junk_of(I, X, alive))
    for o in alive:
        for lab in itertools.product(alive, repeat=len(J)):
            if any(lab.count(u) > 1 for u in alive if u != o):
                continue
            Y = [set(b) for b in X]
            for g, u in zip(J, lab):
                Y[u].add(g)
            if I.efx0(Y):
                return Y
    return None


def is_sd(I, X, alive):
    goods = present_goods(I, X, alive)
    if any(len(X[a]) != 1 for a in alive):
        return False
    tgt = {a: next(iter(X[a])) for a in alive}
    return any(I.sd(o, goods) == tgt and len(tgt) == len(alive) for o in itertools.permutations(alive))


def wants(I, X, a, g):
    return I.v[a].get(g, 0) > I.val(a, X[a])


def all_settlements(I, X, alive):
    J = junk_of(I, X, alive)
    out = []
    for k in alive:
        if len(X[k]) != 1:
            continue
        y = next(iter(X[k]))
        if not any(a != k and wants(I, X, a, y) for a in alive):
            continue
        if not any(I.v[k].get(g, 0) > 0 for g in J):
            continue
        chains = []
        stack = [(k,)]
        while stack:
            P = stack.pop()
            last = X[P[-1]]
            if len(last) != 1:
                continue
            g = next(iter(last))
            for w in alive:
                if w not in P and wants(I, X, w, g):
                    chains.append(P + (w,))
                    stack.append(P + (w,))
        for P in chains:
            pool = sorted(g for g in J | X[P[-1]] if I.v[k].get(g, 0) > 0)
            for r in range(1, len(pool) + 1):
                for T in itertools.combinations(pool, r):
                    if I.val(k, T) > I.val(k, X[k]):
                        out.append((k, P, frozenset(T)))
    return out


def admissible_rounds(I, X, alive):
    """Every admissible round: (settlements, new X, new alive)."""
    S = all_settlements(I, X, alive)
    dead = [a for a in range(I.n) if a not in alive]
    res = []
    for r in (1, 2):
        for combo in itertools.combinations(S, r):
            ags = [a for _, P, _ in combo for a in P]
            if len(ags) != len(set(ags)):
                continue
            if r == 2 and combo[0][2] & combo[1][2]:
                continue
            Y = [set(b) for b in X]
            for k, P, T in combo:
                Y[k] = set(T)
                for l in range(1, len(P)):
                    Y[P[l]] = set(X[P[l - 1]])
            bad = False
            for k, P, T in combo:
                for a in alive:
                    if a != k and I.threatens(T, a, I.val(a, Y[a])):
                        bad = True
                for f in dead:
                    if I.threatens(T, f, I.val(f, X[f])):
                        bad = True
            if bad:
                continue
            K = set(k for k, _, _ in combo)
            al2 = [a for a in alive if a not in K]
            if al2 and not is_sd(I, Y, al2):
                continue
            res.append((combo, Y, al2))
    return res


def official_moves(I, X, alive):
    J = junk_of(I, X, alive)
    for L in range(2, len(alive) + 1):
        for P in itertools.permutations(alive, L):
            pool0 = sorted(g for g in J | X[P[-1]] if I.v[P[0]].get(g, 0) > 0)
            for r in range(1, len(pool0) + 1):
                for H0 in itertools.combinations(pool0, r):
                    if I.val(P[0], H0) <= I.val(P[0], X[P[0]]):
                        continue
                    rest = sorted(J - set(H0))

                    def mids(l, avail, acc):
                        if l == L:
                            yield acc
                            return
                        x = P[l]
                        rel = [g for g in avail if I.v[x].get(g, 0) > 0]
                        for rr in range(0, len(rel) + 1):
                            for H in itertools.combinations(rel, rr):
                                if I.val(x, set(X[P[l - 1]]) | set(H)) > I.val(x, X[x]):
                                    yield from mids(l + 1, [g for g in avail if g not in H], acc + [set(H)])
                    for Hs in mids(1, rest, []):
                        Y = [set(b) for b in X]
                        Y[P[0]] = set(H0)
                        for l in range(1, L):
                            Y[P[l]] = set(X[P[l - 1]]) | Hs[l - 1]
                        yield P, H0, Hs, Y


def feasible(I, X, alive):
    goods = sorted(present_goods(I, X, alive))
    for lab in itertools.product(alive, repeat=len(goods)):
        Y = [set(b) for b in X]
        for a in alive:
            Y[a] = set()
        for g, a in zip(goods, lab):
            Y[a].add(g)
        if I.efx0(Y):
            return True
    return False


def check(d):
    I = Instance(d['sets'], d['vals'])
    X = [{g} for g in d['picks']]
    alive = list(range(I.n))
    assert one_absorber(I, X, alive) is None or d['path'], 'start'
    for rnd in d['path']:
        want = sorted((k, tuple(P), tuple(sorted(T))) for k, P, T in rnd)
        hit = None
        for combo, Y, al2 in admissible_rounds(I, X, alive):
            if sorted((k, P, tuple(sorted(T))) for k, P, T in combo) == want:
                hit = (Y, al2)
                break
        assert hit is not None, 'round not admissible'
        X, alive = hit
    assert [sorted(b) for b in X] == [sorted(b) for b in d['B']] and alive == d['alive'], 'state mismatch'
    assert one_absorber(I, X, alive) is None, 'completion exists'
    assert not admissible_rounds(I, X, alive), 'an admissible round exists'
    has_move = False
    for P, H0, Hs, Y in official_moves(I, X, alive):
        if one_absorber(I, Y, alive) is not None:
            has_move = True
            break
    assert has_move == (d['base'] is not None), 'one-move repair mismatch'
    assert feasible(I, X, alive) == d['feasible'], 'feasibility mismatch'
    # does some phantom keep an "l alone" constraint on a present agent's base (a good outside its set worth more
    # to it than its set, held alone or with others by a present agent)?
    lock = any(any(I.v[f][g] > I.val(f, X[f]) for a in alive for g in X[a] if g in I.v[f] and g not in X[f])
               for f in range(I.n) if f not in alive)
    return len(d['path']), d['feasible'], d['base'] is not None, lock


if __name__ == '__main__':
    fn = sys.argv[1]
    stride = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    print('$ python3 k4/base_phantom/check_deadends.py', fn, stride)
    import multiprocessing as mp
    C = collections.Counter()
    recs = [json.loads(line) for t, line in enumerate(gzip.open(fn, 'rt')) if t % stride == 0]
    with mp.Pool(4) as pool:
        for depth, feas, mv, lock in pool.imap_unordered(check, recs, chunksize=32):
            C['verified: %d rounds, feasible %s, one-move repair %s' % (depth, feas, mv)] += 1
            if depth:
                C['  with phantoms: some phantom has an "l alone" constraint on a present base: %s' % lock] += 1
    for k in sorted(C):
        print('  %7d  %s' % (C[k], k))
    print('all records verified:', sum(v for k, v in C.items() if k.startswith('verified')))
