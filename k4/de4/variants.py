"""Replays the refutations of the simpler variants of DE4 (attempts/k4-de4-variants.md). Each check prints
'confirmed' or 'NOT confirmed'. Exit status 0 iff all are confirmed.  python3 k4/de4/variants.py"""
import itertools
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from de4lib import *  # noqa: F401,F403
from check import SUITE

ok_all = True


def report(name, ok, detail=''):
    global ok_all
    ok_all &= ok
    print(('confirmed    ' if ok else 'NOT confirmed') + ' ' + name + (': ' + detail if detail else ''))


def inst(name):
    return Inst.from_json(json.load(open(os.path.join(SUITE, name + '.json'))))


def all_efx0(I):
    return [bundles(I, own) for own in itertools.product(range(I.n), repeat=I.m) if efx0(I, bundles(I, own))]


def states_with(I, allowed_fn):
    opts = [[A for A in subsets(I.sets[i]) if allowed_fn(I, i, A)] for i in range(I.n)]
    out = []
    for Y in itertools.product(*opts):
        if len(set(g for A in Y for g in A)) == sum(map(len, Y)) and valid(I, list(Y)):
            out.append(list(Y))
    return out


# 1. DE's own holdings (empty, single goods, sets without the top worth more than the top): too few at k = 4.
I = inst('adaptive-cover-multi4')
X = all_efx0(I)
def de_shape(I, i, B):
    A = [g for g in B if g in I.v[i]]
    top = I.ranked(i)[0]
    return len(A) <= 1 or (top not in A and I.val(i, A) > I.v[i][top])
report('V1 DE holdings: two identical 4-good agents (values 2,4,5,8) have no EFX0 allocation of that shape',
       bool(X) and not any(all(de_shape(I, i, X0[i]) for i in range(I.n)) for X0 in X),
       f'{len(X)} EFX0 allocations, all of the form top+lowest | middle pair: {X}')

# 2. Upper sets only (no lower pair): some maximum (level sum, then Pareto) is not completable.
def upper_only(I, i, A):
    return len(A) <= 1 or is_upper(I, i, A)
I = inst('red-a1-hopeless-key')
st = states_with(I, upper_only)
best = max(levsum(I, Y) for Y in st)
mx = pareto_max(I, [Y for Y in st if levsum(I, Y) == best])
bad = [Y for Y in mx if completion(I, Y) is None]
report('V2 upper sets only (no lower pair {c,d}): a maximum is not completable', bool(bad),
       f'red-a1-hopeless-key, maxima {mx}, not completable {bad}')

# 3. All minimal sets beating a single value (e.g. {b,d} worth more than c): contains the dead end of
#    attempts/k4-ls-dead-end.md, which is value-Pareto-maximal there and has no completion.
I = inst('ls-dead-end-n4m7')
Y = [(2,), (6,), (1, 4), (3, 5)]
def ms(I, i, A):
    if len(A) <= 1:
        return True
    vA = I.val(i, A)
    mp_ = max(I.val(i, T) for T in subsets(A) if 0 < len(T) < len(A))
    return any(vA > t >= mp_ for t in I.v[i].values())
st = states_with(I, ms)
dom = [Z for Z in st if all(a >= b for a, b in zip(values(I, Z), values(I, Y))) and values(I, Z) != values(I, Y)]
report('V3 every minimal set beating some single value: the LS dead end is a valid, Pareto-maximal, non-completable state',
       Y in [list(map(tuple, Z)) for Z in st] and not dom and completion(I, Y) is None,
       f'Y = {Y}, values {values(I, Y)}; Y is not a DE4 state ({{1,4}} is b+d < a for agent 2)')

# 4. DE4 states but value-Pareto maxima (no level sum): gm4-B has a Pareto-maximal state that is not completable.
I = inst('gm4-B')
st = all_states(I)
pm = pareto_max(I, st)
bad = [Y for Y in pm if completion(I, Y) is None]
report('V4 DE4 states, value-Pareto maxima: a maximum is not completable', bool(bad),
       f'gm4-B, {bad}, levels {[[level(I, i, Y[i]) for i in range(I.n)] for Y in bad]}')

# 5. DE's single-owner finishing rule: a DE4 maximum of hall-cyc6 needs two agents to take leftover goods.
I = inst('hall-cyc6')
mx = maxima(I, all_states(I))
bad = [Y for Y in mx if de_finish(I, Y) is None]
report('V5 DE single-owner finishing at DE4 maxima', bool(bad) and all(completion(I, Y) is not None for Y in bad),
       f'hall-cyc6: {bad[0] if bad else None} is a maximum; completion {completion(I, bad[0]) if bad else None}')

# 6. Owners restricted to agents holding at most one good (as in DE).
I = inst('induct-g-r1')
mx = maxima(I, all_states(I))
def finish_small_owner(I, Y):
    J = leftover(I, Y)
    W = wanted_goods(I, Y)
    for o in range(I.n):
        if set(Y[o]) & W or len(Y[o]) > 1:
            continue
        for assign in itertools.product(range(I.n), repeat=len(J)):
            X = [list(A) for A in Y]
            for g, i in zip(J, assign):
                X[i].append(g)
            big = [i for i in range(I.n) if len(X[i]) > 2 and i != o]
            if not big and efx0(I, X):
                return X
    return None
report('V6 owner must hold at most one good', all(finish_small_owner(I, Y) is None for Y in mx),
       f'induct-g-r1 (n = 2): every maximum {mx} has both agents holding a pair and one leftover good')

# 7. DE's ring with distinct leftover goods chosen greedily for *all* free agents (pair holders included): along the
#    algorithm's run, a free agent holding two goods takes the only usable leftover good, and no ring is built;
#    with DE's rule proper (greedy over the free agents holding at most one good) the ring exists.
from check import draft, better
for sets, vals in [([[0, 2, 4, 5], [1, 5, 6, 7], [3, 5, 6, 7], [4, 6, 7]], [[2, 3, 8, 4], [7, 8, 4, 2], [7, 2, 4, 8], [3, 2, 4]]),
                   ([[0, 3, 5, 6], [1, 4, 5, 6], [2, 3, 4, 5], [2, 3, 4, 6]], [[7, 4, 2, 8], [4, 8, 5, 6], [4, 3, 8, 6], [1, 4, 8, 6]])]:
    I = Inst(sets, vals)
    Y = draft(I)
    ok = de_finish(I, Y) is None
    Y = chain_move(I, Y)
    ok &= Y is not None and de_finish(I, Y) is None and chain_move(I, Y) is None
    Zall = pointer_ring(I, Y, lazy=False)
    Z1 = pointer_ring(I, Y, lazy=False, f1_only=True)
    ok &= (Zall is None or not better(I, Y, Zall)) and Z1 is not None and better(I, Y, Z1)
    report('V7 DE ring with the greedy over all free agents (n = 4)', ok,
           f'state after draft and chain {Y}; greedy over all free agents: {Zall}; greedy over F1: {Z1}')

# 8. Conjecture 11 of k4/de4.md in its first form (the walk stops => move P or move K): a stopped walk (n = 4, m = 8)
#    with neither; the refined walk (keep-own arcs, cycle-closing arcs first) gives a strict Pareto improvement.
from cycle import walk, walk2, partial_paths, keep_own_exchanges, strictly_pareto
I = Inst([[0, 1, 4, 5], [1, 3, 6, 7], [2, 3, 4, 7], [2, 5, 6, 7]], [[2, 8, 4, 5], [10, 8, 6, 3], [4, 2, 10, 7], [10, 3, 8, 4]])
Y = [(0, 4), (1,), (2, 7), (5, 6)]
st, _, _ = walk(I, Y)
st2, Z2, _ = walk2(I, Y)
ok = (valid(I, Y) and completion(I, Y) is None and chain_move(I, Y) is None and st == 'F2 stuck'
      and not any(True for _ in partial_paths(I, Y)) and not any(True for _ in keep_own_exchanges(I, Y))
      and st2 == 'ok' and strictly_pareto(I, Y, Z2))
report('V8 Conjecture 11 with moves P and K only', ok,
       f'Y = {Y} (values {values(I, Y)}): walk stops, no P, no K; refined walk gives {Z2} (values {values(I, Z2) if Z2 else None})')

sys.exit(0 if ok_all else 1)
