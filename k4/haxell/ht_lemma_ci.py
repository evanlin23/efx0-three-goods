"""Random check of Lemma CI (k4/haxell.md §4): in a partial EFX0 allocation S, for local moves e, f that change the
bundles of disjoint agent sets, touch disjoint goods, and lower no touched agent's value (holding-monotone), with e
victim-free (e(S) partial EFX0): the victims of f after e are among the victims of f before e.  Also counts, for
contrast, the violations when monotonicity is dropped.

    python3 k4/haxell/ht_lemma_ci.py SRC [TRIALS=200]"""
import sys, random, itertools, collections
from ht_lib import Inst, happy_vec, bundles, instances, generic_moves, apply


def agents_of(I, st, mv):
    st2 = apply(I, st, mv)
    return frozenset(a for g in range(I.m) for a in (st[0][g], st2[0][g]) if st[0][g] != st2[0][g] and a >= 0)


def monotone(I, st, mv):
    st2 = apply(I, st, mv); X, X2 = bundles(I, st[0]), bundles(I, st2[0])
    return all(I.val(i, X2[i]) >= I.val(i, X[i]) for i in range(I.n))


def victims(I, st, mv):
    h = happy_vec(I, st[0]); h2 = happy_vec(I, apply(I, st, mv)[0])
    return frozenset(i for i in range(I.n) if h[i] and not h2[i])


if __name__ == '__main__':
    args = dict(a.split('=') for a in sys.argv[2:] if '=' in a)
    trials = int(args.get('TRIALS', '200')); rng = random.Random(5)
    C = collections.Counter()
    print('$ python3 k4/haxell/ht_lemma_ci.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in instances(sys.argv[1]):
        if len(sets) > 4 or m > 8:
            continue
        I = Inst(sets, vals, m)
        for _ in range(trials):
            own = tuple(rng.randrange(-1, I.n) for _ in range(m))
            if not all(happy_vec(I, own)):
                continue
            st = (own, tuple([False] * m))
            mv = list(generic_moves(I, st, 1))
            if not mv:
                continue
            for _ in range(20):
                e, f = rng.choice(mv), rng.choice(mv)
                Ae, Af = agents_of(I, st, e), agents_of(I, st, f)
                ge = {g for g, _ in e[1]}; gf = {g for g, _ in f[1]}
                if Ae & Af or ge & gf:
                    continue
                if victims(I, st, e):
                    continue
                mono = monotone(I, st, e) and monotone(I, st, f)
                ok = victims(I, apply(I, st, e), f) <= victims(I, st, f)
                C['pairs, monotone' if mono else 'pairs, not monotone'] += 1
                if not ok:
                    C['VIOLATIONS, monotone' if mono else 'violations, not monotone'] += 1
    for k in sorted(C):
        print(k, C[k])
