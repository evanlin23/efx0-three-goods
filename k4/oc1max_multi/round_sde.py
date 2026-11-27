"""Lemma SD-E for a round, and (L*) at the end of a round (k4/oc1max_multi.md §17; ROUND-RSD's proof tools).

A round settles a set K of dangerous agents at once: vertex-disjoint earliest-wanter chains E(k) (k in K, all computed at
the picks of the order), each k taking an improving set T_k (|T_k| <= 3, inside J + {Y_{z_k}}, pairwise disjoint).
  SD-E(round): after the round, without K and the T_k, the state is the SD outcome of the order minus K.
  (L*)-round: no T_k threatens any other agent at its value after the round (real agents at their new values, the
  other members of K at tau_k' = v_k'(T_k')).
With PREFIX=1 each chain may be any prefix of E(k) (its head may be frozen at the picks, its wanters being served by
the round); SD-E(round) is then checked, not assumed.
Census at every start of a file: every round with |K| = 2 (and the single settlements, |K| = 1); SD-E(round) checked
against the SD outcome; for rounds meeting (L*)-round, whether the reduced start completes at once (every one-absorber
completion, lifted, raw EFX0 in the full instance) or after one Theorem S move (S^phi, raw).

    python3 k4/oc1max_multi/round_sde.py ROWS.jsonl[.gz]    (rows: sets, vals, picks, orders or order)
"""
import sys, os, json, gzip, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, dangerous
from reduce_s import earliest_chain
from theorem_s import s_cases
from sphi import all_oa

PREFIX = os.environ.get('PREFIX') == '1'


def reduce_many(I, nb, K):
    """delete agents K and the goods they hold at nb; returns (I2, b2, keep agents, kept goods)"""
    gone = set(g for k in K for g in nb[k]); goods = [g for g in range(I.m) if g not in gone]; new = {g: i for i, g in enumerate(goods)}
    keep = [i for i in range(I.n) if i not in K]
    I2 = Inst([[new[g] for g in I.sets[i] if g not in gone] for i in keep], [[I.v[i][g] for g in I.sets[i] if g not in gone] for i in keep], len(goods))
    return I2, tuple(tuple(new[g] for g in nb[i]) for i in keep), keep, goods


def rounds(I, b, order, size):
    J = junk(I, b); p = [I.V(i, b[i]) for i in range(I.n)]; D = dangerous(I, b)
    opts = {}
    for k in D:
        E = earliest_chain(I, b, k, order)
        opts[k] = []
        for t in range(1, len(E)):                       # PREFIX=1: every prefix E(k)[:t+1] (the head may be frozen)
            if not PREFIX and t != len(E) - 1: continue
            P = E[:t + 1]; pool = [g for g in J + [b[P[-1]][0]] if g in I.R[k]]
            opts[k] += [(P, T) for r in (2, 3) for T in itertools.combinations(pool, r) if I.V(k, T) > p[k]]
    for K in itertools.combinations(D, size):
        for choice in itertools.product(*[opts[k] for k in K]):
            Ps = [c[0] for c in choice]; Ts = [c[1] for c in choice]
            if len(set(a for P in Ps for a in P)) != sum(len(P) for P in Ps): continue    # vertex-disjoint
            if len(set(g for T in Ts for g in T)) != sum(len(T) for T in Ts): continue    # disjoint sets
            nb = [list(x) for x in b]
            for k, P, T in zip(K, Ps, Ts):
                nb[k] = sorted(T)
                for i in range(1, len(P)): nb[P[i]] = list(b[P[i - 1]])
            yield K, Ps, Ts, tuple(tuple(x) for x in nb)


def study(rec, size):
    I = Inst(rec['sets'], rec['vals']); b = base_from_picks(tuple(rec['picks'])); C = collections.Counter(); rep = set()
    for order in (rec.get('orders') or [rec['order']]):
        for K, Ps, Ts, nb in rounds(I, b, order, size):
            C['rounds'] += 1
            I2, b2, keep, goods = reduce_many(I, nb, K)
            oo = [keep.index(a) for a in order if a not in K]
            val = [I.V(i, nb[i]) for i in range(I.n)]; taken = set(g for T in Ts for g in T)
            rel = [b[P[-1]][0] for P in Ps if b[P[-1]][0] not in taken]
            H = all(I.v[a].get(y, 0) <= val[a] for y in rel for a in range(I.n) if a not in K and I.v[a].get(y, 0) > I.V(a, b[a]))
            sde = I2.sd(oo) == tuple(x[0] if x else None for x in b2)
            C['(H) holds' if H else '(H) fails'] += 1
            if H and not sde: C['SD-E(round) VIOLATION with (H)'] += 1
            if not sde: C['SD-E(round) fails'] += 1; continue
            C['SD-E(round) holds'] += 1
            if any(I.threat(i, val[i], T) for k, T in zip(K, Ts) for i in range(I.n) if i != k): C['(L*)-round fails'] += 1; continue
            C['(L*)-round holds'] += 1
            fixed = {k: list(T) for k, T in zip(K, Ts)}
            def lifted(X):
                A = [list(fixed.get(a, [])) for a in range(I.n)]
                for j, a in enumerate(keep): A[a] = [goods[g] for g in X[j]]
                return I.efx0(A)
            if any(lifted(X) for X in all_oa(I2, b2)): rep.add('round, then completion at once'); C['repair: completion at once'] += 1
            elif any(X is not None and lifted(X) for *_, X, how in s_cases(I2, b2, dangerous(I2, b2), True, True)):
                rep.add('round, then a Theorem S move'); C['repair: Theorem S move'] += 1
    return C, rep


if __name__ == '__main__':
    print('$ PREFIX=%d python3 k4/oc1max_multi/round_sde.py' % PREFIX, *sys.argv[1:])
    for fn in sys.argv[1:]:
        for size in (1, 2):
            T = collections.Counter(); R = collections.Counter(); nos = []
            for line in (gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn)):
                rec = json.loads(line); C, rep = study(rec, size); T.update(C); T['starts'] += 1
                for x in rep: R[x] += 1
                if rep: R['starts repaired by a round of this size'] += 1
                else: nos.append('%s#%s' % (rec.get('list', ''), rec.get('idx', '')))
            print('== |K| = %d:' % size, dict(T), dict(R), 'not repaired:', nos[:10], '(%d)' % len(nos))
