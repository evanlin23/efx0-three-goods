"""Lemma ABS' (k4/RFMIN.md §6): Lemma ABS at a general state. Test it, and test "after one move, ABS' applies", at the
RF-PRIV gap starts (random strict connected k = 4 cores with a private-top agent f; maximum-matching starts whose picks
have no one-absorber completion; the same generator and seeds as privtop_gap.py).

ABS' hypotheses at a state B, for an agent f:
  (A0) B_f = {p}, and nobody else values p;
  (A1) (G2): v_i(g) <= v_i(B_i) for every free good g and every agent i;
  (A2) (G1): no bundle B_q of two or more goods (q != f) threatens anybody: max_h v_i(B_q - h) <= v_i(B_i);
  (A3) every non-receiver i != f values the free goods at most its bundle: v_i(J) <= v_i(B_i). A receiver is an agent
       with at most one good that nobody else wants.
Construction: the receivers in turn take their most valuable free good if they value the free goods above their
bundle; f takes the rest. Every construction is checked by the raw EFX0 definition (Inst.efx0).
Usage: privtop_absp.py N SEED NMIN NMAX"""
import sys, os, random, itertools, collections, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sdc'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oc1_mc2_rand import Inst, gen
from privtop_random import nu
from multiprocessing import Pool


def absp(I, B, f):
    """None if ABS' hypotheses fail at B for f (with the reason), else the constructed allocation."""
    n, v, V = I.n, I.v, I.V
    J = [g for g in range(I.m) if all(g not in b for b in B)]
    b = [V(i, B[i]) for i in range(n)]
    if len(B[f]) != 1 or any(i != f and v[i].get(B[f][0], 0) > 0 for i in range(n)): return 'A0', None
    if any(v[i].get(g, 0) > b[i] for g in J for i in range(n)): return 'A1', None
    for q in range(n):
        if q != f and len(B[q]) >= 2:
            for i in range(n):
                if i != q and max(V(i, [x for x in B[q] if x != h]) for h in B[q]) > b[i]: return 'A2', None
    recv = [r for r in range(n) if r != f and len(B[r]) <= 1 and all(i == r or V(i, B[r]) <= b[i] for i in range(n))]
    bad = [i for i in range(n) if i != f and i not in recv and V(i, J) > b[i]]
    if bad: return 'A3', bad
    X = [list(x) for x in B]; free = list(J)
    for r in recv:
        if V(r, free) > b[r]:
            g = max(free, key=lambda g: v[r].get(g, 0)); X[r].append(g); free.remove(g)
    X[f] += free
    return 'ok', X


def job(args):
    n, seed = args
    rng = random.Random(seed)
    while True:
        try: sets, vals = gen(n, rng)
        except ValueError: continue
        deg = collections.Counter(g for S in sets for g in S)
        pt = [a for a in range(n) if deg[sets[a][vals[a].index(max(vals[a]))]] == 1]
        if pt: break
    I = Inst(sets, vals); N = nu(I); f = pt[0]
    C = collections.Counter(); ex = []
    for pk in set(I.sd(o) for o in itertools.permutations(range(n))):
        if sum(x is not None for x in pk) != N: continue
        base = [[g] if g is not None else [] for g in pk]
        why, X = absp(I, base, f)
        C['max starts'] += 1
        C['  at the picks: ABS\' %s' % why] += 1
        if why == 'ok':
            assert I.efx0(X), ('ABS\' construction not EFX0', sets, vals, pk)
            C['  at the picks: ABS\' construction EFX0 (raw)'] += 1
            continue
        if I.one_absorber(base): C['  at the picks: ABS\' fails, but a one-absorber completion exists'] += 1; continue
        C['gap starts (picks do not complete)'] += 1
        J = set(range(I.m)) - {g for g in pk if g is not None}
        frozen = [a for a in range(n) if pk[a] is not None and any(
            i != a and I.v[i].get(pk[a], 0) > I.V(i, base[i]) for i in range(n))]
        D = [a for a in frozen if I.V(a, J) > I.v[a][pk[a]]]
        kinds, reasons = set(), collections.Counter()
        for st in I.moves(base):
            st = [list(x) for x in st]
            ch = tuple(sorted(a for a in range(n) if sorted(st[a]) != sorted(base[a])))
            why, X = absp(I, st, f)
            reasons[why] += 1
            if why != 'ok': continue
            assert I.efx0(X), ('ABS\' construction not EFX0', sets, vals, pk, st)
            C['  states where ABS\' applies; construction EFX0 (raw)'] += 1
            k = 'other'
            if len(ch) == 2:
                d = next((a for a in ch if pk[a] is not None and set(st[a]) <= J), None)
                w = next((a for a in ch if a != d), None)
                if d is not None and pk[d] in st[w] and len(st[w]) == 1:
                    k = 'chain d -> w: d %s, w %s, |H0| = %d' % ('in D_full' if d in D else 'not in D_full',
                                                             'frozen' if w in frozen else 'unfrozen', len(st[d]))
            elif len(ch) == 1: k = 'one agent adds junk'
            else: k = 'chain of %d agents' % len(ch)
            kinds.add(k)
        if kinds:
            C['ABS\' applies after some move'] += 1
            for k in kinds: C['  ABS\' after: %s' % k] += 1
            if any(k.startswith('chain d -> w') and 'w unfrozen' in k for k in kinds):
                C['  ABS\' after a chain d -> w with w unfrozen'] += 1
        else:
            C['ABS\' applies after no move'] += 1
            for r, x in reasons.items(): C['  no-ABS\' start: states failing %s' % r] += 1
            if len(ex) < 4: ex.append((sets, vals, pk, f))
    return C, ex


if __name__ == '__main__':
    N, seed, nmin, nmax = map(int, sys.argv[1:5])
    T = collections.Counter(); exs = []
    with Pool(4) as pool:
        for C, ex in pool.imap_unordered(job, [(nmin + i % (nmax - nmin + 1), seed * 1000003 + i) for i in range(N)]):
            T.update(C); exs += ex
    print('ABS\' on random private-top cores: %d instances, n = %d..%d, seed %d' % (N, nmin, nmax, seed))
    for k, x in sorted(T.items()): print('  %-62s %d' % (k, x))
    for e in exs[:6]: print('  example', json.dumps(e))
