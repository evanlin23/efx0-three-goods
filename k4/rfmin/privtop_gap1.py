"""Lemma GAP1 and the profile of the RF-PRIV gap starts with one dangerous agent (k4/RFMIN.md §6).

Random private-top cores (the generator and seeds of privtop_gap.py). At every maximum-matching start with
D_full = {d} (d frozen with v_d(J) > p_d, every other frozen agent valuing the junk at most its pick):
  - the parking construction P(r, h) is run for every receiver r != f and every admissible h in J_d (v_d(J_d - h) <= p_d):
    r takes h, the other receivers greedily take their best free good if they value the free goods above their pick, f
    takes the rest. Lemma GAP1 (1): it fails only through r's own safety (asserted on every run);
  - at gap starts (no one-absorber completion at the picks, Inst.one_absorber), Lemma GAP1 (2), (3) are asserted:
    (2) at most one pickless agent, and if one, no admissible h; (3) if some h is admissible, every unfrozen pick holder
    r != f that wants some pick values exactly four goods: its pick, a wanted pick, and two junk goods, neither admissible, worth more than its
    pick together;
  - the profile: |J_d|, pickless agents, whether d holds its top.
Usage: privtop_gap1.py N SEED NMIN NMAX"""
import sys, os, random, itertools, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sdc'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oc1_mc2_rand import Inst, gen
from privtop_random import nu
from privtop_absp import absp
from multiprocessing import Pool


def park(I, base, f, r, h, J, recv):
    X = [list(b) for b in base]; free = [g for g in J if g != h]; X[r].append(h)
    for q in recv:
        if q != r and free and I.V(q, free) > I.V(q, base[q]):
            g = max(free, key=lambda g: I.v[q].get(g, 0)); X[q].append(g); free.remove(g)
    X[f] += free
    return X, free


def job(args):
    n, seed = args
    rng = random.Random(seed)
    while True:
        try: sets, vals = gen(n, rng)
        except ValueError: continue
        deg = collections.Counter(g for S in sets for g in S)
        pt = [a for a in range(n) if deg[sets[a][vals[a].index(max(vals[a]))]] == 1]
        if pt: break
    I = Inst(sets, vals); N = nu(I); f = pt[0]; C = collections.Counter()
    for pk in set(I.sd(o) for o in itertools.permutations(range(n))):
        if sum(x is not None for x in pk) != N: continue
        base = [[g] if g is not None else [] for g in pk]
        if absp(I, base, f)[0] == 'ok': continue
        J = sorted(set(range(I.m)) - {g for g in pk if g is not None})
        p = [I.V(i, base[i]) for i in range(n)]
        wants = lambda i, a: i != a and pk[a] is not None and I.v[i].get(pk[a], 0) > p[i]
        frozen = lambda a: any(wants(i, a) for i in range(n))
        D = [a for a in range(n) if pk[a] is not None and frozen(a) and I.V(a, J) > p[a]]
        if len(D) != 1: continue
        d = D[0]; Jd = [g for g in J if g in I.R[d]]
        adm = [h for h in Jd if I.V(d, [g for g in Jd if g != h]) <= p[d]]
        recv = [r for r in range(n) if r != f and not frozen(r)]
        for r in recv:
            for h in adm:
                X, F = park(I, base, f, r, h, J, recv)
                ok = I.efx0(X)
                C['  P(r, h) runs'] += 1
                # GAP1 (1): the only possible failure is r against f's bundle
                if not ok:
                    assert I.V(r, F) > p[r] + I.v[r].get(h, 0), ('GAP1 (1)', sets, vals, pk, r, h)
                    Y = [list(x) for x in X]; Y[f] = list(base[f])
                    C['  P(r, h) runs failing, each only through r against f\'s bundle'] += 1
        gap = not I.one_absorber(base)
        C['%s starts with |D_full| = 1' % ('gap' if gap else 'non-gap')] += 1
        if not gap: continue
        pickless = [i for i in range(n) if pk[i] is None]
        assert len(pickless) <= 1 and (not pickless or not adm), ('GAP1 (2)', sets, vals, pk)
        for r in recv:
            if not adm or pk[r] is None or not any(wants(r, a) for a in range(n)): continue
            Jr = [g for g in J if g in I.R[r]]
            assert len(I.R[r]) == 4 and len(Jr) == 2 and not set(Jr) & set(adm) and I.V(r, Jr) > p[r], ('GAP1 (3)', sets, vals, pk, r)
            C['  gap: unfrozen wanting pick holders checked for GAP1 (3)'] += 1
        top = max(I.R[d], key=lambda g: I.v[d][g]) == pk[d]
        C['  gap profile: |J_d| = %d, pickless %d, d holds its top %s, admissible goods %d' % (
            len(Jd), len(pickless), top, len(adm))] += 1
    return C


if __name__ == '__main__':
    N, seed, nmin, nmax = map(int, sys.argv[1:5])
    T = collections.Counter()
    with Pool(4) as pool:
        for C in pool.imap_unordered(job, [(nmin + i % (nmax - nmin + 1), seed * 1000003 + i) for i in range(N)]):
            T.update(C)
    print('Lemma GAP1 and the one-dangerous-agent profile: %d cores, n = %d..%d, seed %d' % (N, nmin, nmax, seed))
    for k, x in sorted(T.items()): print('  %-80s %d' % (k, x))
