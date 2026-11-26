"""The k <= 4 steps of Theorem DT and Theorem DT1 (k4/sdc.md §6, §30) fail at k = 5 (k4/ksens.md §3).  Each claim
is checked twice: by SAT (ocsat.py / dt1_k5.gdt_completion, EFX0 clauses of k4/sdc/sdclib.py) and by brute force
over every complete allocation against the raw EFX0 definition (brute.py).

1. DT5: distinct tops, n = 2, m = 6: the picks (the tops) have no one-absorber completion, for either owner (Theorem
   DT's conclusion, hence Theorem DT+ and Lemma GDT with no pair holders and no frozen agent); a free completion
   exists, and OC1 holds by a chain with t = 0.  The k = 4 version (one junk good less) has one.
2. DT1-5: n = 3, m = 8, one frozen agent x wanted by exactly one agent w, an improving pair H0: after the swap, Lemma
   GDT's completion with the only owner outside {x, w} does not exist (Theorem DT1's conclusion), because x's two
   other goods are both unallocated (GDT's hypothesis (G3) fails); one-absorber completions of another shape exist.

    python3 k4/ksens/refute_dt_k5.py"""
import json
import numpy as np
import _paths
import ocsat, brute
from dt1_k5 import gdt_completion

DT5 = ([[0, 2, 3, 4, 5], [1, 2, 3, 4, 5]], [[100, 91, 92, 93, 94], [100, 94, 93, 92, 91]])
DT4 = ([[0, 2, 3, 4], [1, 2, 3, 4]], [[100, 91, 92, 93], [100, 93, 92, 91]])
DT1_5 = ([[1, 2, 3, 6, 7], [0, 1, 2, 4, 7], [2, 3, 4, 5, 7]], [[33, 19, 27, 18, 28], [22, 32, 14, 26, 28], [6, 5, 9, 14, 10]])


def brute_shape(I, bases, owner, nojunk=()):
    """number of complete EFX0 allocations keeping bases, no junk for agents in nojunk, at most one junk good for
    every other agent except owner (brute force)"""
    L = I.efx0_list(); ok = np.ones(len(L), dtype=bool); inb = np.zeros(I.m, dtype=bool)
    for i, b in enumerate(bases):
        for g in b: ok &= L[:, g] == i; inb[g] = True
    for i in range(I.n):
        jk = ((L == i) & ~inb).sum(1)
        if i in nojunk: ok &= jk == 0
        elif i != owner: ok &= jk <= 1
    return int(ok.sum())


if __name__ == '__main__':
    print('$ python3 k4/ksens/refute_dt_k5.py')
    for name, (sets, vals), m in (('DT5', DT5, 6), ('DT4', DT4, 5)):
        I = brute.Inst(sets, vals, m); O = ocsat.OC(sets, vals, m)
        Y = ocsat.sd(sets, vals, (0, 1), m); b = ocsat.bases_of(Y, 2)
        sat1 = O.holds(b, chain='none', A=1); sat_free = O.holds(b, chain='none'); sat_oc1 = O.holds(b, chain='need', A=1)
        br = [brute_shape(I, b, o) for o in range(2)]
        print('%s %s: picks %s; one-absorber completion: SAT %s, brute force (owner 0, owner 1) %s; free completion SAT %s, '
              'brute %s; one chain then one absorber (OC1) SAT %s' % (name, json.dumps((sets, vals)), Y, sat1, br, sat_free,
              I.completes(b), sat_oc1))
        if name == 'DT5': assert not sat1 and br == [0, 0] and sat_free and sat_oc1
        else: assert sat1 and min(br) > 0
        O.close()
    sets, vals = DT1_5; m = 8; I = brute.Inst(sets, vals, m); O = ocsat.OC(sets, vals, m)
    Y = ocsat.sd(sets, vals, (0, 1, 2), m)
    x, w, o, H0 = 0, 1, 2, (3, 6)
    v = [dict(zip(s, vv)) for s, vv in zip(sets, vals)]
    print('DT1-5 %s: order (0, 1, 2), picks %s' % (json.dumps(DT1_5), Y))
    wants = [(i, j) for i in range(3) for j in range(3) if i != j and v[i].get(Y[j], 0) > v[i][Y[i]]]
    print('   wants (i wants the pick of j):', wants, '; so x = 0 is the only frozen agent and w = 1 its only wanter')
    assert wants == [(1, 0)]
    print('   x values H0 = %s at %d > its pick %d' % (H0, v[x][3] + v[x][6], v[x][Y[x]]))
    bases = [list(H0), [Y[x]], [Y[o]]]
    J = [g for g in range(m) if not any(g in b for b in bases)]
    print('   after the swap: bases %s, junk %s; x values its other goods 2 and 7 at %d + %d = %d > %d (GDT (G3) fails)' %
          (bases, J, v[x][2], v[x][7], v[x][2] + v[x][7], v[x][3] + v[x][6]))
    s = gdt_completion(O, bases, x, o, J); bshape = brute_shape(I, bases, o, nojunk=(x,))
    print('   GDT completion with owner %d: SAT %s, brute force %d allocations' % (o, s, bshape))
    s1 = O.holds(bases, chain='none', A=1); b1 = I.completes(bases, 1)
    print('   any one-absorber completion of the swapped state: SAT %s, brute %s' % (s1, b1))
    assert not s and bshape == 0 and s1 and b1
    O.close()
    print('OK: Theorem DT and Theorem DT1 fail at k = 5 as stated; the k = 4 version of DT5 completes')
