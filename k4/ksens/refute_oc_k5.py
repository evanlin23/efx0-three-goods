"""OC and OC1 are false at k = 5 (k4/ksens.md §1): the instance PW5 (n = 5, m = 9).

Agents 0, 1, 2 (x_1, x_2, x_3): x_j values its good p_j = j at 10 and the shared pool D = {5, 6, 7, 8} at 9, 8, 7, 6.
Agents 3, 4 (w_1, w_2): each values p_1, p_2, p_3 at 6, 4, 2 and its own good q_i (3, resp. 4) at 1.
Order (0, 1, 2, 3, 4): picks p_1, p_2, p_3, q_1, q_2; the junk is D.

Two independent checks of "neither the picks nor any state one improving chain reaches extends to a complete EFX0
allocation (free completion, hence also with one absorber)":
  1. ocsat.py: one SAT call (chain encoded in SAT, EFX0 clauses of k4/sdc/sdclib.py);
  2. brute.py: every complete allocation (5^9) checked against the raw EFX0 definition with numpy, every improving
     chain enumerated by depth-first search from the definition.
Also reported: the same for every other order, MD (value domination) and SD-C, and the k = 4 version (pool of three
goods, values 9, 8, 7), where everything holds.

    python3 k4/ksens/refute_oc_k5.py"""
import json, itertools, time
import _paths
import ocsat, brute

SETS = [[0, 5, 6, 7, 8], [1, 5, 6, 7, 8], [2, 5, 6, 7, 8], [0, 1, 2, 3], [0, 1, 2, 4]]
VALS = [[10, 9, 8, 7, 6]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]]
ORDER = (0, 1, 2, 3, 4)
SETS4 = [[0, 5, 6, 7], [1, 5, 6, 7], [2, 5, 6, 7], [0, 1, 2, 3], [0, 1, 2, 4]]
VALS4 = [[10, 9, 8, 7]] * 3 + [[6, 4, 2, 1], [6, 4, 2, 1]]


def show(name, sets, vals, m):
    t0 = time.time()
    a = ocsat.report(sets, vals, m); b, I = brute.report(sets, vals, m)
    assert a.keys() == b.keys()
    mism = sum(1 for Y in a for k in ('md', 'ext', 'ext1', 'oc', 'oc1') if a[Y][k] != b[Y][k])
    print('%s: n %d, m %d, k %d; %d complete EFX0 allocations (brute force); %d distinct starts over %d orders; '
          'mismatches between the two checks: %d' % (name, len(sets), m, max(map(len, sets)), len(I.efx0_list()), len(a),
                                                     len(list(itertools.permutations(range(len(sets))))), mism))
    for k in ('md', 'ext', 'ext1', 'oc', 'oc1'):
        bad = [Y for Y in a if not a[Y][k]]
        print('   starts failing %-4s: %d %s' % (k, len(bad), ['picks %s order %s' % (Y, a[Y]['order']) for Y in bad][:3]))
    print('   SD-C (some order extends): ocsat %s, brute %s' % (any(r['ext'] for r in a.values()), any(r['ext'] for r in b.values())))
    print('   time %.1f s' % (time.time() - t0))
    return a, b, I


if __name__ == '__main__':
    print('$ python3 k4/ksens/refute_oc_k5.py')
    print('PW5 =', json.dumps((SETS, VALS)))
    a, b, I = show('PW5', SETS, VALS, 9)
    Y = tuple(ocsat.sd(SETS, VALS, ORDER, 9))
    base = [frozenset([g]) for g in Y]
    ch = I.chains(base)
    print('order', ORDER, 'picks', Y, 'junk', sorted(set(range(9)) - set(Y)))
    print('   improving chains from these picks (brute force, distinct states):', len(ch))
    print('   states with a free completion:', sum(1 for s in ch if I.completes(s)), '; with a one-absorber completion:',
          sum(1 for s in ch if I.completes(s, 1)))
    print('   picks extend: free', I.completes(base), ', one absorber', I.completes(base, 1))
    print('   OC from this order: ocsat', a[Y]['oc'], 'brute', b[Y]['oc'], '; OC1: ocsat', a[Y]['oc1'], 'brute', b[Y]['oc1'])
    assert not a[Y]['oc'] and not b[Y]['oc'] and not a[Y]['oc1'] and not b[Y]['oc1']
    assert a[Y]['md'] and b[Y]['md']
    print('k = 4 version (pool of three goods):', json.dumps((SETS4, VALS4)))
    a4, b4, _ = show('PW4', SETS4, VALS4, 8)
    assert all(r['oc1'] for r in a4.values()) and all(r['oc1'] for r in b4.values())
    print('OK: OC and OC1 fail at k = 5 from order', ORDER, '; MD and SD-C hold; the k = 4 version satisfies all four')
