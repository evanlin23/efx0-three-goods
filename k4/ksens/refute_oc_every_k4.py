"""The every-order forms of OC1 and OC at k = 4 fail (k4/ksens.md §5): the two strict core instances of k4/sdc.md §31
(found by the TTC session, claude/k4-ttc; §31 as read on branch compute/k4-oc1max-cert), replayed with this
workstream's checkers: ocsat.py (SAT) and brute.py (every one-chain state from the definition, official move rule and
with empty passes, each completion decided by backtracking on the raw EFX0 definition, completes_bt).
  B<  (n = 6, m = 10), order 0..5: no one-absorber completion after any one chain (OC1);
  MC2 (n = 5, m = 9),  order 0..4: no completion at all after any one chain (OC).
Result: both fail under the official move rule of k4/sdc.md §29 (no agent hands on an empty base), and both are
repaired by one chain once an agent with an empty base may pass it on (ocsat's default and brute.chains' default).
Neither start is a maximum-matching start (4 of 6 and 3 of 5 agents pick, nu = n).

    python3 k4/ksens/refute_oc_every_k4.py"""
import json, time
import _paths
import ocsat, brute
from maxmatch import nu

CASES = {'B<': ([[0, 2, 3, 1], [6, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]],
                [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 21], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]], 1),
         'MC2': ([[0, 3, 6, 8], [1, 4, 7, 6], [2, 5, 8, 7], [0, 1, 2], [0, 1, 2]],
                 [[10, 6, 5, 7]] * 3 + [[4, 3, 2], [2, 4, 3]], None)}

if __name__ == '__main__':
    print('$ python3 k4/ksens/refute_oc_every_k4.py'); t0 = time.time(); ok_all = True
    for name, (S, V, A) in CASES.items():
        n = len(S); m = 1 + max(max(s) for s in S); I = brute.Inst(S, V, m); O = ocsat.OC(S, V, m)
        Y = tuple(I.sd(tuple(range(n)))); b = ocsat.bases_of(Y, n); base = [frozenset([g]) if g is not None else frozenset() for g in Y]
        sat = O.holds(b, chain='any', A=A); ch = I.chains(base); ch0 = I.chains(base, empty_pass=False)
        bf = any(I.completes_bt(s, A) for s in ch); bf0 = any(I.completes_bt(s, A) for s in ch0)
        size = sum(1 for g in Y if g is not None)
        print('%s %s order 0..%d picks %s (%d picks, nu %d); completion %s; SAT one chain: %s; brute: %d one-chain states '
              '(%d official), any with a completion: %s (official %s)' % (name, json.dumps((S, V)), n - 1, Y, size,
              nu(S, V), 'one absorber' if A == 1 else 'free', sat, len(ch), len(ch0), bf, bf0), flush=True)
        ok_all &= sat and bf and not bf0 and size < nu(S, V); O.close()
    print('both: one chain fails under the official rule and succeeds with empty passes; neither start is maximum:',
          ok_all, '; %.0f s' % (time.time() - t0))
