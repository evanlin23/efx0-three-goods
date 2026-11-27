"""Conjecture RF (receiver first; k4/sdc.md §31 end, ledger K4.SDC.RF) fails at k = 5 with four agents (k4/ksens.md §8):
the instance RF5, found by rfcegar.py on the core-like hypergraph core5_n4_m7_688 (results/k4_ksens/rfcegar_k5_core5_n4.*).

    agent 0: goods 0, 1, 2, 5, 6 worth 3, 35, 33, 43, 39
    agent 1: goods 1, 2, 4, 5, 6 worth 20, 26, 16, 43, 32
    agent 2: goods 3, 4, 5, 6    worth 8, 2, 7, 4
    agent 3: goods 3, 4, 5, 6    worth 8, 2, 7, 4        (a twin of agent 2)

Checked here from the definitions, by two checkers: brute force (brute.py: every SD order, every chain under the
official rule, every complete allocation) and SAT (ocsat.py; its chains allow empty passes, which only adds moves).
- the start Y = (6, 5, 4, 3) is an SD start and a maximum matching, and OC1 fails there (no one-absorber completion at
  the picks or after one chain; also the free completion);
- the receivers of Y (agents whose pick no other agent values above its own pick): exactly agent 2;
- every order with agent 2 first, its picks, whether they are a maximum matching, and OC1 there.
RF fails when some receiver-first maximum-matching vector fails OC1.  Also: every profile-level check of strictness
(all subset sums of each agent distinct) and the type of failure (free completion too).

    python3 k4/ksens/refute_rf_k5.py"""
import itertools, time, json
import _paths
import brute, ocsat, rf_replay
from maxmatch import nu

SETS = [[0, 1, 2, 5, 6], [1, 2, 4, 5, 6], [3, 4, 5, 6], [3, 4, 5, 6]]
VALS = [[3, 35, 33, 43, 39], [20, 26, 16, 43, 32], [8, 2, 7, 4], [8, 2, 7, 4]]
Y = (6, 5, 4, 3)
# RF5b: the same hypergraph and start with agents 2 and 3 NOT twins (same ranking 3 > 5 > 6 > 4, different values),
# found by rfcegar.RFT (RF up to relabelling twins): the twin-swap failure does not need exact twins
VALS_B = [[3, 22, 23, 43, 38], [20, 26, 16, 43, 32], [10, 2, 7, 4], [8, 1, 6, 4]]


def main(SETS, VALS, Y, label):
    print('---', label, json.dumps([SETS, VALS])); t0 = time.time()
    n, m = len(SETS), 1 + max(max(s) for s in SETS)
    strict = all(len(set(sum(c) for r in range(len(v) + 1) for c in itertools.combinations(v, r))) == 1 << len(v) for v in VALS)
    I = brute.Inst(SETS, VALS, m); O = ocsat.OC(SETS, VALS, m); v = nu(SETS, VALS)
    val = lambda i, g: dict(zip(SETS[i], VALS[i])).get(g, 0)

    def oc1_both(W):
        b = ocsat.bases_of(W, n)
        bf = rf_replay.oc1(I, W, n)
        sat = 'picks' if O.holds(b, chain='none', A=1) else ('one chain' if O.holds(b, chain='any', A=1) else None)
        base = [frozenset([g]) if g is not None else frozenset() for g in W]
        free = I.completes(base) or any(I.completes([frozenset(x) for x in s]) for s in I.chains(base))
        freesat = O.holds(b, chain='none') or O.holds(b, chain='any')
        return bf, sat, free, freesat

    orders = [o for o in itertools.permutations(range(n)) if tuple(I.sd(o)) == Y]
    rec = [u for u in range(n) if Y[u] is not None and
           not any(j != u and val(j, Y[u]) > (val(j, Y[j]) if Y[j] is not None else 0) for j in range(n))]
    print('strict profile (all subset sums of each agent distinct):', strict, '; nu =', v)
    print('Y =', Y, 'from orders', orders, '; maximum matching:', sum(g is not None for g in Y) == v)
    print('OC1 at Y [brute A1, SAT A1, brute free, SAT free]:', oc1_both(Y))
    print('receivers of Y:', rec)
    fails = []
    for u in rec:
        vecs = {}
        for o in itertools.permutations(range(n)):
            if o[0] == u: vecs.setdefault(tuple(I.sd(o)), []).append(o)
        for Z, os_ in sorted(vecs.items()):
            mx = sum(g is not None for g in Z) == v; r = oc1_both(Z) if mx else None
            print('  u = %d: picks %s from %s; maximum matching %s; OC1 [brute A1, SAT A1, brute free, SAT free] %s' % (
                u, Z, os_, mx, r))
            if mx and r[0] is None and r[1] is None: fails.append((u, Z))
    O.close()
    ok = bool(strict and orders and rec and fails)
    twins = VALS[2] == VALS[3]
    print('RF fails: receiver-first maximum-matching vectors with no OC1 (both checkers):', fails, '; agents 2, 3 identical:', twins)
    print('OK: Conjecture RF fails at k = 5, n = 4' if ok else 'NOT CONFIRMED', '%.0f s' % (time.time() - t0))
    return ok


if __name__ == '__main__':
    print('$ python3 k4/ksens/refute_rf_k5.py', flush=True)
    a = main(SETS, VALS, Y, 'RF5 (agents 2, 3 twins)'); b = main(SETS, VALS_B, Y, 'RF5b (agents 2, 3 same ranking, not twins)')
    print('both confirmed' if a and b else 'NOT BOTH CONFIRMED')
