"""Independent replay of the refutation of P1 (k4/sdc.md §1; ledger K4.SDC.P1). Written from the definitions only; it
shares no code with p1_brute.py or the SAT climber sdclib.py.

P1: in every instance with at most four relevant goods per agent, every partial EFX0 allocation X that is
Pareto-maximal among partial EFX0 allocations (by the vector of values v_i(X_i)), and allocates the most goods among
the partial EFX0 allocations with the same value vector, is complete.

The instance is GM4-E of k4/de4/gm4_counterexample.py (n = 4, m = 7, a k = 4 core with a strict profile).
    python3 k4/sdc/refute_p1.py"""
import itertools, json, os

SETS = [[0, 2, 4, 6], [1, 3, 5, 6], [2, 3, 6], [4, 5, 6]]
VALS = [[3, 10, 6, 2], [3, 4, 8, 2], [4, 2, 3], [2, 4, 3]]
X = {0: [0, 4], 1: [1, 3], 2: [2], 3: [5]}            # good 6 is left unallocated
N, M = len(SETS), 7
val = [{g: x for g, x in zip(S, V)} for S, V in zip(SETS, VALS)]


def worth(i, bundle):
    return sum(val[i].get(g, 0) for g in bundle)


def is_efx0(bundles):
    """Raw EFX0 for a partial allocation: v_i(B_i) >= v_i(B_j minus h) for all i != j and every h in B_j."""
    for i in range(N):
        mine = worth(i, bundles[i])
        for j in range(N):
            if j != i:
                for h in bundles[j]:
                    if worth(i, [g for g in bundles[j] if g != h]) > mine:
                        return False
    return True


def main():
    print('$ python3 k4/sdc/refute_p1.py')
    B = [X[i] for i in range(N)]
    u = [worth(i, B[i]) for i in range(N)]
    print('instance', json.dumps({'sets': SETS, 'vals': VALS}))
    print('X =', B, 'unallocated: [6]; values', u, '; X is partial EFX0:', is_efx0(B))
    assert is_efx0(B)
    dominating, complete_efx0 = [], []
    for owner in itertools.product(range(N + 1), repeat=M):        # owner N = unallocated
        bundles = [[g for g in range(M) if owner[g] == i] for i in range(N)]
        if not is_efx0(bundles):
            continue
        w = [worth(i, bundles[i]) for i in range(N)]
        k = sum(1 for o in owner if o < N)
        if N not in owner:
            complete_efx0.append((bundles, w))
        if all(a >= b for a, b in zip(w, u)) and (w != u or k > 6):
            dominating.append((bundles, w, k))
    print('partial EFX0 allocations with values >= X and (some value larger, or more than 6 goods allocated):',
          len(dominating))
    print('complete EFX0 allocations:', len(complete_efx0))
    for bundles, w in complete_efx0:
        worse = [i for i in range(N) if w[i] < u[i]]
        print('  ', bundles, 'values', w, 'agents worse off than in X:', worse)
        assert worse
    assert not dominating and complete_efx0
    print('P1 is FALSE: X is Pareto-maximal among partial EFX0 allocations, no partial EFX0 allocation with the same')
    print('values allocates good 6, and every complete EFX0 allocation leaves some agent worse off than X.')


if __name__ == '__main__':
    main()
