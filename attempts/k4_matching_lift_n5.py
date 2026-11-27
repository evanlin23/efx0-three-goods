"""LIFT-SHAPE+ fails at n = 5, k = 4 (attempts/k4-matching-lift-shape.md).  Self-contained: raw definitions only, and
it imports nothing from k4/.

The instance is compute/k4-oc1max-cert's first n = 5 two-move start, list 5_pure idx 164: n = 5, m = 8, k = 4, a
strict profile.  The script checks, by brute force:
  1. the picks are serial-dictatorship picks, every agent picks, and there is exactly one holder z;
  2. there is no completion at the picks: no assignment of the junk to agents is EFX0, which is stronger than "no
     one-absorber completion";
  3. no official first move completes: no chain from a dangerous agent, with any junk given to its agents, followed by
     any assignment of the remaining junk;
  4. LIFT-SHAPE+ fails, because no pair (P1, P2) has the shape at all, before (L1), (L2'), (L3), (Lb) are even
     tested.  The shape is: P1 starts at a dangerous agent and ends at z; |H0 of P1| = 2, inside J + B_z; only the head
     of P1 takes junk; H0 of P1 is improving for a second dangerous agent; z is a holder after P1.  P2 ends at z; only
     its head takes junk; P2's head is not P1's head; z's new bundle is one good that z values most.
     4b. the weaker LIFT-EX (ledger K4.MATCH.LIFT) fails too: for each of the 75 first chains with its condition (2),
     no official second chain ends at z with z's favourite good in z's new bundle;
  5. two vertex-disjoint chains from dangerous agents repair it: 2 takes {5, 6} and 3 takes 2's pick 3, then 1 takes
     {1, 7} and 0 takes 1's pick 2.  The last junk good 0 goes to agent 1, and the result is EFX0.  It also counts
     every repairing pair of chains from dangerous agents (disjoint or overlapping);
  6. the same repair read as the proof/k4-oc1max-multi recursion: deleting agent 2 and T = {5, 6} after the first chain
     leaves an SD outcome of the smaller instance.

    python3 attempts/k4_matching_lift_n5.py"""
import itertools, collections

SETS = [[0, 2, 3, 7], [1, 2, 6, 7], [3, 4, 5, 6], [3, 4, 5, 7], [4, 5, 6, 7]]
VALS = [[1, 8, 6, 4], [4, 8, 2, 7], [6, 7, 3, 5], [7, 10, 2, 6], [7, 5, 3, 6]]
PICKS = [7, 2, 3, 5, 4]
N, MG = len(SETS), 8
v = [dict(zip(s, x)) for s, x in zip(SETS, VALS)]


def V(i, S): return sum(v[i].get(g, 0) for g in S)


def efx0(X):
    return all(V(i, [h for h in X[j] if h != g]) <= V(i, X[i]) for i in range(N) for j in range(N) if j != i for g in X[j])


def sd(order):
    taken = set(); Y = [None] * N
    for i in order:
        av = [g for g in v[i] if g not in taken]
        if av: g = max(av, key=lambda h: (v[i][h], -h)); Y[i] = g; taken.add(g)
    return Y


def junk(B): used = set(g for b in B for g in b); return [g for g in range(MG) if g not in used]
def wants(i, g, B): return g not in B[i] and v[i].get(g, 0) > V(i, B[i])
def frozen(j, B): return len(B[j]) == 1 and any(i != j and wants(i, B[j][0], B) for i in range(N))
def holder(j, B): return len(B[j]) <= 1 and not frozen(j, B)
def dangerous(B): return [x for x in range(N) if frozen(x, B) and any(g in v[x] for g in junk(B))]


def completes(B):
    """Some assignment of the junk of B to agents (any agents, any number of goods each) is EFX0."""
    J = junk(B)
    for asg in itertools.product(range(N), repeat=len(J)):
        A = [list(b) for b in B]
        for g, a in zip(J, asg): A[a].append(g)
        if efx0(A): return A
    return None


def chains(B, heads):
    """Every official chain P = (x0, ..., xt): x0 in heads takes H0 (nonempty, inside J + B_xt) and gains; x_i (i >= 1)
    takes B_{x_{i-1}} plus a set S_i of the remaining junk and gains.  Yields (P, H0, S, new state)."""
    J = junk(B)
    for L in range(2, N + 1):
        for P in itertools.permutations(range(N), L):
            if P[0] not in heads or not all(B[P[i - 1]] for i in range(1, L)): continue
            pool = J + list(B[P[-1]])
            for r in range(1, len(pool) + 1):
                for H0 in itertools.combinations(pool, r):
                    if V(P[0], H0) <= V(P[0], B[P[0]]): continue
                    rest = [g for g in J if g not in H0]
                    for lab in itertools.product(range(L), repeat=len(rest)):   # 0: stays junk; i: goes to P[i]
                        nb = [list(b) for b in B]; nb[P[0]] = list(H0); S = {}
                        for i in range(1, L):
                            S[i] = [g for g, l in zip(rest, lab) if l == i]; nb[P[i]] = list(B[P[i - 1]]) + S[i]
                        if all(V(P[i], nb[P[i]]) > V(P[i], B[P[i]]) for i in range(1, L)):
                            yield P, list(H0), S, nb


if __name__ == '__main__':
    print('$ python3 attempts/k4_matching_lift_n5.py')
    base = [[g] for g in PICKS]
    orders = [o for o in itertools.permutations(range(N)) if sd(o) == PICKS]
    print('1. SD picks', PICKS, 'from', len(orders), 'orders, e.g.', orders[0], '; junk', junk(base))
    hold = [j for j in range(N) if holder(j, base)]; D = dangerous(base)
    print('   holders', hold, '; dangerous', D)
    assert orders and len(hold) == 1
    z = hold[0]
    print('2. some completion at the picks:', completes(base) is not None)
    first = list(chains(base, D))
    rep1 = [c for c in first if completes(c[3]) is not None]
    print('3. official first moves', len(first), '; first moves after which some completion exists', len(rep1))
    zfav = max(v[z].values())
    n1 = n2 = 0
    for P1, H01, S1, B1 in first:
        if P1[-1] != z or len(H01) != 2 or not set(H01) <= set(junk(base)) | set(base[z]): continue
        if any(S1[i] for i in S1): continue
        if not any(q != P1[0] and V(q, H01) > V(q, base[q]) for q in D): continue
        if not holder(z, B1): continue
        n1 += 1
        for P2, H02, S2, B2 in chains(B1, range(N)):
            if P2[-1] != z or any(S2[i] for i in S2) or P2[0] == P1[0] or len(B2[z]) != 1: continue
            if v[z].get(B2[z][0], 0) == zfav: n2 += 1
    print('4. first chains with the LIFT shape', n1, '; LIFT-shaped pairs (P1, P2)', n2, '=> LIFT-SHAPE+ fails:', n2 == 0)
    # the weaker LIFT-EX (ledger K4.MATCH.LIFT): (2) P1 from a dangerous agent ends at z with H0 inside J + B_z, H0
    # improving for a second dangerous agent, any junk to P1's agents; (3) some official chain P2 ends at z and z's
    # new bundle contains its favourite good
    fav = [g for g in v[z] if v[z][g] == zfav]
    m1 = m2 = 0
    for P1, H01, S1, B1 in first:
        if P1[-1] != z or not set(H01) <= set(junk(base)) | set(base[z]): continue
        if not any(q != P1[0] and V(q, H01) > V(q, base[q]) for q in D): continue
        m1 += 1
        m2 += sum(1 for P2, H02, S2, B2 in chains(B1, range(N)) if P2[-1] == z and set(fav) & set(B2[z]))
    print('4b. first chains with LIFT-EX (2)', m1, '; of those, second chains with LIFT-EX (3)', m2,
          '=> LIFT-EX fails:', m1 > 0 and m2 == 0)
    B1 = [list(b) for b in base]; B1[2] = [5, 6]; B1[3] = [3]          # P1 = (2, 3): 2 takes {5 (z's pick), 6}
    B2 = [list(b) for b in B1]; B2[1] = [1, 7]; B2[0] = [2]            # P2 = (1, 0): 1 takes {1, 7 (0's pick)}
    norm = lambda B: [sorted(b) for b in B]
    assert any(norm(c[3]) == B1 for c in first) and any(norm(c[3]) == B2 for c in chains(B1, dangerous(B1)))
    A = [list(b) for b in B2]; A[1] = A[1] + [0]
    print('5. disjoint chains (2, 3) then (1, 0), both official; final allocation', A, 'EFX0:', efx0(A))
    pairs = collections.Counter()
    for Q1, _, _, C1 in first:
        for Q2, _, _, C2 in chains(C1, dangerous(C1)):
            if completes(C2) is not None: pairs['disjoint' if not set(Q1) & set(Q2) else 'overlapping'] += 1
    print('   repairing pairs of chains from dangerous agents (any completion):', dict(pairs))
    # 6. the multi session's recursion (Lemma LIFT, OC2-REC): delete agent 2 and T = {5, 6}; the reduced state is an SD
    # outcome of the smaller instance, and (1, 0) then the junk to agent 1 completes it, lifting to A
    keep = [0, 1, 3, 4]; T = {5, 6}
    def sd_red(order):
        taken = set(T); Y = {}
        for i in order:
            av = [g for g in v[i] if g not in taken]
            if av: g = max(av, key=lambda h: (v[i][h], -h)); Y[i] = g; taken.add(g)
        return Y
    red_orders = [o for o in itertools.permutations(keep) if sd_red(o) == {i: B1[i][0] for i in keep}]
    print('6. reduced instance (agents', keep, ', goods without', sorted(T), '): state', [B1[i] for i in keep],
          'is the SD outcome of', len(red_orders), 'orders, e.g.', red_orders[0] if red_orders else None,
          '; the lifted allocation is A above')
    assert completes(base) is None and not rep1 and n2 == 0 and m2 == 0 and efx0(A) and red_orders
    print('LIFT-SHAPE+ and LIFT-EX refuted at n = 5, k = 4')
