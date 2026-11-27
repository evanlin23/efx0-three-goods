"""Independent replay (coordinator) of the claim that P1 (K4.SDC.P1) already fails at k = 3 (branch claude/kgen-charity,
kgen/charity/refute_pm.py, construction S'(2, 3)).  The instance is typed in here from that construction's output; the
EFX0 test and the dominance search are written from the raw definitions and share no code with it.
Instance: n = 4, m = 7, every agent values exactly 3 goods (no agent is R1-peelable: 10 < 6 + 6, 5 < 2 + 2 + ... ).
State X: agent 0 holds {5}, agent 1 {6}, agent 2 {0, 1}, agent 3 {2, 3}; good 4 unallocated.
Checks: X is a partial EFX0 allocation; no partial EFX0 allocation Z has v_i(Z_i) >= v_i(X_i) for all i with a strict
gain or more goods allocated (brute force over all 5^7 partial allocations); every complete EFX0 allocation leaves some
agent worse off than X."""
import itertools
vals = [{5: 10, 0: 6, 4: 6}, {6: 10, 2: 6, 4: 6}, {6: 5, 0: 2, 1: 2}, {5: 5, 2: 2, 3: 2}]
n, m = 4, 7
X = [2, 2, 3, 3, 4, 0, 1]          # good -> holder (4 = unallocated)
V = lambda i, S: sum(vals[i].get(g, 0) for g in S)
def efx0(asg):
    B = [[g for g in range(m) if asg[g] == i] for i in range(n)]
    return all(V(i, [g for g in B[j] if g != h]) <= V(i, B[i])
               for i in range(n) for j in range(n) if j != i for h in B[j])
assert efx0(X)
xv = [V(i, [g for g in range(m) if X[g] == i]) for i in range(n)]; xa = sum(a < n for a in X)
dom = comp = comp_weak = 0
for asg in itertools.product(range(n + 1), repeat=m):
    if not efx0(asg): continue
    v = [V(i, [g for g in range(m) if asg[g] == i]) for i in range(n)]; a = sum(x < n for x in asg)
    comp += a == m
    if all(v[i] >= xv[i] for i in range(n)):
        comp_weak += a == m
        if any(v[i] > xv[i] for i in range(n)) or a > xa: dom += 1
print('X values', xv, 'allocated', xa)
print('partial EFX0 allocations dominating X:', dom)
print('complete EFX0 allocations:', comp, '| of which weakly better for everyone:', comp_weak)
print('P1 at k = 3:', 'REFUTED' if dom == 0 and comp_weak == 0 and xa < m else 'not refuted')
