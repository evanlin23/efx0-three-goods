# "Every exposed agent's rotation repairs": false at n = 7

Workstream `proof/kgen-n3`; context in `kgen/n3.md` §15.7–§15.11.

**The approach.** At a one-terminal gap draft (k = 3, a perfect start, T = {t}, |E_t| ≥ 2), rotate *any* exposed k
along its earliest-wanter (Rule E) chain into t. The hope was that a one-absorber completion always follows:
- T1-E, with any owner;
- T-E (k3-oc1's form), with owner none, t or k and k's slot.

Either would have removed the choice of k from the proof.

**Why it seemed right.** Both held on every one-terminal gap draft with n ≤ 6: 122,680 drafts and 265,840 rotations,
from k3-oc1's complete gap lists, checked by two independent completion tests.

**Smallest failing configuration known** (n = 7, m = 12, a ledger core; found by k3-oc1's sampling).
- Rankings 0: 3≻9≻0, 1: 4≻6≻10, 2: 5≻11≻8, 3: 2≻0≻8, 4: 3≻2≻1, 5: 5≻1≻7, 6: 7≻4≻6. Order 0, …, 6 gives
  picks (3, 4, 5, 2, 1, 7, 6), J = {0, 8, 9, 10, 11}, T = {6} and E_t = {0, 1, 2, 3}.
- The rotation of k = 1 along its only need chain (1, 6) has no one-absorber completion. lb2, the owner none/t/k
  test and an exhaustive search over every completion (raw EFX₀, values 4, 3, 2) agree.
- k = 0, 2, 3 complete.

**Reproduce:** `K3OC1=<a checkout of claude/k4-k3-oc1>/k4/k3oc1 python3 kgen/te_cex7.py`
(`results/kgen_n3/te_cex7.log`).

**What survives:** the "some k" form (T1-k), on all n ≤ 6 data and on k3-oc1's n = 7 sample.
