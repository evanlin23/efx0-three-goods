# D1-H, D1-LONG and Finding D1 with canonical chains only are false

Workstream `proof/k4-d1` (`k4/d1.md` §5).

**Idea.** `k4/oc1_hall.md` §21 reduces Finding D1 (one dangerous agent k: some ED chain from k with a minimal
improving H₀ leaves an S\* completion owned by k) to *canonical* chains, in which the head x_t takes its new good
a = Y_{x_{t−1}} alone, and leaves two sub-lemmas: D1-C (CROWD) and D1-H (HEAD: a failing chain whose head is frozen
by a second wanter w is replaced by a canonical chain through w). Conjecture D1-LONG says some longest canonical
chain works.

**Result: false.** D1-C holds (Theorem D1-C, `k4/d1.md` §3), but D1-H and D1-LONG fail, and so does the reduction of
Finding D1 to canonical chains. The canonical form of OC₁-ED\* (b) (owner x₀ or x_t, any H₀, the head takes no junk)
fails as well. Finding D1 in its §15 form survives: the head must be allowed to add a junk good.

**Smallest known failing configuration** (D1H-X, found by `k4/d1/head_hunt.py h1 201 3000`; n = 3, m = 8):
- sets [[0,1,5,7],[3,4,6,7],[0,2,5,7]];
- values [[26,3,25,27],[19,17,25,30],[9,14,7,29]];
- order (0, 1, 2), picks (7, 6, 2), J = {0, 1, 3, 4, 5}; F = D = {0} = {k}; agents 1 and 2 both want good 7 and are
  unfrozen. The picks have no one-absorber completion (raw enumeration and SAT agree).
- The canonical chains are (0, 1) and (0, 2), both with HEAD. k's pool goods are {0, 1, 5}, every pair improving.
  - Chain (0, 1): the head 1 holds 7 (30) and is threatened by its pool goods {3, 4, 6}, every pair of which is worth
    more than 30. Two of them must be kept out, and agent 2 is the only holder.
  - Chain (0, 2): the head 2 holds 7 (29) and its pool goods {0, 2, 5} are worth 30 together, so one must be kept
    out. The only holder, agent 1, is itself exposed ({3, 4} is worth 36 > 25) and needs its own slot.
  - With every improving H₀ (minimal or not), neither k nor the head owns an S\* completion afterwards.
- **Repair:** the ED chain (0, 2) in which the head takes 7 *and junk 0* (29 + 9 = 38), k takes the minimal pair
  {1, 5}, and agent 1 takes 3: [[1, 5, 2, 4], [6, 3], [7, 0]]. The head's own junk good removes its threat.

A strictly valued variant with smaller values, [[26,3,25,27],[2,17,18,19],[4,5,2,10]] on the same sets, refutes the
owner-k forms (D1-H, D1-LONG) but not the owner-k-or-head form.

**Repro.** `python3 k4/d1/verify_cex.py` (log `results/k4_d1/verify_cex.log`): two implementations (this
workstream's `k4/d1/d1lib.py` and the Hall session's `ohlib` plus the SAT test `oc_absorb.extends_A`) agree.
