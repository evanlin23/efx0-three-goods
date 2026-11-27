# "Owner none or k suffices at one terminal" (T1-k, and Conjecture R-ω): false at n = 7

Workstream `proof/kgen-n3`; context in `kgen/n3.md` §15.9, §15.16–§15.19.

**The approach.** At a one-terminal gap draft (k = 3, a perfect start after LB's upgrades, T = {t}, |E_t| ≥ 2),
rotate some exposed k along its earliest-wanter (Rule E) chain into t. The hope was that the result then completes
with either no owner (Lemma 1 (a)) or owner k (Lemma 1 (b)):
- T1-k: some k works this way;
- Conjecture R-ω (§15.17): on Proposition A's residual, some rotation needs no owner at all.

Proposition A (proved) gives owner k on its class. So R-ω would have finished the one-terminal case with owners
{none, k} only.

**Why it seemed right.**
- T1-k held on all 122,680 one-terminal gap drafts with n ≤ 6, and on the samples at n = 7–8.
- R-ω held on all 8,944 residual drafts with n ≤ 6, and on 249 sampled at n = 7–8.

**Smallest failing configuration known** (n = 7, m = 11, a ledger core; found by k3-oc1,
`attempts/k4-k3oc1-tprime-k.md` on `claude/k4-k3-oc1`, and replayed here).
- **Rankings:** 0: 7≻0≻8, 1: 5≻7≻9, 2: 5≻10≻7, 3: 0≻3≻2, 4: 1≻2≻6, 5: 1≻6≻4, 6: 3≻4≻6.
- **The draft.** The order (2, 1, 0, 5, 6, 3, 4) gives picks (0, 7, 5, 2, 6, 1, 3), with no upgrades. Then J = {4, 8, 9, 10},
  T = {4} and ω = 3.
- **Twins.** E_t = {5, 6} share the pair {4, 6}, which contains Y_t = 6. This is class R1 of §15.17.
- **The rotations.** Only two rotations into t exist, (5, 4) and (6, 3, 4), and both are Rule E chains with t last.
  Both leave ω′ = 1.
- **Exhaustive search** over every completion of the rotated bases (raw EFX₀, values 4, 3, 2): the only absorbers of
  one-absorber completions are agents 3 and 4 = t, four completions each. No completion uses no owner or owner k.
- **Why owner k fails.** The twin's pair lies inside k's bundle, and Lemma 4 protects only owners other than k.
- **Owner t works.** Lemma 3 holds for owner t after either rotation.
  - After (5, 4), t gets its top 1; after (6, 3, 4) it gets 2.
  - No exposed top-holder's pair contains that good, so t has no frozen exposed agent.

**Reproduce:** `K3OC1=<a checkout of claude/k4-k3-oc1>/k4/k3oc1 python3 kgen/tk_cex7.py`
(`results/kgen_n3/tk_cex7.log`).

**What survives:**
- Conjecture T-t (§15.18): some Rule E rotation, with t last, passes Lemma 3 for owner t. It holds here, on all n ≤ 6
  gap drafts, and on 3,993 sampled at n = 7–8.
- k3-oc1's T-E∃ (owners none, t or k).
- k3-oc1's twin statement: every twin's rotation completes with owner none or t, on all 6,736 twin gap drafts with
  n ≤ 6 and on this instance.
