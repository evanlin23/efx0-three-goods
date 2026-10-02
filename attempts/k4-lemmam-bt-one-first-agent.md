# One chosen first agent (Lemma M, rule F with one rotation)

**Idea.** Rule F (`k4/adaptive.md`, K4.AD.F) and rule RK (`k4/rulef.md` §4) choose only the first agent of the
insertion sequence, then insert in index order; Lemma M (K4.RF.M) says some first agent a is in class K0 or K1 (Lemma
K certifies the run of τ_a without rotation or after one), which would give rule F with one rotation, `RuleFConn` and
TARGET₄ (K4.RF.LEAN). On the cores H_t the right first agent lies in gadget 1 (Propositions H′, H″). The big-top
programme (`k4/rulef.md` §6) tried to find the first agent by the big-top agents.

**Where it breaks.** A core can need two independent choices. Glue two copies of H_t by one shared good: whichever
agent is inserted first, one copy is left to index order, and Proposition H's count (K4.C4.R) leaves that copy short
of 2t slot places (2t − 3 after one rotation inside it), while the copy that holds the first agent returns at most one
slot place and the shared good one more. For t ≥ 3 no first agent works with one rotation: Proposition HH of
`k4/lemmam_bt.md` §3 (written proof). This is not a counterexample to K4.D: two adaptive insertion steps (a gadget-1
agent in each copy) need no rotation.

**Smallest failing configuration** (smallest known; with two copies of H_2 some first agents are in K1; every
certified core with n ≤ 4 and at most three 4-good agents satisfies Lemma M): HH_3, n = 26, m = 65, every agent with
four goods, none big-top. Agents ℓ_A {0, 3, 4, 5} (8, 6, 5, 4), ℓ_B {33, 36, 4, 37} (8, 6, 5, 4) (good 4 = u is shared),
then copy A's gadget agents and copy B's, each as in H_3 (`k4/lemmam_bt_hh.py core HH3` prints the sets and values).
- Lemma K's classes (`k4/lemmam_bt.py`, `results/k4_lemmam_bt/classes_HH3.log`): for every first agent and every
  policy the least deficit is at least 4 at the Phase 1 + upgrade state and at least 1 after every single RotStep: no
  first agent in K0 or K1.
- LB₄ʳ(τ_a) with at most one rotation, for every a, every policy, every owner, Lean's `Output` with the owner's needs
  from its bundle: no output, by three implementations: PR #33's two encodings (`results/k4_lemmam_bt/exactA_HH3.log`,
  `exactB_HH3.log`) and the PR #83 referee's own model (`k4/lemmam_bt_indep.py`, `indep_exactR_HH3.log`, also with
  the owner's needs from its base). So rule F with one rotation fails, and `EFX.LB4R.TheoremRuleF`,
  `EFX.LB4R.RuleFConn` are false. On HH_2 outputs exist (`indep_exactR_HH2.log`).
- K4.D on HH_3: `results/k4_lemmam_bt/d2_HH3.log` (insertion sequence (x^A_{1,2}, x^B_{1,2}), an `Output` without
  rotation, raw EFX₀ check; HH_4 too, `indep_d2.log`).

Reproduce: `python3 attempts/k4_lemmam_bt_attempts.py` (part 2: the instance, Lemma K at the best first agent, and
one exact check), or `bash k4/lemmam_bt_runs.sh` (every log of this workstream, one worker, about an hour), or
`python3 k4/lemmam_bt_indep.py exact HH3 --model=R --conv=bundle,base` (the independent model, about 40 minutes).
