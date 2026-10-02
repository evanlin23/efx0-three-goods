# Lemma K with kept-out sets inside R_x (k4/rulef.md §2, Remark 4)

**Idea.** In Lemma K an agent x threatened by the owner's widest bundle W_o = B_o ∪ J can be served by a set D_x of
junk goods kept out of the owner's bundle. Since only goods x values seem to matter for x's envy, the first
implementation (`k4/rulef.c` without `-Y1`) searched kept-out sets inside J ∩ R_x only, and rule RK's classes K0 / K1
were computed with that restricted count.

**Where it breaks.** threatened(x, L, H) = max_{h ∈ L} v_x(L ∖ h) > v_x(H) discounts the least good of L only when every
good of L is in R_x; if L holds a good x does not value, removing that good is the best removal and x's comparison is
against all of v_x(L ∩ R_x). So to protect x it can be necessary to keep out *every* good of W_o ∖ R_x as well, which
the restricted search never tries. On the profile below the restricted count gives every first agent and both
policies deficit 1, also after any single `RotStep`, so the restricted rule RK finds no class (Lemma M fails for the
restricted Lemma K). With kept-out sets that also hold the goods outside R_x (`-Y1`, `XKEEP = True`), every first agent
is in K0 (owner 1 for first agents 0 and 3, owner 0 for 1 and 2) and the completion of Lemma K's proof is an `Output`
and EFX₀. Lemma K's statement always allowed any D_x ⊆ J ∖ K; only the implementation was restricted. The restricted
count is still sound (it is at least the full deficit), so the exhaustive logs of k4/rulef.md §5.1 stand; they leave no
profile open even restricted.

**Smallest failing configuration known** (n = 4, m = 8, four big-top agents; no smaller n fails, and neither does
n = 4 with at most three 4-good agents: the restricted search leaves no profile of those certified cores open,
`results/k4_rulef/rk_n*.log`, nor any of 4.4·10⁶ random pure n = 4 profiles, `results/k4_rulef/rk_pure4_sample.log`; this
profile comes from the suite, `k4/suite/instances/lb4-owner-needs-from-base-n4m8.json`):
agents {0, 2, 4, 6}, {0, 2, 5, 6}, {1, 3, 4, 7}, {1, 3, 5, 7}, each with values (2, 3, 8, 4). LB₄ʳ itself needs no
rotation on index order (PR #33's independent model `k4/c4_verify_H/lb4r.py`, exact owner search), so the profile is
hard only for the restricted count.

Reproduce: `python3 attempts/k4_rulef_attempts.py` (part 6; `results/k4_rulef/attempts.log`), or
`python3 k4/suite/run.py --pred=k4/rulef_suite.py:lemma_k0` (with `-Y1`, `results/k4_rulef/suite_rk.log`).
