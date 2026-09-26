# Attempt: remove the 4-good agent together with one of its goods (B-form)

Workstream `proof/k4-induct` (`k4/induct.md` §2, §6). Failed as a "bounded repair for every X′" statement; kept for the
record.

**Idea.** Delete the agent w and a good d ∈ R_w (L10 for d = a_w). Every EFX₀ allocation X′ of I − w − d should become
EFX₀ for I after giving w the good d (and nothing else) plus at most ρ moved goods.

**Result.** Much better than deleting only d (the least ρ for the best (w, d) was ≤ 3 in every sample with n ≤ 5:
ρ = 3 on 1 of the 5,010 sampled n = 4 profiles, statistic best_B of `results/k4_induct_n4.log`; ρ = 2 on 1 of the 800
sampled n = 5 profiles and ρ ≤ 1 on the rest, `results/k4_induct_n5.log`), but not bounded by any ρ ≤ 2: ρ = 0 fails
at n = 2, ρ = 1 at n = 3, ρ = 2 at n = 4 (`results/k4_induct_n2.log` … `results/k4_induct_n5.log`). No failure of
ρ = 3 was found.

**Why.** With d = a_w, X′ + (w ↦ {a_w}) is EFX₀ iff no bundle of X′ threatens w; bundles of ≤ 2 goods never do, so for
a D2-shaped X′ the obstruction is exactly the large bundle holding a threatening set of w's lower goods, LB₄'s owner
constraint (OC₄) (`k4/lb4.md` §1). The induction hypothesis does not control the large bundle's contents.

**Smallest failing configurations:**
- ρ = 0 (n = 2, m = 4): {0, 1, 2, 3} (4, 8, 6, 1); {1, 2, 3} (4, 2, 3).
- ρ = 1 (n = 3, m = 5): {0, 1, 3, 4} (3, 6, 10, 8); {2, 3, 4} (4, 3, 2); {2, 3, 4} (4, 2, 3).
- ρ = 2 (n = 4, m = 7): {0, 2, 3, 5} (4, 7, 2, 8); {1, 4, 6} (3, 2, 4); {2, 3, 6} (3, 2, 4); {4, 5, 6} (2, 3, 4).

Reproduce: `python3 attempts/k4_induct_attempts.py B-r0 B-r1 B-r2`.
