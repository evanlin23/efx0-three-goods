# First agent minimizing a counting deficit (k4/rulef.md §5.3)

**Idea.** Make rule F explicit by replacing its lookahead (run LB₄ʳ for every first agent) by a count: take the first
agent a whose state after Phase 1(τ_a) and upgrades has the least deficit of an owner count, ties by index. Counts
tried (`k4/rulef.c -A40`, rules 3–7, 9–14, 16, 17 of `rulef_rules`): A₄⁺ᴺ's deficit (K4.AD.AN), A₄⁺(o)'s after
envy-free upgrades (K4.C4.AO), the smaller of the two; the refined counts (common kept-out sets; with the owner's
needs from a kept set); Lemma K's deficit (k4/rulef.md §2) after need-shrinking upgrades or either policy; ω after
need-shrinking upgrades (#44's `-A4`); ties broken by the fewest frozen or exposed 4-good agents; and "a 4-good agent
first". If the least deficit is ≤ 0 the rule is certified (Lemma K); the hope was that the minimizer also needs at most
one rotation when the deficit is positive.

**Where it breaks.** When every first agent has deficit 1, the counts do not see which agent's run one rotation can
repair. On the profile below every count gives the three first agents the same deficit (1); the tie goes to agent 0
(to agent 2 with the tie-break by exposed 4-good agents), and LB₄ʳ(τ₀) and LB₄ʳ(τ₂) need two rotations, τ₁ one.
Rule RK (k4/rulef.md §4) chooses agent 1, the only agent of class K1 (Lemma K after one rotation: in τ₁'s run agent
2 gives its top to agent 0 along the need chain 2 → 0 and takes the junk good 3 as its base, a downgrade rotation).

**Smallest failing configuration** (n = 3, m = 6; every rule above; none fails at n = 2, where no profile needs a
rotation under any first agent, nor at n = 3 with m ≤ 5: `results/k4_rulef/rules_n2.log`, `rules_n3_m4.log`,
`rules_n3_m5.log`):
agents {0, 1, 4, 5}, {2, 3, 4, 5}, {2, 3, 4, 5} with values (1, 4, 6, 8), (2, 3, 4, 8), (2, 7, 8, 4) (the profile on
which #44's ω rules fail, `attempts/k4-adaptive-greedy-omega.md`). Confirmed in PR #33's independent model of LB₄ʳ
(`k4/c4_verify_H/lb4r.py`): least rotations 2 on the rule's sequence, τ = [0] for every rule but rule 12 and τ = [2]
for rule 12, under every policy and both owner-needs conventions; brute force finds
EFX₀ allocations with at most one large bundle (the rule fails, not K4.D).

Reproduce: `python3 attempts/k4_rulef_attempts.py` (part 1; `results/k4_rulef/attempts.log`).
