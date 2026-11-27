# Charity independent of n from a global potential: Pareto maxima (kgen/charity.md §5)

**Idea (Conjecture PM(k)).** Since CKMS's local rules can stall with Θ(√n) goods out (attempt
`kgen-charity-local-rules.md`), use a global object instead: a *Pareto maximum*, a partial EFX₀ allocation that no
partial EFX₀ allocation Pareto-dominates and that allocates the most goods among those with its value vector (the
hypothesis of K4.SDC.P1). Pareto maxima exist, have strong charity and are robust CKMS stopping states (Lemma CH6),
and they kill the stalls S(σ, k), whose sources hold goods worth nothing to them (Lemma PM1). PM(k) would say that a
Pareto maximum leaves at most f(k) goods out, which implies CH(k). The curated k = 4 instances support f(4) = 1 (20
have a Pareto maximum leaving one good out, none two; `results/kgen_charity/pm_screen_*.log`).

**Where it breaks.** S′(σ, k) (`kgen/charity/stuck_family.py`, `build(own=True)`; rebuilt independently in
`kgen/charity/refute_pm.py`) is S(σ, k) with every agent valuing its own bundle: sources value x_j and x′_j at 2 each
and their children at 5, relays value their own good at 4 and their children at 5. The state leaving σ − 1 goods out
is a Pareto maximum for every σ ≥ 2 and every k ≥ 3 (Proposition CH-E: an agent that loses its own goods must take a
child's good; the displacement runs down a tree to a champion c(·, j − 1), which must take x_{j−1} and a pool good,
which displaces s_{j−1}; so it goes round all σ sources and needs σ distinct pool goods). n = O(σ²), so Pareto
maxima can leave Θ(√n) goods out, already at k = 3.

With σ = 2 this refutes **P1 at k = 3**: n = 4, m = 7, every agent values exactly three goods.

| agent | values | holds |
|---|---|---|
| c₀ | 5: 10, 0: 6, 4: 6 | {5} |
| c₁ | 6: 10, 2: 6, 4: 6 | {6} |
| s₀ | 6: 5, 0: 2, 1: 2 | {0, 1} |
| s₁ | 5: 5, 2: 2, 3: 2 | {2, 3} |

Good 4 is unallocated. Every one of the 58 complete EFX₀ allocations leaves some agent worse off than this state,
and no partial EFX₀ allocation dominates it (brute force over all 5⁷ partial allocations). So K4.SDC.P1's
consequence ("a procedure that keeps a partial EFX₀ allocation and never lowers a value can stop") holds at k = 3
too; it is not a k = 4 phenomenon. (LB⁺ is not such a procedure, so there is no conflict with TARGET.)

**Smallest failing configurations.** P1 at k = 3: S′(2, 3) above. PM(3) and PM(4) with f = 1: S′(3, 3) (n = 12,
m = 17) and S′(3, 4) (n = 9, m = 14), two goods unallocated.

**What survives.** The welfare and leximin maxima of S′(2, 3) are complete, so "the welfare maximum with the fewest
unallocated goods leaves at most f(k) out" is not refuted by this family (Question W in `kgen/charity.md`).

Reproduce: `python3 kgen/charity/refute_pm.py 3 4` and `python3 kgen/charity/refute_pm.py 4 4` (no SAT, exhaustive;
logs `results/kgen_charity/refute_pm_k*.log`); the SAT check to σ = 7: `results/kgen_charity/pm_family_sat.log`.
