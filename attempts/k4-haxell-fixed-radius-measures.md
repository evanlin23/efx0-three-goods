# One-step lemmas with a fixed radius of local moves: false for welfare, leximin and relevance (family CYC_n)

Workstream `proof/k4-haxell` (`k4/haxell.md` §6).

**Approach.** Prove CONN₂ (every partial EFX₀ allocation reaches a complete one) by local search: find a measure
μ = (|pool|, φ), compared lexicographically, and a radius r such that from every partial EFX₀ allocation with a
nonempty pool some composite of at most r local moves (move one good to an agent, swap two holders with the pool as a
holder, trade two bundles) leads to a partial EFX₀ allocation with smaller μ. The candidates for φ were welfare
Σᵢ vᵢ(Xᵢ), leximin, the number of envy pairs, the number of goods held by an agent that values them, and others
(`k4/haxell/gstar_measure.c`).

**Why it fails.** No fixed r works for welfare, leximin or the relevance count, already at k = 3. A long envy cycle
can only be resolved by rotating it whole, and no partial rotation raises any of these measures.
- *r = 2*: every candidate has stuck states on the screen set (welfare 3, the best tie-break 1; `measure_screen.log`).
- *r = 3*: welfare, leximin and the envy count have none on any dataset with n ≤ 5 (`measure3_*.log`).
- But CYC₅ (below) is stuck at r = 3 for welfare, leximin and every welfare tie-break, and CYCₙ needs r ≥ n − 1.

## Smallest failing configuration found

CYC₅ (n = 5, m = 6, k = 3): agent i values its own good gᵢ = i at 10, the next agent's good g_{i+1 mod 5} at 11, and
the pooled good p = 5 at 1.
- The state where every agent holds its own good, with p pooled, is partial EFX₀ (singletons).
- p cannot be placed: whoever receives it, its predecessor strongly envies the bundle {gⱼ, p} (11 > 10 after removing
  p).
- A partial rotation along a path of r agents changes welfare by r − 10 and leaves some agent at 0.
- No composite of at most three local moves (4,916 states) gives a partial EFX₀ allocation with an empty pool, or
  with larger welfare, or with a larger leximin vector.
- One rotation along the 5-cycle gives every agent its 11-good (welfare 55), after which p can be placed.
- CYC₄ is not stuck at r = 3 (its rotation takes three trades). CYC₆ is stuck at r = 3 as well (`families.log`).

**What survives.** Counting a rotation of the bundles along any cycle of agents as one move: with steps of at most two
such moves, welfare (Conjecture W) and leximin have no stuck state on any dataset (`k4/haxell.md` §6). The envy-pair
count is not stuck on CYC₄–CYC₆ even at r = 2, but it fails elsewhere at r = 2 with rotations.

**Reproduce:** `python3 attempts/k4_haxell_cyc.py` (raw EFX₀ definition, no shared code).
