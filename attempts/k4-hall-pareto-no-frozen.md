# Every Pareto-maximum without frozen agents is completable (k = 4): false

Workstream `proof/k4-hall` (`k4/hall.md` §3). **Approach.** Suppose a strict profile of a k = 4 core has a valid
pre-allocation with no frozen agent. Show that every Pareto-maximal P ∈ 𝒫 with no frozen agent is removal-only
completable. Such P are exactly the Pareto-maxima of 𝒫 in the class with the fewest frozen agents. This is Theorem K3's
statement (`k4/c4x.md` §3) restricted to the case without frozen agents.

**What survives.** Theorem H0 (`k4/hall.md` §3) proves this when at least two agents hold one good (T ≥ 2). For T ≤ 1,
a non-completable Pareto-maximum forces the exposure relation to be a permutation of the agents. Rotating a cycle of
it is a Pareto-improvement unless two agents of the cycle need the same junk good (a *label collision*, Lemma H5).

**Why it fails.** The label collision occurs.

## Smallest failing configuration found

Pure core, n = 6, m = 15 (`k4/hall_instances/cyc6.inst`; built by hand from the collision pattern of `k4/hall.md`
§3.1, so it is not known to be smallest). The agents, with good:value pairs, all strict and strictly balanced:

| agent | goods and values | base in P | shape |
|---|---|---|---|
| y | 0:8 2:6 3:5 12:4 | {2, 3} | e2 w.r.t. w′ (wants 0, label 12) |
| z | 4:10 2:8 3:6 5:3 | {4, 5} | e3 w.r.t. y (wants {2, 3}) |
| w | 4:8 6:6 7:5 13:4 | {6, 7} | e2 w.r.t. z (wants 4, label 13) |
| y′ | 6:8 8:6 9:5 12:4 | {8, 9} | e2 w.r.t. w (wants 6, label 12) |
| z′ | 10:10 8:8 9:6 11:3 | {10, 11} | e3 w.r.t. y′ (wants {8, 9}) |
| w′ | 10:8 0:6 1:5 14:4 | {0, 1} | e2 w.r.t. z′ (wants 10, label 14) |

Private goods: 5 (z), 7 and 13 (w, 5 + 4 < 8 + 6), 11 (z′), 1 and 14 (w′, 5 + 4 < 8 + 6), so it is a core (`k4/check4.py`
`is_core`).

In P, J = {12, 13, 14} and every base is need-free, so nobody is frozen. There are no slots (T = 0) and ω = 3. Every
owner's bundle B_o ∪ J threatens the agent it exposes, and there is no slot to remove a good into, so P is not
completable, not even with protection by slot goods. P is Pareto-maximal among all 4,015 valid pre-allocations.

The rotation along the cycle y → z → w → y′ → z′ → w′ → y does not repair it:
- z and z′ hold {a, d}, and their successors w and w′ want their tops 4 and 10;
- so z and z′ must take both goods of y's and y′'s bases;
- then y and y′ both need their bottom good 12.

The profile itself satisfies C₄ᵐⁱⁿ. Among the Pareto-maxima without frozen agents, 55 of 56 are completable, and so are
all three Σℓ-maxima. The repair lowers w′.

## Replay

`python3 attempts/k4_hall_attempts.py` replays it with both implementations:
- `k4/hall.c` enumerates 𝒫 and computes the exact removal-only deficit: every_ok 0, some_ok 1, and this P has
  deficit 1;
- `k4/hall_check.py` is independent plain Python. It checks validity, Pareto-maximality among all valid
  pre-allocations, and every completion literally, with a raw EFX₀ re-check: completable False, removal-only completable
  False.

It prints "ALL CONFIRMED".

## What would close the gap

A potential finer than Pareto-maximality, under which the collision yields an improving move. The candidate is the
level sum Σℓ (conjecture K4.HALL.F0Σ, `k4/hall.md` §3.4). On cyc6 the repair raises Σℓ, and every Σℓ-maximum without
frozen agents was completable in every test.
