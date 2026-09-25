# LB₄ʳ with need-shrinking upgrades only

**Idea.** LB₄ʳ (`k4/lb4.md` §5) tries three upgrade policies in turn: need-shrinking upgrades, envy-free upgrades
only, none. With up to three nested rotations, perhaps LB₄'s own policy (need-shrinking) suffices, and a candidate
Theorem C₄ needs no fallback (`k4/lb4.c -i0 -u1 -r3 -w1 -c1`, and `-i1` for every insertion order).

**Where it breaks.** Already at n = 2: 1 of the 5 cores fails (300 profiles, index order). Index order, n ≤ 4 with at
most three 4-good agents: 149 cores fail; every insertion order: 262; random profiles on n = 5 (5,000 per core,
index order): 376 cores (`results/k4_lb4r_weak.log`). The other two policies alone do not fail on those tests:
envy-free upgrades only, and no upgrades at all, each with three rotations (same log and `results/k4_lb4r_simple.log`).

**Smallest failing configuration** (n = 2, m = 5; the core of `attempts/lb4-lbplus-shape.md`). Agents 0 = {0, 2, 3, 4}
and 1 = {1, 2, 3, 4}; values 0: (1, 4, 6, 8), 1: (2, 4, 5, 8). Index order: agent 0 picks 4, agent 1 picks 3. The
need-shrinking upgrade gives agent 1 the pair {2, 3} (worth 9 to it, above its top good 4), which leaves the goods 0
and 1 as junk, and no agent is frozen, so no rotation applies. Each of the four ways to place goods 0 and 1 breaks
EFX₀: goods 0 and 1 both to agent 0, and agent 1 values {0, 1, 4} without good 0 at 10 > 9; good 0 to agent 0 and good
1 to agent 1, and agent 0 values {1, 2, 3} without good 1 at 10 > 9; good 0 to agent 1 (with or without good 1), and
agent 0 values agent 1's bundle without a zero-valued good or without good 0 at 10 or more > 8. By brute force two
EFX₀ allocations with at most one large bundle exist, {0, 2, 3} | {1, 4} and {2, 3} | {0, 1, 4}: the construction
fails, not K4.D. Envy-free upgrades do not take {2, 3} (agent 1 values the rest {1, 4} at 10 > 9), and LB₄ʳ succeeds.

Reproduce: `python attempts/lb4_variants.py lb4r-need-shrinking-only` (`results/k4_lb4r_variants_repro.log`).
