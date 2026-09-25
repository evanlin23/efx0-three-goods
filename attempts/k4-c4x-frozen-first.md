# Fewest frozen agents first, with a simple tie-break (k = 4)

Workstream `proof/k4-c4x` (`k4/c4x.md` §2). Approach: over the valid pre-allocations 𝒫 (bases of at most two goods,
value-based needs), take one with the fewest frozen agents (equivalently the smallest ω = |F| − σ, the smallest large
bundle a pre-allocation can need), break ties by a natural potential, and show that every such maximum is completable.

**What survives.** The *existence* form holds on every strict profile tested: some pre-allocation with the fewest
frozen agents is completable, and even removal-only completable with the owner's needs from its bundle (exhaustive for
n ≤ 3, and n = 4 with one or two 4-good agents; `k4/c4x.md` §5, conjecture K4.C4X.MIN). With the Hall-type deficit as
tie-break, (−frozen, −deficit), every maximum is completable by construction of the deficit; that is the conjecture,
not a proof.

**What fails.** The "every maximum" form with any simple tie-break:
- −frozen alone: every-form fails at n = 2 (50,320 of 189,216 profiles; `results/k4_c4x_n3.log`). The maxima include
  pre-allocations whose two-good bases are not envy-free: at k = 4 a pair {top, private good} can be worth less than
  the complementary pair, so its free holder has no slot and is threatened by the owner's bundle.
- (−frozen, slots): every-form fails at n = 2 (1,560 profiles), and at n = 3 on 153,256 of 299,837,376 profiles
  (`results/k4_c4x_n3.log`); even the some-form fails at n = 4 (instance 3 below, found in the review of PR #36 by
  sampling n = 4 cores with two 4-good agents; how often is not measured here).
- (−frozen, Σℓ): every-form fails at n = 3, m = 6 (84,388 profiles over n = 3), and even the some-form fails at
  n = 3, m = 8 (128 profiles): no maximum is completable there.
- (−frozen, leximin), (−frozen, slots, leximin), (−frozen, −exposed), (−frozen, frozen agents' Σℓ), and every other
  lexicographic combination tested without the deficit (31 in all): every-form fails at n = 3
  (`results/k4_c4x_n3_potentials.log`, 20,000 random profiles per core).

Why: the frozen count does not see *which* agents are frozen. Two examples from `k4/c4x.md` §2's exploration: an agent
of type c + d < a < b + d frozen on a contested top is threatened by pairs, while agents of type a > b + c are
threatened only by a triple, so the choice of the frozen agent decides completability; and a free agent whose private
goods land in the owner's bundle can be threatened by its three goods at once.

## Smallest failing configurations (checked by both implementations)

1. −frozen, every-form, **n = 2, m = 5** (the smallest n; exhaustive). Agents 0: goods 0, 2, 3, 4 with values 1, 4, 6, 8;
   agent 1: goods 1, 2, 3, 4 with values 1, 4, 8, 6. The maximum B = {0, 4} | {1, 3}, J = {2} has no frozen agent
   (ω = 1), both agents hold non-envy-free pairs (9 < 10), and good 2 in either bundle threatens the other agent.
2. (−frozen, slots), every-form, **n = 2, m = 5**: same core, agent 1's values 2, 4, 5, 8.
3. (−frozen, slots), some-form (no maximum completable), **n = 4, m = 7** (not known to be the smallest m): agents 0:
   goods 0, 2, 3, 6 with values 2, 6, 3, 10; 1: goods 1, 5, 6 with values 2, 4, 3; 2: goods 3, 4, 5, 6 with values
   3, 10, 8, 6; 3: goods 4, 5, 6 with values 4, 3, 2. Of 16 valid pre-allocations 12 are completable, but the unique
   maximum B = {6} | {5} | {4} | ∅ (three frozen agents) is not.
4. (−frozen, Σℓ), every-form, **n = 3, m = 6** (smallest m at n = 3; exhaustive): agents 0: goods 0, 2, 4, 5 with values
   2, 3, 4, 8 (a > b + c); 1: goods 1, 3, 5 with values 2, 4, 3; 2: goods 3, 4, 5 with values 4, 2, 3.
5. (−frozen, Σℓ), some-form (no maximum completable), **n = 3, m = 8** (smallest m at n = 3; exhaustive): the pure
   core with agents' goods {0, 2, 6, 7}, {1, 4, 6, 7}, {3, 5, 6, 7}, each with values 3, 4, 2, 8 in that order (good 7
   is everyone's top).

Replay: `python3 attempts/k4_c4x_attempts.py` (both `k4/c4x.c` and the independent `k4/c4x_check.py` on each instance;
prints "confirmed" for each).
