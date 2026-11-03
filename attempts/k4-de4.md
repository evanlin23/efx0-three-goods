# Conjecture DE4 is false (k = 4)

Workstream `proof/k4-de4` (`k4/de4.md`, ledger K4.DE4, K4.DE4.C11B). Approach: the DE4 state space and order of
`k4/de4.md` §1 (holdings ∅, single goods, upper sets, the lower pair; validity (V1) + (V2); the level sum, then
value-Pareto), with the claim that **every maximum is completable** (Conjecture DE4), equivalently that every valid
state without an EFX₀ completion has a better valid state (the improvement form, and its restriction to (H) states,
Conjecture 11″). The plan was to prove the improvement form by DE's ring argument (`k4/de4.md` §7); the Lean frame
derives TARGET₄ from it (`EFX.DE4.target4_of_conjDE4H₂`).

## The counterexample

Found by the exhaustive run over every strict profile of every n = 4 core with two 4-good agents
(`results/k4_de4/exhaustive_4_n4_2.log`, `k4/de4/de4.c`; 922,669,056 profiles): 8 profiles, all of core 131, have a
maximum without an EFX₀ completion. In every profile some maximum is completable.

Core 131 (n = 4, m = 7): R_0 = {0, 2, 4, 6}, R_1 = {1, 3, 5, 6}, R_2 = {2, 3, 6}, R_3 = {4, 5, 6}. Profile A
(de4.c profile 353961):

| agent | values | ranking |
|---|---|---|
| 0 | 0: 3, 2: 8, 4: 2, 6: 4 | 2 ≻ 6 ≻ 0 ≻ 4 |
| 1 | 1: 3, 3: 2, 5: 8, 6: 4 | 5 ≻ 6 ≻ 1 ≻ 3 |
| 2 | 2: 4, 3: 2, 6: 3 | 2 ≻ 6 ≻ 3 |
| 3 | 4: 2, 5: 4, 6: 3 | 5 ≻ 6 ≻ 4 |

The profile is strict (all subset sums of each R_i distinct) and every agent is strictly balanced, so it is an R1-core
profile as in `k4/de4.md` §1 (and `EFX.DE4.R1Core4`, `EFX.Strict`).

Y = ({0, 4}, {1, 3}, {2}, {5}), leftover J = {6}:
- agents 0 and 1 hold their lower pairs (3 + 2 = 5, between b = 4 and a = 8; level 3) and want their tops 2 and 5;
- agents 2 and 3 hold their tops alone (level 4), so they are frozen;
- the level sum 14 is the largest over the 13 valid states, and no valid state with level sum 14 is value-Pareto-better:
  Y is a maximum, and no valid state is better than Y;
- Y has no EFX₀ completion: good 6 to agent 0 gives {0, 4, 6}, and agent 3 sees {4, 6} (5 > 4) after removing 0;
  to agent 1 symmetrically agent 2 sees {3, 6}; to agent 2 or 3 the bundle {2, 6} or {5, 6} contains agent 0's or 1's
  top (8 > 5 after removing 6);
- Y satisfies (H): every agent holds a good, J alone threatens nobody, no free agent has a self-upgrade (agent 0's
  sets inside {0, 4, 6} worth more than 5 are {0, 6} and {4, 6}, which are not holdings, and {0, 4, 6}, an upper set
  that threatens agent 3; the same for agent 1).

So Conjecture DE4, its improvement form and Conjecture 11″ (also its form `EFX.DE4.ConjDE4H₂`, as agents 0 and 1
are free and hold two goods) are false. The other two maxima, ({2}, {1, 3}, {6}, {5}) and ({0, 4}, {5}, {2}, {6}),
are completable.

**Mechanism.** It is the mechanism of the GM₄ counterexample (K4.GM.CEX, `attempts/k4-gm4-level-sum.md`): the two
frozen blockers 2 and 3 both need the one leftover good 6 for their danger sets ({3, 6} into agent 1, {4, 6} into
agent 0), and good 6 is each hungry agent's b. Every move that lets a blocker take its danger set (the walk, the
relaxed cycle, move PR) leaves the hungry agent that gave a good holding its c, and it then wants good 6, which sits
in a two-good holding: (V1) fails. The dead good of `k4/de4.md` §7.7 is here also the b of both hungry agents.
DE4's holdings were chosen so that GM₄'s instance E is not a valid state (its {0, 4} is agent 0's b and c); this
instance has the same shape with lower pairs.

**What survives.**
- The *some* form: every profile of the class has a completable maximum (`some_fail 0` in the log). It suffices for
  TARGET₄ but cannot be proved by an improvement step in this order, since a non-completable state with no better
  state exists.
- Algorithm DE4-ALG (K4.DE4.ALG) finishes on both profiles (the draft ({2}, {5}, {6}, {4}) is finished by DE's
  single-owner rule).
- Every lemma of `k4/de4.md` §3 and §7 that is proved (Lemmas 2, 4, 4′, 7, 8, 12–15, Theorem 9, Corollary 10) and the
  Lean results of K4.DE4.LEAN: they are statements about valid states, not about maxima.

## Tie-breaks do not repair it

The failing maximum has two lower pairs and the completable ones one, so a tie-break after the level sum looked like
a repair. Scale-invariant tie-breaks were tested on every strict profile of every n = 4 core with two 4-good agents,
all at once (`k4/de4/de4m.c`, `k4/de4/run_tiebreaks.py`, `results/k4_de4/tiebreaks_4_n4_2.log`; the order is the
level sum, then the tie-break key, then value-Pareto):

| tie-break after the level sum | profiles with a non-completable maximum | profiles with no completable maximum |
|---|---|---|
| none (DE4) | 8 (core 131) | 0 |
| fewest frozen agents | 8 (core 131: all three maxima there have two frozen agents) | 0 |
| fewest lower pairs | 1,620 (cores 127, 161, 179, 260, 265) | 0 |
| fewest goods held (most leftover goods) | 1,620 (the same cores) | 0 |
| fewest holdings of two or more goods | 1,620 (the same cores) | 0 |
| fewest lower pairs, then fewest goods held | 1,620 (the same cores) | 0 |

The last three remove core 131's failure: a lower-pair holder whose b is left over can switch to b (same level,
fewer lower pairs; the move is always valid, since the holder then wants only its top, which is held alone). But
they create failures where DE4 had none. Profile C (core 127: R = {0,2,3,5}, {1,4,6}, {2,3,5,6}, {4,5,6}; values
{0:2, 2:8, 3:5, 5:4}, {1:2, 4:4, 6:3}, {2:4, 3:2, 5:3, 6:8}, {4:4, 5:2, 6:3}): every DE4 maximum is completable, but
the tie-breaks discard the maximum ({0,2}, {4}, {3,5}, {6}), which dominated ({3,5}, {4}, {2}, {6}). That state then
becomes a maximum, and it has no EFX₀ completion. So the shape of the failure moves; it does not go away. In every
profile of the class, and under every criterion, some maximum is completable.

## Smallest failing configuration

n = 4, m = 7 (core 131). The 8 failing profiles are A, B (A with goods 2 ↔ 4 and 3 ↔ 5 exchanged, and agents 2 ↔ 3
with them) and, for each, the three profiles obtained by exchanging the values of a lower-pair holder's two pair goods.
No exhaustive run found a smaller one: none for n ≤ 3 (every strict profile of every core) or for n = 4 with one 4-good
agent, and core 131 is the only failing core with two 4-good agents. Cores with n = 4 and three or four 4-good agents
were only sampled.

## Replay

`python3 k4/de4/refute_de4.py` (written from `k4/de4.md` §1 only, sharing no code with `de4lib.py`, `de4.c` or
`de4m.c`; prints "confirmed" for each claim on profiles A and B, the tie-break claims on A and C, and exits 0 iff all
are confirmed;
`results/k4_de4/refute_de4.log`). `k4/de4/de4lib.py` agrees (all_states, maxima, completion). Machine-checked in
Lean for profile A: `EFX.DE4.Refute.not_conjDE4` (`lean/EFX/DE4Refute.lean`; the instance satisfies `R1Core4` and
`Strict`, the state is valid, no valid state is better, and none of the four completions is EFX₀), hence also
`not_conjDE4Imp`, `not_conjDE4H` and `not_conjDE4H₂`.
