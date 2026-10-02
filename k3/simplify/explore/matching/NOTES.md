# Exploration: bipartite-matching approaches to a simpler K3S

Branch `proof/k3-simplify`, exploration "matching" (about 75 minutes, one CPU). Everything here is **evidence**
except the short arguments in §4, which are written proofs of partial claims and have **not** been refereed.
Nothing here changes the ledger.

Setting: the core case of `proofs/k3_simple.md`. Every agent has three goods a ≻ b ≻ c, strictly balanced; values
4, 3, 2 (EFX₀ is ordinal, Lemma L5); goods nobody ranks are worthless. Every allocation built here is checked with
the raw EFX₀ definition (`k3s.efx0`).

## 1. The model (`common.py`)

A **base state** gives every agent one *option*: nothing, a, b, c, or the pair {b, c}, with disjoint goods. Goods
nobody holds are *junk*. Needs as in the paper (nothing → a, b, c; b → a; c → a, b; a and {b, c} → nothing); NA is
the set of needed goods. A base state is **valid** if every good of NA is held by an agent holding a single good.
*Free* agents: those holding nothing, or one good that nobody needs. *Slots*: 2 per agent holding nothing, 1 per free
agent holding a good.

**Completion** with absorber o (o free, or a pair holder): if the junk fits the slots, fill them (no bundle has three
goods). Otherwise every agent x that holds only a_x, with b_x and c_x both junk or in o's base, is *exposed for o*;
a minimum hitting set of these pairs (junk goods only) goes into the other agents' slots, the rest of the junk fills
the remaining slots, and o takes what is left. This is K3ALG's slot filling plus K3S's HitSet; the bipartite graph
"protecting goods → free agents" is complete, so Hall's condition (idea 4) is just |HitSet| ≤ other slots.

Utilities used for objectives: nothing 0 < c 1 < b 2 < a 3 < {b, c} 4 (the strict-balance order: v(b) + v(c) > v(a)).

## 2. Singleton matchings as picks (idea 1): FAIL at n = 3, m = 5

Picks = a matching (each agent at most one good), then K3S's upgrade loop, then completion with *any* absorber
(`exp_objectives.py`; log `logs/objectives_n3.log`).

| picks | n = 3, m = 5 (3,600) | n = 3, m = 6 (14,400) | n = 3, m = 7 (44,100) |
|---|---|---|---|
| rank-maximal (every optimum) | 54 fail for every optimum | 144 | 300 |
| max cardinality, then rank-maximal | 54 | 144 | 300 |
| max weight 4, 3, 2 | 54 where some optimum fails (some optimum works) | 144 | 300 |
| popular matching (when one exists) | 54 fail for every popular matching, 540 for some; 9 have none | 144 / 1,728; 16 none | 300 / 4,200; 25 none |

Nothing fails at n = 2 or n = 3, m = 4.

**Smallest failure** (all four rules): n = 3, m = 5, rankings (0, 1, 2), (0, 1, 2), (1, 2, 3); good 4 is worthless.
The rank-maximal (= popular) matchings are 0→0, 1→2, 2→1 and 0→2, 1→0, 2→1. In the first, junk {3, 4}, no upgrade
applies, and the only free agent is agent 1 (its c = 2; agents 0 and 2 hold goods agent 1 needs alone), so agent 1
must take {2, 3, 4}, which holds b = 2 and c = 3 of agent 2 (who holds only its top 1): agent 2 is unsafe. The
second is symmetric. The EFX₀ allocations need a pair: e.g. agent 2 takes {2, 3} and agent 1 takes 1.

So matchings of single goods are the wrong object: the answer needs a pair {b, c} that no matching objective on
single goods produces. This is the same lesson as the leader rules (`attempts/k3s-leader-rules.md`).

## 3. Matchings with pairs (idea 2): every optimum works, for every objective tried

Optimize over **valid base states** (pairs allowed). `exp_fast.py` (bitmask enumeration) tests "every optimal state
completes (some absorber)" for:
`sumU` (Σ utilities), `sumV` (Σ values, {b, c} = 5), `minNA` (fewest goods needed alone, = smallest overflow
`minOv`, since overflow = m − 2n + |NA|), `leximin`, lexicographic combinations, and **`pareto`: every
Pareto-optimal valid state** (no valid state is weakly better for everyone and strictly for someone).

| set | profiles | failures (any objective, any optimum) | log |
|---|---|---|---|
| every ranking profile, n = 2, m = 3–6; n = 3, m = 4–7 | 62,886 | 0 | `logs/fast_small_n23.log` |
| every ranking profile, n = 4, m = 5 | 216,000 | 0 | `logs/fast_4_5.log` |
| every ranking profile, n = 4, m = 6 | 1,728,000 | 0 | `logs/fast_4_6.log` |
| cores n = 5, 200 random profiles per core (objectives `pareto`, `minNA`, `sumU`) | 61,400 | 0 | `logs/fast_cores5.log` |

The strongest statement tested is

> **Conjecture PO.** Every Pareto-optimal valid base state completes (absorber + slot filling).

It implies existence at once (valid states exist, e.g. serial dictatorship, so a valid state maximizing Σ utilities
exists, and it is Pareto-optimal). It follows from Conjecture ST below: every move of §4 is a Pareto improvement, so a
Pareto-optimal valid state is stuck.

## 4. Augment until stuck (idea 3): LS and the stuck lemma

**Moves** on a valid base state (`exp_local.py`); each keeps the state valid and makes every agent it touches
strictly better, so Σ utilities grows (at most 4n moves):
- `up`: an agent holding b, with c junk and b needed by nobody, takes c too (K3S step 2);
- `cycle`: agents holding one good each trade around a cycle, each getting a good it needs;
- `rot`: an agent x holding a_x takes {b_x, c_x}; a_x goes along a need chain j₁, j₂, … (each needs the previous
  agent's good; any length, possibly 0), the last agent's good is released; b_x and c_x must be junk or the released
  good, and the result must be valid. This is K3S's rotation without the choice of k and r.

A valid state is **stuck** if no move applies.

> **Conjecture ST (stuck lemma).** Every stuck valid base state completes (some absorber works).

> **Algorithm LS** (`ls.py`). (1) Serial dictatorship in index order. (2) Apply moves (`up`, then `cycle`, then
> `rot`; first found) until none applies. (3) Completion with absorber rule `mindef`: among the agents whose base
> contains no exposed pair, one minimizing |HitSet(E_o)| − (slots of the other free agents).

LS has no draft blocks, no leaders, no "r = last agent not upgraded", no "k = last exposed agent", and no need chain
that must end at r. Its correctness would follow from the potential Σ utilities and Conjecture ST alone. It is not
"rotation-free": it can rotate several times (counts below), and it rotates even when no rotation is needed.
A lazy variant (move only while completion fails) is equally covered by ST.

Results (logs in `logs/`):

| test | profiles / states | failures | notes |
|---|---|---|---|
| ST, every stuck valid state, every ranking profile n = 2, m = 3–6; n = 3, m = 4–7 | 106,846 stuck states | 0 | `logs/stuck_small.log` |
| ST, every stuck valid state, every ranking profile n = 4, m = 5 | 666,288 stuck states | 0 | all fit the slots (no absorber needed) |
| ST, every stuck valid state of 2,000 random profiles n ≤ 5 | 5,218 stuck states | 0 | `logs/stuck_random5.log`; 2,004 need an absorber |
| LS, every ranking profile n = 2, m = 3–6; n = 3, m = 4–7; n = 4, m = 5 | 279,084 | 0 | `logs/ls_small.log` (absorber rule `minexp`) |
| LS, cores n = 5, 200 random profiles per core | 61,400 | 0 with `mindef`; **2 with `minexp`** | `logs/ls_cores5.log`, `logs/ls_cores5_minexp.log` |
| LS, 20,000 random profiles 2 ≤ n ≤ 8, n ≤ m ≤ 2n + 3 | 20,000 | 0 | `logs/ls_random8.log`; up to 6 moves |

Not run (time box): LS on every profile with n = 4, m = 6 (last line of `run_all.sh`; Conjecture PO was checked there
instead), ST on every stuck state with n = 4, m = 6, and ST on random n = 6.

**Absorber rule.** `minexp` (fewest exposed agents, ties by index) fails on 2 of the 61,400 core profiles at n = 5,
e.g. rankings (6, 0, 1), (3, 7, 5), (5, 4, 8), (2, 1, 0), (2, 3, 4), m = 9: LS ends with agent 0 holding {0, 1}, agents
1, 2, 3 their tops, agent 4 its c = 4; junk {6, 7, 8}; all three candidates have one exposed agent, the tie goes to
pair holder 0, and its bundle {0, 1, …} holds b = 1 and c = 0 of agent 3 (who holds only its top): agent 3 is unsafe.
Absorber 2 or 4 works. `mindef` (exclude an absorber whose base contains an exposed pair; then smallest
|HitSet| − other slots) fixes both; it is "an absorber that works" whenever one exists.

**Trading cycles** were used 3 times from the serial-dictatorship start (cores n = 5), never at n ≤ 4 or in the random
n ≤ 8 sample.

**Without `cycle` the stuck lemma is false**: n = 2, m = 5, rankings (0, 1, 2), (1, 0, 2), state "each agent holds
its b" (agent 0 holds 1, agent 1 holds 0). It is valid, nobody is free, the junk {2, 3, 4} must go to someone, and
every bundle that receives it breaks the other agent's need. The swap is the missing move. From the serial
dictatorship start, LS met a trading cycle only 3 times (cores n = 5).

### Partial proof of Conjecture ST (written here, not refereed)

Let Y be a stuck valid state.

**(S1) No agent x holds a_x with b_x and c_x both junk.** Suppose x does. If nobody needs a_x, `rot` with the empty
chain applies: a_x becomes junk, and it is needed by nobody (needs of other agents are unchanged; b_x, c_x were junk
so not in NA). Otherwise let j₁ need a_x. Walk: while the current agent j_t holds a good g_t needed by someone, let
j_{t+1} be such an agent. Every j_t (t ≥ 1) needs something, so it holds b, c or nothing; x needs nothing, so x
never recurs. If the walk revisits an agent,
the agents between form a trading cycle (`cycle` applies: everyone in it gets a good it needs, all goods stay held as
singles, needs only shrink). Otherwise it stops at an agent holding nothing, or one whose good nobody needs (a free
agent); then `rot` with this chain applies: needs only shrink (each agent on the chain gets a better good, x needs
nothing), so NA′ ⊆ NA, and the released good (if any) is not in NA. Contradiction. ∎

**(S2) If some agent e holds nothing, e is a valid absorber.** e is free; an agent exposed for e would have b_x, c_x
both junk (e's base is empty), excluded by (S1). ∎

**(S3) If nobody holds nothing and there is at most one free agent, some absorber works.**
- No free agent: every single holder's good is needed, and needers hold b or c. Walking backwards along "is needed
  by" inside the agents holding b or c gives a trading cycle, unless no agent holds b or c; then no agent holds a top
  either (a top is needed only by an agent holding b, c or nothing), so everyone holds a pair, and any pair holder
  absorbs: everyone is in case P.
- One free agent o: an agent x exposed for o holds a_x, one of b_x, c_x is o's good and the other is junk (S1). x is
  not free, so the walk of (S1) from a_x can only stop at o (or close a cycle), and the chain ending at o is a `rot`
  move (o's released good goes to x). So nobody is exposed for o. ∎

**Open case:** nobody holds nothing, at least two free agents, overflow > 0. Then exposures come only from the
absorber's own good (S1): E_o = {x holding a_x : o's good ∈ {b_x, c_x}, the other junk}, and stuckness says that no
need chain from a_x reaches o. What is missing is a counting lemma "some free o has |HitSet(E_o)| ≤ |F| − 1". Data
(`exp_stuck_cases.py`, `logs/stuck_cases.log`): (S1) holds on every stuck state; the open case is common (41,478 of the
stuck states with overflow at n = 3, m = 7; 1,906 in 4,000 random profiles n ≤ 5), the best deficit is always ≤ 0, and
usually (37,910 and 1,759 of these) some free agent has nobody exposed, but not always. Smallest state with every
free agent exposed-for: n = 2, m = 5, rankings (0, 3, 4), (3, 2, 0), both agents holding their tops (each one's good
is the other's b or c; deficit 0: the other agent's slot takes the protecting good).

## 5. What does not simplify

- Rank-maximal, popular, max-weight matchings of single goods (§2): n = 3, m = 5.
- Stuck lemma without trading cycles (§4): n = 2, m = 5 (as a lemma on all stuck states; LS from SD needed a cycle
  3 times in 61,400 core profiles at n = 5, so cycles cannot simply be dropped from LS either without a new argument).
- Absorber "fewest exposed agents, ties by index" (§4): n = 5, m = 9 (an absorber whose base holds a whole exposed
  pair).
- Hall's condition (idea 4) carries no information beyond a count: any protecting good fits any free slot.

## 6. Verdict

No rotation-free *matching* rule was found: single-good matchings fail at n = 3, m = 5, and every rule that works
(§3) optimizes over states containing pairs {b, c}, which is what the rotation produces. What the matching view does
give is a possibly **simpler proof shape**: "a valid state that no upgrade, trading cycle or rotation improves can be
completed" (Conjecture ST), with S1–S3 proved and one counting case open. If ST is proved, K3S's Theorem B and the
block structure of the draft are no longer needed for correctness, and Conjecture PO (every Pareto-optimal valid
state completes) follows.

## Files

- `common.py`: base states, validity, slots, exposure, completion, upgrade loop.
- `exp_objectives.py`: singleton matchings (rank-maximal, popular, max weight) and generalized objectives, n ≤ 3.
- `exp_fast.py`: generalized objectives and Pareto-optimal states, bitmask enumeration.
- `exp_local.py`: moves, the stuck lemma on every stuck valid state.
- `exp_stuck_cases.py`: which case of the stuck lemma occurs.
- `ls.py`: algorithm LS.
- `run_all.sh`: the protocol runs; logs in `logs/`.
