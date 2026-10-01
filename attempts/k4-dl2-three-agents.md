# DL₂ fails at n = 3: a deficit trap that needs three agents

Workstream `proof/k4-dl2-k1` (`k4/dl2.md`). Statement tested: Conjecture DL₂ of `k4/strategy.md` §3 (ledger
K4.STRAT.DL2): for every strict profile of every connected k = 4 core with ω ≥ 1, every min-frozen P ∈ 𝒫 with
def(P) > 0 has a min-frozen P′ whose bases differ from P's for at most two agents and def(P′) < def(P).

**Result: false at n = 3, m = 7**, on a connected k = 4 core. Found by `k4/dl2_classify.py` on #53's n = 3 catalogue
(`results/k4_gap/gap_n3.json.gz` at 245040b, record of core 0 of `results/k4_certs_3.json.gz`, profile 10,23,219);
confirmed by two implementations (`attempts/k4_dl2_attempts.py`: `k4/suite/model.py` with
`k4/suite/deficit_local.kstar`, and main's independent checker `k4/c4x_check.py`, whose `analyse` enumerates every base
map and computes its own removal-only deficit `rodef`) and by hand below. The ledger row K4.STRAT.DL2E did not run the
n = 3 catalogue (its rows are n = 4, 5 and the suite).

## The instance (`dl2-n3m7`)

Goods 0–6; agent: good:value.

| agent | goods and values | type |
|---|---|---|
| 0 | 0:2, 1:4, 2:3, 3:8 | big-top (8 > 4 + 3), private goods 0, 1 (2 + 4 < 3 + 8) |
| 1 | 2:2, 4:6, 5:10, 6:7 | top 5 |
| 2 | 3:8, 4:3, 5:4, 6:2 | big-top (8 > 4 + 3) |

It is a connected k = 4 core (every agent strictly balanced, agent 0's two private goods worth less than its two
shared goods, every good valued) with strict values. σ = 2n − m = −1, the fewest frozen agents is f = 1 (the needed
set is always {3}: agents 0 and 2 both have top 3), ω = 2. There are 21 min-frozen pre-allocations, at two keys:
κ₀ (agent 0 frozen on 3, agent 2 needs it) and κ₂ (agent 2 frozen on 3, agent 0 needs it).

| key | min-frozen P (bases of agents 0, 1, 2) | def |
|---|---|---|
| κ₀ | {3}, {5}, {4,6} · {3}, {2,5}, {4,6} · {3}, {4,6}, {5} | 1, 1, 1 |
| κ₂ | agent 1 holds {2,5}: {1}, {2,5}, {3} · {0,1}, {2,5}, {3} | 1, 1 |
| κ₂ | agent 1 holds {5}, {4,5}, {4,6} or {5,6}; agent 0 holds {1}, {0,1}, {0,2} or {1,2} (16 P, agent 0 holds a good of {0,2} only if agent 1 does not hold 2) | −1 |

## Why P₀ needs three agents

P₀ = ({3}, {2,5}, {4,6}) has def(P₀) = 1. Every P with a smaller deficit is at κ₂, so agents 0 and 2 both change
(agent 0 unfreezes, agent 2 takes 3). A P′ at κ₂ that changes only agents 0 and 2 keeps agent 1's base {2,5}, and the
two such P′ have deficit 1. So the nearest smaller deficit is at distance 3: the frozen agent and its needer swap
roles **and** agent 1 releases good 2, agent 0's good. (Inside κ₀ every P has deficit 1.)

The deficits by hand (Lemma H1 of `k4/hall.md`: def(P) = ω + 2 − max(|X| + u_o(X)) over free owners o and safe X,
B_o ⊆ X ⊆ B_o ∪ J):
- **P₀**: J = {0, 1}, no slots. Owner 1: W = {0,1,2,5} gives agent 0 (holding 3, worth 8) the goods {0,1,2} = 9 > 8
  with 5 ∉ R_0, so one of 0, 1 must go (2 is the owner's base); X = {1,2,5} or {0,2,5} is safe (agent 2 sees only 5,
  4 < 5). |X| = 3, u = 0 (agent 2 needs 3), def = 4 − 3 = 1. Owner 2: W = {0,1,4,6}; agent 1 (holding {2,5}, 12) sees
  {4,6} = 13 > 12 as soon as X contains a good it does not value, and 4, 6 are the owner's base, so X = {4,6}: def ≥ 2.
  def(P₀) = 1.
- **({1}, {2,5}, {3})** (κ₂, agent 1 unchanged): J = {0,4,6}, one slot (agent 0). Owner 0: W = {0,1,4,6} gives agent
  1 the goods {4,6} = 13 > 12, so 4 or 6 goes; X = {0,1,6} or {0,1,4}, |X| = 3; agent 0's value from X is 6 < 8, so it
  still needs 3 and u = 0: def 1. Owner 1: W = {0,2,4,5,6}; agent 0 (holding 1, worth 4) sees {0,2} = 5 > 4, agent 2
  (holding 3) sees {4,5,6} = 9 > 8; removing 0 and one of 4, 6 leaves |X| = 3: def 1. ({0,1}, {2,5}, {3}) is the same
  with agent 0's slot used by 0.
- **({1}, {5}, {3})** (κ₂, agent 1 released 2): J = {0,2,4,6}, two slots. Owner 0: X = {0,1,2,6} is safe (agent 1
  sees {2,6} = 9 ≤ 10; agent 2 sees 6 alone), and agent 0's value from X is 9 > 8, so nobody needs 3 any more and agent
  2 unfreezes: u = 1, def = 4 − 4 − 1 = −1.

## What this says

- DL₂ as stated is false; the smallest failure found is n = 3, m = 7 (no n = 2 profile of the catalogue has a state
  with def > 0, and every n = 3 failure found has m ∈ {7, 8}). On #53's n = 3 catalogue (74,256 gap profiles: every
  100th n = 3 gap profile plus the hard ones), 89 profiles have k* = 3, with 311 states at distance 3
  (`results/k4_dl2_classify/`). Not exhaustive; the parallel `compute/k4-dl2` workstream runs every n ≤ 3 profile.
- Every distance-3 repair found (all minimal repairs of all 311 states) has the same shape: a **role swap** (the
  frozen agent unfreezes, a free agent takes its good and freezes) **plus a third, free agent that gives up at least
  one good of its base** (in 159 of the 311 states some minimal repair has the third agent only dropping goods, a pure
  release). `k4/dl2.md` records this; a corrected target has to allow it (for example: a role swap together with one
  more base change counts as one move).
- The two-agent role swap has the shape of Lemma F1's path move (`k4/c4min_f1.md`) and #51's Lemma PM; here x's goods
  have to be freed first. The mechanism (`k4/dl2.md` Lemma 7): agent 0 is big-top, and as the owner it unfreezes
  agent 2 only with all three of its lower goods 0, 1, 2 in its bundle (2 + 4 + 3 > 8); good 2 is in agent 1's base.
- The successor target is DL_T (`k4/dl2.md` §3: re-bases, trades, role swaps with at most one helper), which holds
  here and on every state tested; the narrower relations that fail are in `attempts/k4-dl2-relations.md`.

## Reproduce

```
python3 attempts/k4_dl2_attempts.py      # check 1: k* = 3 with model.py and with k4/c4x_check.py; P0 at distance 3
python3 k4/dl2_classify.py one '{"sets": [[0,1,2,3],[2,4,5,6],[3,4,5,6]], "vals": [[2,4,3,8],[2,6,10,7],[8,3,4,2]], "m": 7}'
```
