# Conjecture BT (a failing Pareto-maximum has a frozen big-top agent): false at n = 4

Workstreams `proof/k4-hall` (`k4/hall.md` §5, row K4.HALL.BT) and `proof/k4-hall-bt` (`k4/hall_bt.md`).

**Approach.** At a Pareto-maximal P ∈ 𝒫 at the fewest frozen agents with ω ≥ 1 and no removal-only owner, some frozen
agent is a *big-top* agent: four goods, holding its top a, a > b + c. It holds for all 377,832 such maxima with n ≤ 3
(exhaustive), and trivially on the n = 4 cores with one 4-good agent, which have none. The hope was that every other
frozen exposure is local and repairable, so that only big-top agents need the owner step.

**Why it fails.** Two frozen agents that are not big-top agents can each block one of the two possible owners by a
local exposure when there are no slots. The repair is a *downgrade swap*, which is not a cycle of #41's exchange
digraph:
- a frozen agent gives its top to the agent that needs it;
- it takes as a single base a junk good it values (admissible: its only need is the top it gave away);
- the needer's old pair becomes junk.

The frozen agent loses value, so no Pareto argument sees the move.

## Smallest failing configuration found

Pure core, n = 4, m = 7 (core 59 of `results/k4_certs_4_pure.json.gz`; found in the sample of
`results/k4_hall_bt_samples.log`, 1 of the 303 maxima there that are not removal-only completable), `k4/hall_instances/bt4.inst`:

| agent | goods and values | type | base in P |
|---|---|---|---|
| 0 | 0:2 2:6 5:3 6:10 | big-top (10 > 6 + 3) | {2, 5}, free, needs 6 |
| 1 | 0:6 3:3 4:10 6:8 | not big-top | {0, 3}, free, needs 4 |
| 2 | 1:8 2:6 4:10 6:3 | not big-top | {4}, frozen |
| 3 | 1:6 3:4 5:1 6:8 | not big-top | {6}, frozen |

J = {1}, there are no slots, ω = 1, and the fewest frozen agents is 2. P is Pareto-maximal among all 24 valid
pre-allocations and not completable:
- owner 0: B_0 ∪ J = {2, 5, 1} gives agent 2 the goods 1 and 2, worth 14 > 10;
- owner 1: {0, 3, 1} gives agent 3 the goods 1 and 3, worth 10 > 8.

No frozen agent is a big-top agent. Among the Pareto-maxima inside the min-frozen class, 4 of 5 are completable. One of
them, with deficit −2, is the downgrade swap: agent 1 takes 4, agent 2 takes {1}, and {0, 3} becomes junk. `k4/hall.c -B` finds no exchange-digraph cycle that completes P, through any exposed frozen agent (`results/k4_hall_bt4_cycles.log`).

## Replay

`python3 attempts/k4_hall_attempts.py`:
- `k4/hall.c`: this P is a Pareto-maximum with deficit 1;
- `k4/hall_check.py` (independent): P is valid, has the fewest frozen agents, is Pareto-maximal and is not completable.
- `k4/hall.c -B`: no exchange-digraph cycle through any exposed frozen agent completes P.

## What survives

- With an exposed frozen big-top agent, a cycle through it completes in every case found (K4.HALL.BTCYC).
- The move catalogue for exposed frozen agents needs the downgrade swap as well. That is the kind of catalogue
  `proof/k4-c4min-f1` (PR #50) is building for f = 1. This instance has f = 2.
