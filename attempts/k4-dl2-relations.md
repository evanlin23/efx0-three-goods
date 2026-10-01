# Structured relations R for which DL_R fails

Workstream `proof/k4-dl2-k1` (`k4/dl2.md` §3). After DL₂ failed (`attempts/k4-dl2-three-agents.md`), the target became
DL_R for a structured neighbourhood relation R: every min-frozen P ∈ 𝒫 with def(P) > 0 has a min-frozen R-neighbour
P′ with def(P′) < def(P). DL_R implies TARGET₄ for every R (PR #68, K4.STRAT.DL2.LEAN). This file records the
relations tested that **fail**, each with its smallest failing configuration found; the surviving relation R_T and its
evidence are in `k4/dl2.md` §3.

Moves (P, P′ min-frozen; "needed set unchanged": NA(P′) = NA(P)):
- *re-base*: one agent's base changes;
- *trade*: two agents' bases change, both free in P and P′, needed set unchanged;
- *role swap with a needer*: a frozen agent x with base {g} unfreezes, a free agent z with g ∈ N_z(B_z) takes {g} and
  freezes, needed set unchanged; *helpers*: further changed agents, free in P and P′.

Tool: `k4/dl2_relations.py` enumerates, for each def > 0 state, **every** min-frozen P′ with a smaller deficit and
tests each relation on the move P → P′; the runs are `results/k4_dl2_relations/*.log`. Each failure below is replayed
by `attempts/k4_dl2_attempts.py` with two implementations: `k4/dl2_relations.py` (on `k4/suite/model.py`) and main's
`k4/c4x_check.py` (its own enumeration of 𝒫 and deficit `rodef`) with membership tests written separately in the
attempts script.

## The failures

| relation | moves allowed | smallest failure found | where it fails (`results/k4_dl2_relations/`) |
|---|---|---|---|
| R2 (= DL₂) | at most two agents change | `dl2-n3m7` (n = 3, m = 7) | n = 3: 311 states of 89 profiles |
| RB2 | re-base, plain role swap with a needer, trade | `dl2-n3m7` | n = 3: the same 311 states |
| RB, RS1 | re-base; role swap with a needer and no helper (RB) or helpers that each give up exactly one good (RS1); no trades | `induct-g-r1` (n = 2, m = 5, f = 0) | suite: 7 states of 3 profiles; n = 3: 1,427 (RB) and 1,212 (RS1) states |
| RSY, RSYa, RSYg | re-base; role swap with a needer and at most one helper (RSY, RSYg: the helper gives up a good) or any number (RSYa); **no trades** | `induct-g-r1` | suite: 5 states of 2 profiles (f = 0 only) |
| RS1+2, RSR+2 | re-base, trade, role swap with a needer and helpers that only give up goods (one good each, or any) | `dl2-n3m7-trade` (n = 3, m = 7) | n = 3: 152 states of 51 profiles |
| RC | re-base, trade, a chain of frozen goods ending at a free agent (LB⁺'s rotation shape, no needer condition) with releasing helpers | `dl2-n3m7-trade` | n = 3: 152 states of 51 profiles |
| RSYz+2, RSYgz+2 | re-base, trade, role swap with a needer and at most one helper that takes goods only from its own base and the needer's old base | `dl2-n3m8-junk` (n = 3, m = 8) | n = 3: 13 states of 7 profiles |
| RSY+2, RSYg+2, R_T2 (code `RT`) | re-base, trade (two free agents), role swap with a needer and at most one helper | `dl2-rot-n3m7` (n = 3, m = 7, f = 0; found by compute/k4-dl2, PR #70) | that profile; no state of our inputs (they run before the instance was known, and #53's catalogues have f ≥ 1 only) |

At each of these states DL_T (`k4/dl2.md` §3: rotations of any number of free agents in place of trades; code `RTr`)
holds, by both implementations.

**`dl2-rot-n3m7`** (from the parallel workstream compute/k4-dl2, PR #70, `attempts/k4-dl2-rotation.md` and
`k4/suite/instances/dl2-rot-n3m7.json` on its branch; core 44 of `results/k4_certs_3.json.gz`): agent 0 = 0:6, 2:4,
4:8, 6:5; agent 1 = 1:2, 3:7, 5:4, 6:10; agent 2 = 2:7, 3:4, 4:2, 5:8. f = 0, ω = 1. P₀ = ({0,6}, {3,5}, {2,4}),
J = {1}, deficit 1; every min-frozen P′ with a smaller deficit changes all three bases, and the improvements rotate goods
around a cycle (each agent's top lies in another agent's base: 4 ∈ B_2, 6 ∈ B_0, 5 ∈ B_1; e.g. P′ = ({0,4}, {3,6},
{2,5}) with deficit 0). No agent is frozen, so there is no role swap;
**rotations of three free agents are needed**. Replayed here with both implementations (`attempts/k4_dl2_attempts.py`,
check 2e).

**`induct-g-r1`** (suite, from #43; n = 2, m = 5; agent: good:value): agent 0 = 0:4, 2:10, 3:8, 4:3; agent 1 = 1:4, 2:8,
3:10, 4:3. No agent is frozen at the fewest frozen agents (f = 0, ω = 1). P₀ = ({0,3}, {1,2}) has deficit 1. Every
min-frozen P′ with a smaller deficit changes both bases, and in every one agent 0 holds good 2 and agent 1 good 3: the
two agents exchange their tops (Theorem Z's rotation of a 2-cycle, `k4/c4min.md` Lemma R). There is no frozen agent, so
no role swap exists: **trades are needed**.

**`dl2-n3m7`**: `attempts/k4-dl2-three-agents.md` (the DL₂ trap).

**`dl2-n3m7-trade`** (#53's n = 3 catalogue, core 0 of `results/k4_certs_3.json.gz`, profile 10,57,227): agent 0 =
0:2, 1:4, 2:3, 3:8 (big-top, frozen on 3); agent 1 = 2:3, 4:6, 5:7, 6:5; agent 2 = 3:8, 4:4, 5:2, 6:3 (needs 3).
f = 1, ω = 2. P₀ = ({3}, {2,4}, {5,6}), J = {0,1}, deficit 1. Every min-frozen P′ with a smaller deficit (16 of them)
has agent 2 holding {3}, agent 0 a base among {1}, {0,1}, {0,2}, {1,2}, and agent 1 a base among {5}, {4,5}, {4,6},
{5,6}: the helper gives up good 2 (agent 0's) **and takes a good of agent 2's old base** {5,6}. It cannot just release:
{4} alone needs 5 (7 > 6), which is not a needed good. So a role swap needs a helper that trades.

**`dl2-n3m8-junk`** (core 4 of `results/k4_certs_3.json.gz`, profile 14,112,152): agent 0 = 0:2, 2:4, 4:8, 5:3 (frozen on
4); agent 1 = 1:4, 4:8, 6:3, 7:2 (holds {1}, needs 4); agent 2 = 3:6, 5:3, 6:5, 7:7. f = 1, ω = 3.
P₀ = ({4}, {1}, {3,5}), J = {0,2,6,7}, deficit 1. Every improvement has agent 1 holding {4}, agent 0 one of {2}, {0,2},
{0,5}, {2,5}, and agent 2 one of {7}, {3,6}, {3,7}, {6,7}: the helper gives up good 5 (agent 0's) **and takes a junk
good** (6 or 7); agent 1's old base {1} is worthless to it. So the helper must be allowed junk.

## Reproduce

```
python3 attempts/k4_dl2_attempts.py          # every failure above, two implementations
python3 k4/dl2_relations.py suite             # all relations on the suite (results/k4_dl2_relations/suite.log)
sh k4/dl2_relations_runs.sh                   # all relations on #53's catalogues and hunts
```
