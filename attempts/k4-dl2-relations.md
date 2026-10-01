# Relations R for which DL_R fails

Workstream `proof/k4-dl2-k1` (`k4/dl2.md` §3). After DL₂ failed (`attempts/k4-dl2-three-agents.md`), the target became
DL_R for a structured neighbourhood relation R: every min-frozen P ∈ 𝒫 with def(P) > 0 has a min-frozen R-neighbour
P′ with def(P′) < def(P). DL_R implies TARGET₄ for every R (PR #68, K4.STRAT.DL2.LEAN). This file records the
relations tested that **fail**, each with its smallest failing configuration found; the surviving relations R_T and
(at f ≥ 1) R_13, and their evidence, are in `k4/dl2.md` §3.

Moves (P, P′ min-frozen; "needed set unchanged": NA(P′) = NA(P)):
- *re-base*: one agent's base changes;
- *trade*: two agents' bases change, both free in P and P′, needed set unchanged;
- *rotation*: any number of agents' bases change, all free in P and P′, needed set unchanged (a trade is a rotation of
  two agents);
- *role swap with a needer*: a frozen agent x with base {g} unfreezes, a free agent z with g ∈ N_z(B_z) takes {g} and
  freezes, needed set unchanged; *helpers*: further changed agents, free in P and P′.

R_T (code `RTr`): (T1) re-bases keeping the needed set, (T2) rotations, (T3) role swaps with a needer and at most one
helper that gives up a good of its base. R_13 (code `R13`): (T1) and (T3) only. (T1) ∪ (T2) are exactly the moves to a
min-frozen P′ with the same key (needed set, frozen agents and their goods), so at f = 0 every min-frozen P′ is an
R_T-neighbour and DL_T there holds by Theorem Z (`k4/dl2.md` §3). **The relations below are not sub-relations of R_T**,
except R_T2 and R_13 (the others allow re-bases that change the needed set, or helpers that keep their whole base);
and **failures at f = 0 do not bear on DL_T or DL₁₃**, whose open content is f ≥ 1.

Tool: `k4/dl2_relations.py` enumerates, for each def > 0 state, **every** min-frozen P′ with a smaller deficit and
tests each relation on the move P → P′; the runs are `results/k4_dl2_relations/*.log`, which split every count by the
fewest frozen agents f. Each failure below is replayed by `attempts/k4_dl2_attempts.py` with two implementations:
`k4/dl2_relations.py` (on `k4/suite/model.py`) and main's `k4/c4x_check.py` (its own enumeration of 𝒫 and deficit
`rodef`) with membership tests written separately in the attempts script (`results/k4_dl2_relations/attempts.log`).
Inclusions cover the relations not replayed: RB and RS1 are sub-relations of RSYa (RB also of RSY), RSYg of RSY and
RSYg+2 of RSY+2, so they fail wherever those do.

Cores are named (m, idx) as in the certificate files (`results/k4_certs_3.json.gz` lists the n = 3 cores by m, and idx
counts within an m).

## The failures

Counts: states (f ≥ 1 states in brackets) over all runs of `results/k4_dl2_relations/table.md`; "dump" is the
exhaustive n = 3 dump of compute/k4-dl2 (every state at distance 3, `trapped_n3_compute.log`).

| relation | moves allowed | smallest failure found | where it fails |
|---|---|---|---|
| R2 (= DL₂) | at most two agents change | `dl2-n3m7` (n = 3, m = 7, f = 1) | 314 (311 with f ≥ 1); dump: all 87,056 (29,072) |
| RB2 | re-base, plain role swap with a needer, trade | `dl2-n3m7` | the states of R2 |
| RB, RS1 | re-base; role swap with a needer and no helper (RB) or helpers that each give up exactly one good (RS1); no trades | `induct-g-r1` (n = 2, m = 5, f = 0); at f = 1: `dl2-n3m6-take` (n = 3, m = 6) | RB: 14,285 (1,433 with f ≥ 1); RS1: 14,067 (1,215 with f ≥ 1) |
| RSY, RSYa, RSYg | re-base; role swap with a needer and at most one helper (RSY, RSYg: the helper gives up a good) or any number (RSYa); **no trades** | `induct-g-r1` | 12,852, all at f = 0 |
| R_13 (`R13`) | re-base keeping the needed set; role swap with a needer and at most one helper giving up a good; **no rotations** | `induct-g-r1` | 12,852, all at f = 0; dump: the 57,984 f = 0 states |
| RS1+2, RSR+2 | re-base, trade, role swap with a needer and helpers that only give up goods (one good each, or any) | `dl2-n3m7-trade` (n = 3, m = 7, f = 1) | 155 (152 with f ≥ 1) |
| RC | re-base, trade, a chain of frozen goods ending at a free agent (LB⁺'s rotation shape, no needer condition) with releasing helpers | `dl2-n3m7-trade` | 155 (152 with f ≥ 1) |
| RSYz+2, RSYgz+2 | re-base, trade, role swap with a needer and at most one helper that takes goods only from its own base and the needer's old base (RSYgz+2: and gives up a good) | `dl2-n3m8-junk` (n = 3, m = 8, f = 1) | 16 (13 with f ≥ 1) |
| RSY+2, RSYg+2, R_T2 (code `RT`) | re-base, trade (two free agents), role swap with a needer and at most one helper | `dl2-rot-n3m7` (n = 3, m = 7, f = 0; found by compute/k4-dl2, PR #70) | 3, all at f = 0 (two random n = 3 profiles, below); dump: all 57,984 f = 0 states |

At each of these failing states DL_T (R_T) holds, by both implementations, and at the f ≥ 1 ones so does DL₁₃ (R_13).
On the dump, R2 and RB2 fail at all 87,056 states, RSY+2, R_T2 and R_13 at the 57,984 with f = 0, and R_T at none.

**`dl2-rot-n3m7`** (from the parallel workstream compute/k4-dl2, PR #70, `attempts/k4-dl2-rotation.md` and
`k4/suite/instances/dl2-rot-n3m7.json` on its branch; core (m = 7, idx 11) of `results/k4_certs_3.json.gz`): agent 0 =
0:6, 2:4, 4:8, 6:5; agent 1 = 1:2, 3:7, 5:4, 6:10; agent 2 = 2:7, 3:4, 4:2, 5:8. f = 0, ω = 1.
P₀ = ({0,6}, {3,5}, {2,4}), J = {1}, deficit 1; every min-frozen P′ with a smaller deficit changes all three bases, and
the improvements rotate goods around a cycle (each agent's top lies in another agent's base: 4 ∈ B_2, 6 ∈ B_0,
5 ∈ B_1; e.g. P′ = ({0,4}, {3,6}, {2,5}) with deficit 0). No agent is frozen, so there is no role swap;
**rotations of three free agents are needed** (at f = 0, where Theorem Z holds). Replayed here with both
implementations (`attempts/k4_dl2_attempts.py`, check 2e). Two more of the same kind are in the random n = 3 sample
(`results/k4_dl2_relations/certs_3_r400.jsonl.gz`, also replayed in check 2e): core (m = 8, idx 4), profile
19,197,115 (agent 0 = 0:2, 2:5, 4:8, 5:4; agent 1 = 1:7, 4:4, 6:10, 7:2; agent 2 = 3:4, 5:8, 6:5, 7:2;
P₀ = ({2,5}, {1,4}, {3,6}), deficit 1), and core (m = 9, idx 0), profile 17,25,41 (agent 0 = 0:2, 2:4, 6:10, 7:7;
agent 1 = 1:2, 4:7, 6:4, 8:10; agent 2 = 3:3, 5:4, 7:8, 8:6; P₀ = ({2,7}, {4,6}, {3,8}) or ({2,7}, {4,6}, {5,8}),
deficit 1). In both f = 0 and every improvement moves all three agents, all free.

**`induct-g-r1`** (suite, from #43; n = 2, m = 5; agent: good:value): agent 0 = 0:4, 2:10, 3:8, 4:3; agent 1 = 1:4, 2:8,
3:10, 4:3. No agent is frozen at the fewest frozen agents (f = 0, ω = 1). P₀ = ({0,3}, {1,2}) has deficit 1. Every
min-frozen P′ with a smaller deficit changes both bases, and in every one agent 0 holds good 2 and agent 1 good 3: the
two agents exchange their tops (Theorem Z's rotation of a 2-cycle, `k4/c4min.md` Lemma R). There is no frozen agent, so
no role swap exists: **trades are needed** (at f = 0).

**`dl2-n3m6-take`** (#53's n = 3 catalogue, core (m = 6, idx 13) of `results/k4_certs_3.json.gz`, profile
4,17,236): agent 0 = 0:1, 2:8, 4:4, 5:6 (frozen on 2); agent 1 = 1:2, 3:4, 4:10, 5:7; agent 2 = 2:8, 3:4, 4:6, 5:3
(holds {4}, needs 2). f = 1, ω = 1. P₀ = ({2}, {3,5}, {4}), deficit 1. The improvements (deficit 0): agents 1 and 2
trade (agent 1 takes {4} or {1,4}, agent 2 takes {3,5}), or agent 2 takes {2} from agent 0, agent 0 takes {5} or
{0,5}, and agent 1 (the helper) takes {4}, {1,4} or {3,4}: it gives up 5 **and takes agent 2's old good 4**. So
neither a plain role swap (RB) nor helpers that only release one good each (RS1) suffice, at f = 1; R_13 and R_T
hold (the helper gives up a good). The smallest f ≥ 1 failure of RB and RS1 found (n = 3, m = 6; replayed in check
2f). Over all runs RB fails at 1,433 and RS1 at 1,215 states with f ≥ 1.

**`dl2-n3m7`**: `attempts/k4-dl2-three-agents.md` (the DL₂ trap; core (m = 7, idx 0), profile 10,23,219).

**`dl2-n3m7-trade`** (#53's n = 3 catalogue, core (m = 7, idx 0) of `results/k4_certs_3.json.gz`, profile 10,57,227):
agent 0 = 0:2, 1:4, 2:3, 3:8 (big-top, frozen on 3); agent 1 = 2:3, 4:6, 5:7, 6:5; agent 2 = 3:8, 4:4, 5:2, 6:3 (needs
3). f = 1, ω = 2. P₀ = ({3}, {2,4}, {5,6}), J = {0,1}, deficit 1. Every min-frozen P′ with a smaller deficit (16 of them)
has agent 2 holding {3}, agent 0 a base among {1}, {0,1}, {0,2}, {1,2}, and agent 1 a base among {5}, {4,5}, {4,6},
{5,6}: the helper gives up good 2 (agent 0's) **and takes a good of agent 2's old base** {5,6}. It cannot just release:
{4} alone needs 5 (7 > 6), which is not a needed good. So a role swap needs a helper that trades.

**`dl2-n3m8-junk`** (core (m = 8, idx 4) of `results/k4_certs_3.json.gz`, profile 14,112,152): agent 0 = 0:2, 2:4, 4:8,
5:3 (frozen on 4); agent 1 = 1:4, 4:8, 6:3, 7:2 (holds {1}, needs 4); agent 2 = 3:6, 5:3, 6:5, 7:7. f = 1, ω = 3.
P₀ = ({4}, {1}, {3,5}), J = {0,2,6,7}, deficit 1. Every improvement (16 of them) has agent 1 holding {4}, agent 0 one
of {2}, {0,2}, {0,5}, {2,5}, and agent 2 one of {7}, {3,6}, {3,7}, {6,7}: the helper gives up good 5 (agent 0's) **and
takes a junk good** (6 or 7); agent 1's old base {1} is worthless to it. So the helper must be allowed junk; this
refutes RSYz+2 (the helper need not give up a good) and its sub-relation RSYgz+2.

## Reproduce

```
python3 attempts/k4_dl2_attempts.py          # every failure above, two implementations (results/k4_dl2_relations/attempts.log)
python3 k4/dl2_relations.py suite             # all relations on the suite (results/k4_dl2_relations/suite.log)
sh k4/dl2_relations_runs.sh                   # all relations on #53's catalogues and hunts
sh k4/dl2_relations_runs2.sh                  # on whole certificate files (every n = 2 profile, random n = 3, 4)
python3 k4/dl2_relations_trapped.py k4/suite/.cache/compute_k4_dl2/trapped_n3.jsonl.gz --model=20   # the dump (k4/dl2.md §7)
```
