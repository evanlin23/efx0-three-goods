# DL₁₃ and DL_T fail at n = 4, m = 6: frozen agents must exchange their goods

Workstreams `compute/k4-dl13` (PR #74) and its n = 4 runs on `compute/k4-dl13-n4` (merged into it). Ledger rows
K4.DL2.T13 (Conjecture DL₁₃) and K4.DL2.T (Conjecture DL_T), both REFUTED by this instance; K4.DL2.T13N (the runs);
issue #76. Definitions: `k4/dl2.md` §3 (moves T1, T2, T3; relations R_13 = T1 ∪ T3 and R_T = T1 ∪ T2 ∪ T3),
`k4/c4x.md` §1 (𝒫, the removal-only deficit), Lemma H1 of `k4/hall.md`. The other shape of DL₁₃ failure (three free
agents that must rotate) and the summary of all failures are in `attempts/k4-dl13-refuted.md`.

**Statements refuted.** DL_T: for every strict profile of every connected k = 4 core with ω ≥ 1, every min-frozen P with
def(P) > 0 has a min-frozen P′ with def(P′) < def(P) reached by (T1) a re-base of one free agent, (T2) a rotation of free
agents, or (T3) a role swap with a needer and at most one helper, the needed set unchanged. DL₁₃: the same at f ≥ 1
without (T2). At f = 0 DL_T still holds (Theorem Z, K4.C4MIN.Z, `k4/dl2.md` §3); the instance below has f = 3.

## The instance `dl13-n4m6-fswap`

Core 25 (m = 6, idx 5) of `results/k4_certs_4_n4_1.json.gz` (one 4-good agent), profile 6,1,3,3. Found by the
exhaustive run over every strict profile of the n = 4 cores with one 4-good agent (`results/k4_dl13/n4_1.log`, made on
the branch compute/k4-dl13-n4 with this workstream's tools and merged here; `results/k4_dl13/n4_FAILURES.md`): DL₁₃
fails there at 20 states, all on this core.

| agent | goods : values |
|---|---|
| 0 | 0:2, 2:3, 4:4, 5:8 |
| 1 | 1:2, 3:4, 5:3 |
| 2 | 3:3, 4:4, 5:2 |
| 3 | 3:3, 4:4, 5:2 (a twin of agent 2) |

Goods 0 and 1 are private (agents 0 and 1). Every agent is strictly balanced (top < sum of the others: 8 < 9, 4 < 5,
4 < 5) with distinct subset sums; the hypergraph is a connected k = 4 core (model.py's `core_violations` is empty).
σ = 2n − m = 2.

**P = ({4}, {1}, {3}, {5})**, J = {0, 2}. Needs: N_0 = {5} (8 > 4), N_1 = {3, 5} (4, 3 > 2), N_2 = {4} (4 > 3),
N_3 = {3, 4} (3, 4 > 2); NA = {3, 4, 5}. So agents 0, 2, 3 are frozen (on 4, 3, 5) and agent 1 (base {1}, not needed)
is free; f = 3 (every min-frozen P of the profile has three frozen agents), ω = 3 − 2 = 1.

def(P) = 1: the only owner is agent 1, with W_1 = {1} ∪ J = {0, 1, 2}. The bundle {0, 1, 2} threatens agent 0
(θ_0 = v_0({0, 2}) = 2 + 3 = 5 > v_0({4}) = 4; good 1 is worth 0 to agent 0), while {0, 1} and {1, 2} are safe
(agent 0 sees at most 3; agents 2 and 3 value none of 0, 1, 2). No frozen agent is counted (every frozen good is needed
by an agent other than the owner: 4 by 2 and 3, 3 by 3, 5 by 0), so Val*(P) = 2 and, by Lemma H1,
def(P) = ω + 2 − 2 = 1.

**The repair.** Agents 0 and 3 exchange their frozen goods: P′ = ({5}, {1}, {3}, {4}). Now agent 0 holds its top
good 5 (8) and agent 3 its top good 4 (4); the needed set is still {3, 4, 5} (agent 1 needs 3 and 5, agent 2 needs 4),
the frozen agents are the same, and {0, 1, 2} no longer threatens agent 0 (5 ≤ 8), so agent 1 owns three goods and
def(P′) = 0. This move is neither (T1) (two agents change), (T2) (the changed agents are frozen), nor (T3) (nobody
unfreezes). The 18 min-frozen P of the profile and their deficits (B: 12 with a smaller deficit than P) give every
improvement (`attempts_replay.log` lists them):

| distance | improvements of P (all have def 0) |
|---|---|
| 2 | the exchange of the frozen goods of agents 0 and 3 |
| 3 | a 3-cycle of the three frozen goods; four chains: agent 0 unfreezes (takes 2 or {0, 2}), a frozen agent takes agent 0's good 4 and the free agent 1 takes that agent's good (a role swap along a need chain of length 2) |
| 4 | six chains through two frozen agents |

No improvement keeps the key (needed set, frozen agents and their goods) and none is a role swap with at most one
helper, so **R_T (DL_T) has no improving move at P** either (A and B). DL₂ (two base changes) holds here.

m = 6 is the least m at which n = 4 admits this shape (f = 3 with ω = f − (2n − m) ≥ 1 needs m ≥ 6). The same shape
(f = 3, def 1, nearest improvement an exchange of two frozen goods, distance 2, R_T failing too) is every DL₁₃ failure
of the exhaustive n = 4 runs with one and two 4-good agents (20 and 3,040 states, 9 cores with m = 6, 7,
`results/k4_dl13/n4_FAILURES.md`, re-checked there by A, B and C), of the sampled three-4-good-agent cores (2 states),
and of this workstream's hunts: 78 states in 38 profiles of 10 cores with m = 6 (five with three 4-good agents, five
pure; `results/k4_dl13/fails_hunt_m6.log`) and 18 at m = 7, 8 (`fails_hunt_m8.log`). At those 96 hunt states no relation
tested (R_T, R_13 plus trades, plus 3-rotations, plus two helpers, plus any number of helpers) has an improving move;
`attempts/k4_dl13_refuted.py` also replays core 12 (m = 6) and core 58 (m = 7) of `results/k4_certs_4_n4_3.json.gz`.

## Smallest failing configuration and reproduction

`dl13-n4m6-fswap` (`k4/suite/instances/dl13-n4m6-fswap.json`): n = 4, m = 6, one 4-good agent, f = 3, ω = 1, 18
min-frozen P, 6 with def > 0 (DL₁₃ and DL_T fail at 2 of them: P and its image under the twin swap). No smaller n fails
(n ≤ 3 exhaustive, `results/k4_dl13/n3.log`), and at n = 4 an f = 3 failure needs m ≥ 6.

```
python3 attempts/k4_dl13_refuted.py                       # this instance (first) with A, B, C; R_T fails too
python3 results/k4_dl13/n4_failures_xcheck.py results/k4_dl13/dump_n4_1.jsonl.gz   # all 20 failures of the class, A, B, C
python3 k4/dl13_run.py certs results/k4_certs_4_n4_1.json.gz --jobs=2               # every n = 4 profile, one 4-good agent
python3 k4/suite/run.py --pred=k4/dl13_pred.py:dl13_c     # FAILS here (also :dl13_model, :dl13_x)
```
