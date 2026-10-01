# DL₁₃ fails at n = 4 (and DL_T with it, at f = 3)

Workstream `compute/k4-dl13` (PR #74). Ledger rows K4.DL2.T13 (Conjecture DL₁₃, now REFUTED), K4.DL2.T13N (the
runs), K4.STRAT.SUITE (two new suite instances). Definitions: `k4/dl2.md` §3 (moves T1, T2, T3; relations R_13 and
R_T), `k4/c4x.md` §1 (𝒫, the removal-only deficit).

**Conjecture DL₁₃** (`k4/dl2.md` §3): for every strict profile of every connected k = 4 core whose fewest frozen
agents is f ≥ 1, with ω ≥ 1, every min-frozen P with def(P) > 0 has a min-frozen P′ with def(P′) < def(P) reached by
(T1) a re-base of one free agent keeping the needed set, or (T3) a role swap (a frozen x gives its good g to a free z
with g ∈ N_z(B_z), x takes a new base) with at most one helper that gives up a good of its base.

**It is false.** Two kinds of counterexamples, both on connected k = 4 cores with n = 4 (at n ≤ 3 DL₁₃ holds at every
f ≥ 1 state, exhaustively: `results/k4_dl13/n3.log`):

1. **`dl13-n4m6-fswap`** (smallest found: n = 4, m = 6, f = 3): the only improvements move frozen goods between frozen
   agents. This is also a counterexample to **DL_T** (K4.DL2.T, `k4/dl2.md` §3), whose relation R_T adds rotations of
   free agents to R_13: no improvement keeps the key or is a role swap with at most one helper.
2. **`dl13-n4m9-rot`** (n = 4, m = 9, f = 1; #53's `gap_n4_pure_s4000` catalogue): no min-frozen P′ at all lies within
   two base changes; the improvements are rotations of the three free agents (in R_T, so DL_T holds here) and role
   swaps with two helpers.

Each is confirmed by three implementations (`python3 attempts/k4_dl13_refuted.py`, output in
`results/k4_dl13/attempts_replay.log`: ALL CONFIRMED):
- A: `k4/dl2_relations.py` on `k4/suite/model.py` (the proof workstream's tool; relations `R13`, `RTr`);
- B: main's `k4/c4x_check.py` (its own enumeration of every base map with (V1), (V2), and its own deficit `rodef`) with
  the membership tests `rel_B` of `k4/dl2_relations_xcheck.py`, written separately from A;
- C: `k4/dl13.c` (this workstream; a copy of `k4/dl2.c`'s enumeration and deficit with the R_13 test added; cross-checked
  against A and B on 8,136 f ≥ 1 states with 0 mismatches, `results/k4_dl13/check_*.log`).

## 1. `dl13-n4m6-fswap`: frozen agents must exchange goods

Core 12 (m = 6, idx 3) of `results/k4_certs_4_n4_3.json.gz` (three 4-good agents), profile 8,10,65,2; found by
`k4/dl13_hunt.py` (`results/k4_dl13/hunt_n4_3_m6.log`, climb 328).

| agent | goods : values |
|---|---|
| 0 | 0:2, 2:3, 4:8, 5:4 |
| 1 | 1:2, 3:4, 4:3, 5:8 |
| 2 | 2:3, 3:8, 4:4, 5:2 |
| 3 | 3:3, 4:2, 5:4 |

Goods 0 and 1 are private (agents 0 and 1). Every agent is strictly balanced (top < sum of the others: 8 < 9, 8 < 9,
8 < 9, 4 < 5) with distinct subset sums; the hypergraph is a connected k = 4 core (model.py's `core_violations` is
empty). σ = 2n − m = 2.

**P = ({5}, {3}, {2}, {4})**, J = {0, 1}. Needs: N_0 = {4} (8 > 4), N_1 = {5} (8 > 4), N_2 = {3, 4} (8, 4 > 3),
N_3 = {3, 5} (3, 4 > 2); NA = {3, 4, 5}. So agents 0, 1, 3 are frozen (on 5, 3, 4) and agent 2 (base {2}, not needed)
is free; f = 3 (every min-frozen P of the profile has three frozen agents), ω = 3 − 2 = 1.

def(P) = 1: the only owner is agent 2, with W_2 = {2} ∪ J = {0, 1, 2}. The bundle {0, 1, 2} threatens agent 0
(θ_0 = v_0({0, 2}) = 2 + 3 = 5 > v_0({5}) = 4; good 1 is worth 0 to agent 0), while {0, 2} and {1, 2} are safe
(agent 0 sees at most 3, agent 1 at most 2, agent 3 values none of 0, 1, 2). No frozen agent is counted (every frozen
good is needed by an agent other than the owner: 5 by 1 and 3, 3 by 3, 4 by 0), so Val*(P) = 2 and, by Lemma H1,
def(P) = ω + 2 − 2 = 1.

**The repair.** Agents 0 and 3 exchange their frozen goods: P′ = ({4}, {3}, {2}, {5}). Now agent 0 holds its top
good 4 (8) and agent 3 its top good 5 (4); the needed set is still {3, 4, 5} (agent 2 needs 3 and 4, agent 1 needs 5),
the frozen agents are the same, and {0, 1, 2} no longer threatens agent 0 (5 ≤ 8), so agent 2 owns three goods and
def(P′) = 0. This move is neither (T1) (two agents change), (T2) (the changed agents are frozen), nor (T3) (nobody
unfreezes). The 18 min-frozen P of the profile and their deficits (B: 12 with a smaller deficit than P) give every
improvement (`attempts_replay.log` lists them):

| distance | improvements of P (all have def 0) |
|---|---|
| 2 | the exchange of the frozen goods of agents 0 and 3 |
| 3 | a 3-cycle of the three frozen goods; four chains: agent 0 unfreezes (takes 2 or {0, 2}), one frozen agent takes agent 0's good 5 and the free agent 2 takes that agent's good (a role swap along a need chain of length 2) |
| 4 | six chains through two frozen agents |

No improvement keeps the key (needed set, frozen agents and their goods) and none is a role swap with at most one
helper, so **R_T (DL_T) has no improving move at P** either (A and B). DL₂ (two base changes) holds here.

m = 6 is the least m at which n = 4 admits this shape (f = 3 with ω = f − (2n − m) ≥ 1 needs m ≥ 6). The hunts found
78 such states (38 profiles of 10 cores with m = 6, five with three 4-good agents and five pure,
`results/k4_dl13/fails_hunt_m6.log`) and 18 more at m = 7, 8 (`fails_hunt_m8.log`); at every one f = 3, the nearest improvement is an
exchange of two frozen goods, and no relation tested (R_T, R_13 plus trades, plus 3-rotations, plus two helpers, plus
any number of helpers) has an improving move.

## 2. `dl13-n4m9-rot`: three free agents must rotate

Core 123 (m = 9, idx 0) of `results/k4_certs_4_pure.json.gz` (pure), profile 7,196,164,44, a record of #53's
`gap_n4_pure_s4000` catalogue (`results/k4_dl13/cat_gap_n4_pure_s4000.log`; earlier DL₁₃ runs took every 10th record of
this catalogue). It is the n = 4 catalogue trap of `k4/dl2_data.md` §5 whose repairs are 3-cycles of free agents.

| agent | goods : values |
|---|---|
| 0 | 0:2, 1:3, 2:6, 7:10 (big-top) |
| 1 | 2:7, 4:4, 5:8, 8:2 |
| 2 | 3:6, 4:5, 5:3, 6:7 |
| 3 | 3:3, 6:2, 7:8, 8:4 |

**P = ({7}, {2, 8}, {4, 5}, {3, 6})**, J = {0, 1}; agent 0 is frozen on 7 (agent 3 needs 7), f = 1, ω = 2, def(P) = 1
(55 min-frozen P; the best owner is agent 1; exposures: agent 0 w.r.t. owner 1 (H7's class L), agents 1 and 2 w.r.t.
owners 2 and 3 (H3's e3)). **No other min-frozen P′ lies within distance 2 of P** (B), so no move of at most two agents
helps. The 54 min-frozen P′ with a smaller deficit are:
- 24 at distance 3, deficit 0: rotations of the free agents 1, 2, 3 (each takes a good of another's base; the frozen
  agent keeps 7), e.g. ({7}, {5}, {6}, {8}) — moves (T2) of R_T, so DL_T holds here;
- 30 at distance 4, deficits −2 to 0: role swaps (agent 0 unfreezes, agent 3 takes 7) with **two** helpers (agents 1, 2,
  each giving up a good), e.g. ({2}, {4, 5}, {6}, {7}) with deficit −2.

Within two type changes of this profile (`k4/dl13_nbhd.py`, `results/k4_dl13/nbhd123.log`, 371,235 profiles of the
same core) DL₁₃ fails at 3,971 of the 59,439 f ≥ 1 states (all f = 1; 264 of them Pareto-maximal, so Lemmas H3/H7's
setting is not enough). `k4/dl13_fails.py` re-derives all 3,971 with model.py (0 mismatches,
`results/k4_dl13/fails_classified.log`): at every one the improvements are 3-rotations of the free agents (nearest at
2,991) or trades (nearest at 980), plus role swaps with two helpers; R_T, R_13 plus rotations of three free agents, and
R_13 with two helpers each repair all 3,971; R_13 plus trades repairs 980.

## 3. What DL₁₃ would have to grow into

On every failure found (4,068 f ≥ 1 states in 3,985 profiles of n = 4 cores; none at n ≤ 3 and none in #53's n = 5
catalogues and hunts):
- **with three free agents** (f = 1 at n = 4): rotations of three free agents (T2), or role swaps with two helpers;
- **with one free agent** (f = 3 at n = 4): moves that change the frozen agents' goods without the T3 shape: an exchange
  of the goods of two frozen agents (both stay frozen; distance 2, the nearest repair at all 96 states), a 3-cycle of
  frozen goods, or a role swap along a need chain of length ≥ 2 (x unfreezes, a frozen w takes x's good, the free z
  takes w's good). None of these is in R_T, so **DL_T is refuted too** (by the same instance; its row K4.DL2.T belongs
  to proof/k4-dl2-k1 and is not changed here).

So a neighbourhood relation R for `EFX.C4min.target4_of_defLocal` must, at f ≥ 1, contain rotations of at least three
free agents (or swaps with two helpers) **and** exchanges of frozen goods among frozen agents (or need chains of length
two). At f = 3 these exchanges keep the frozen set and the needed set but permute the frozen goods, so they are "key
changes" of a kind neither DL_T nor DL₁₃ allows; a natural successor is R_T plus permutations of the frozen goods among
frozen agents that keep NA (and every changed agent's needs inside NA). Whether that suffices is untested here beyond
the failures listed (all are repaired by an exchange or by R_T).

## Smallest failing configuration and reproduction

Smallest found: `dl13-n4m6-fswap` (n = 4, m = 6, f = 3, ω = 1, 18 min-frozen P), in the suite
(`k4/suite/instances/dl13-n4m6-fswap.json`, with `dl13-n4m9-rot.json`).

```
python3 attempts/k4_dl13_refuted.py                                    # both instances (and core 58, m = 7), A, B, C
python3 k4/suite/run.py --pred=k4/dl13_pred.py:dl13_c                  # FAILS at the two suite instances (also :dl13_model, :dl13_x)
python3 k4/dl13_hunt.py certs results/k4_certs_4_n4_3.json.gz --mmax=6 --climbs=400 --init=2000 --steps=60 --nb=48 \
  --patience=15 --bt --seed=2 --jobs=1                                 # finds the m = 6 failures (results/k4_dl13/hunt_n4_3_m6.log)
python3 k4/dl13_fails.py results/k4_dl13/hunt_n4_3_m6.jsonl.gz results/k4_dl13/hunt_pure_m6.jsonl.gz   # their repairs
```
