# DL₁₃ fails at n = 4 (and DL_T with it, at f = 3): the two shapes, and what a successor needs

Workstream `compute/k4-dl13` (PR #74). Ledger rows K4.DL2.T13 (Conjecture DL₁₃) and K4.DL2.T (Conjecture DL_T), now
REFUTED, K4.DL2.T13N (the runs), K4.STRAT.SUITE (two new suite instances); the smallest instance has its own file,
`attempts/k4-dl13-frozen-swap.md`. Definitions: `k4/dl2.md` §3 (moves T1, T2, T3; relations R_13 and
R_T), `k4/c4x.md` §1 (𝒫, the removal-only deficit).

**Conjecture DL₁₃** (`k4/dl2.md` §3): for every strict profile of every connected k = 4 core whose fewest frozen
agents is f ≥ 1, with ω ≥ 1, every min-frozen P with def(P) > 0 has a min-frozen P′ with def(P′) < def(P) reached by
(T1) a re-base of one free agent keeping the needed set, or (T3) a role swap (a frozen x gives its good g to a free z
with g ∈ N_z(B_z), x takes a new base) with at most one helper that gives up a good of its base.

**It is false.** Two kinds of counterexamples, both on connected k = 4 cores with n = 4 (at n ≤ 3 DL₁₃ holds at every
f ≥ 1 state, exhaustively: `results/k4_dl13/n3.log`):

1. **`dl13-n4m6-fswap`** (smallest found: n = 4, m = 6, one 4-good agent, f = 3; from the exhaustive run on the n = 4
   cores with one 4-good agent): the only improvements move frozen goods between frozen agents. This is also a counterexample to **DL_T** (K4.DL2.T, `k4/dl2.md` §3, REFUTED here at f ≥ 1), whose relation
   R_T adds rotations of free agents to R_13: no improvement keeps the key or is a role swap with at most one helper
   (issue #76; `attempts/k4-dl13-frozen-swap.md`).
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

The smallest counterexample, n = 4, m = 6, f = 3 (core 25 of `results/k4_certs_4_n4_1.json.gz`, from the exhaustive run on
the n = 4 cores with one 4-good agent), is written up in **`attempts/k4-dl13-frozen-swap.md`**: at P = ({4}, {1}, {3},
{5}) every improvement moves frozen goods between frozen agents (the nearest: two frozen agents exchange their goods),
so neither R_13 nor R_T has an improving move, and DL_T fails too. The same shape is every DL₁₃ failure of the
exhaustive n = 4 runs (3,060 states) and of the hunts at m = 6, 7, 8 (96 states), and 20 states at n = 5.

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

On every failure found (7,130 f ≥ 1 states of n = 4 cores: the 3,062 of the n = 4 certificate runs, the 3,971 near
`dl13-n4m9-rot` and the 97 of the hunts; and 24 states of 3 profiles of one n = 5 core (pure, m = 11) found by the hunt
from #53's `gap_n5_pure_s100` profiles, re-derived by model.py (`results/k4_dl13/fails_hunt_n5.log`; c4x_check does not
run at n = 5). None at n ≤ 3, none in #53's n = 5 catalogues and hunts themselves, none on H₂ or on random n = 5, 6
profiles):
- **with three free agents** (f = 1 at n = 4; 3,972 states; and f = 2 at n = 5, 4 states): rotations of three free
  agents (T2) or trades, or role swaps with two helpers (n = 4 only);
- **with one or two free agents** (f = 3 at n = 4, 3,158 states; f = 3 at n = 5, 20 states, where the two free agents
  could also trade): moves that change the frozen agents' goods without the T3 shape: an exchange of the goods of two
  frozen agents (both stay frozen; distance 2, the nearest repair at every one of them), a 3-cycle of frozen goods, or a role swap along a need chain of length ≥ 2 (x unfreezes, a frozen w takes x's
  good, the free z takes w's good). None of these is in R_T, so **DL_T is refuted too** (by the same instance; K4.DL2.T is
  set to REFUTED in #74, at f ≥ 1; it still holds at f = 0 by Theorem Z; issue #76).

So a neighbourhood relation R for `EFX.C4min.target4_of_defLocal` must, at f ≥ 1, contain rotations of at least three
free agents (or swaps with two helpers) **and** exchanges of frozen goods among frozen agents (or need chains of length
two). At f = 3 these exchanges keep the frozen set and the needed set but permute the frozen goods, so they are "key
changes" of a kind neither DL_T nor DL₁₃ allows; a natural successor is R_T plus permutations of the frozen goods among
frozen agents that keep NA (and every changed agent's needs inside NA). Whether that suffices is untested here beyond
the failures listed (all are repaired by an exchange or by R_T).

## Smallest failing configuration and reproduction

Smallest found: `dl13-n4m6-fswap` (n = 4, m = 6, one 4-good agent, f = 3, ω = 1, 18 min-frozen P), in the suite
(`k4/suite/instances/dl13-n4m6-fswap.json`, with `dl13-n4m9-rot.json`). No smaller n fails (n ≤ 3 exhaustive) and no
smaller m can carry this shape at n = 4.

```
python3 attempts/k4_dl13_refuted.py                                    # both instances (and cores 12, 58 of n4_3), A, B, C
python3 k4/dl13_run.py certs results/k4_certs_4_n4_1.json.gz --jobs=2   # every n = 4 profile with one 4-good agent: 20 failures
python3 k4/suite/run.py --pred=k4/dl13_pred.py:dl13_c                  # FAILS at the two suite instances (also :dl13_model, :dl13_x)
python3 k4/dl13_hunt.py certs results/k4_certs_4_n4_3.json.gz --mmax=6 --climbs=400 --init=2000 --steps=60 --nb=48 \
  --patience=15 --bt --seed=2 --jobs=1                                 # finds the m = 6 failures (results/k4_dl13/hunt_n4_3_m6.log)
python3 k4/dl13_fails.py results/k4_dl13/hunt_n4_3_m6.jsonl.gz results/k4_dl13/hunt_pure_m6.jsonl.gz   # their repairs
```
