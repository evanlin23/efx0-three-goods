# DL₁₃₄ (R_13 plus frozen-good permutations) fails at n = 4, m = 9: three free agents must rotate

Workstream `compute/k4-dl13` (PR #74). Ledger row K4.DL2.T134 (REFUTED). Background: DL₁₃ and DL_T are refuted
(`attempts/k4-dl13-frozen-swap.md`, `attempts/k4-dl13-refuted.md`). At every one of their f = 3 failures the nearest
repair permutes the frozen agents' goods, which suggested adding that move.

**The extension tested** (the coordinator's, after the refutation of DL₁₃). T4: a move P → P′ between min-frozen
pre-allocations in which every agent whose base changes is frozen in P and in P′ and NA(P′) = NA(P). The frozen agents
then permute their singleton bases, and every other base is unchanged. R_134 := (T1) ∪ (T3) ∪ (T4), with (T1), (T3) of
`k4/dl2.md` §3. **Conjecture DL₁₃₄**: at f ≥ 1 every min-frozen P with def(P) > 0 has a min-frozen P′ with
def(P′) < def(P) reached by a move of R_134.

**It is false**, at `dl13-n4m9-rot` (`k4/suite/instances/dl13-n4m9-rot.json`). This is core 123 (m = 9, idx 0) of
`results/k4_certs_4_pure.json.gz`, profile 7,196,164,44, a record of #53's `gap_n4_pure_s4000`:

| agent | goods : values |
|---|---|
| 0 | 0:2, 1:3, 2:6, 7:10 |
| 1 | 2:7, 4:4, 5:8, 8:2 |
| 2 | 3:6, 4:5, 5:3, 6:7 |
| 3 | 3:3, 6:2, 7:8, 8:4 |

At P = ({7}, {2, 8}, {4, 5}, {3, 6}) only agent 0 is frozen (on 7, needed by agent 3): f = 1, ω = 2, def(P) = 1.
- No other min-frozen P′ lies within distance 2 of P, so no T1 move, no plain T3 move and no T4 move exists at all: a T4
  move with one frozen agent would change no base.
- The 54 min-frozen P′ with a smaller deficit are 24 rotations of the three free agents 1, 2, 3 (distance 3, def 0) and
  30 role swaps with **two** helpers (distance 4). Neither is a T3 move with at most one helper or a T4 move.
- So no R_134 move lowers the deficit. R_T ∪ T4 ("RT4", which adds the (T2) rotations of `k4/dl2.md`) does.

**Implementations.** `python3 attempts/k4_dl13_refuted.py` checks this with two of them, both of which say R_134 has no
improving move and R_T ∪ T4 has one:
- A: `k4/dl2_relations.py` shapes, with T4 by `k4/dl13_fails.t4_moves` on model.py's pre-allocations;
- B: `k4/dl134_xcheck.py`, on main's `k4/c4x_check.py`, with no model.py.

`k4/dl13.c` (C) independently gives the distances and the absence of an R_13 move (log
`results/k4_dl13/attempts_replay.log`).

**How common.**
- Within two type changes of this profile, DL₁₃ fails at 3,971 states (`results/k4_dl13/nbhd123.log`), all with f = 1.
  R_134 repairs none of them, since none has a T4 move. Each is repaired by a rotation of free agents, so RT4 holds:
  see `results/k4_dl13/dl134_xcheck_own.log` (B) and `results/k4_dl13/fails_all.log` (A).
- The other failures of this kind found: one f = 1 hunt state at m = 8, repaired by trades, and four f = 2 states at
  n = 5 (m = 11), repaired by trades and 3-rotations.
- At every f = 3 failure of DL₁₃ (3,062 states of the n = 4 certificate runs and 116 of the hunts, n = 4, 5) an
  improving T4 move exists, and its least number of agents is 2 (an exchange of two frozen goods):
  `results/k4_dl13/dl134_xcheck_n4.log` (B; all 3,062) and `fails_all.log` (A).

**What a successor needs.** Both kinds of move: permutations of frozen goods (T4; 2-swaps suffice on the data) and
rotations of free agents (T2). The candidate is RT4 = T1 ∪ T2 ∪ T3 ∪ T4, which holds at every failure found so far;
compute/k4-rt4 tests it at scale.

## Smallest failing configuration and reproduction

`dl13-n4m9-rot` above: n = 4, m = 9, f = 1, ω = 2, 55 min-frozen P, 1 state with def > 0. At n ≤ 3, DL₁₃ (hence DL₁₃₄,
R_134 ⊇ R_13) holds at every f ≥ 1 state (`results/k4_dl13/n3.log`).

```
python3 attempts/k4_dl13_refuted.py                                 # A, B (R_134, RT4) and C (R_13) at the instances
python3 k4/dl134_xcheck.py results/k4_dl13/states_cat.jsonl.gz      # B on the catalogue state: R134=0, RT4=1
python3 k4/dl134_xcheck.py results/k4_dl13/states_nbhd123.jsonl.gz  # B on the 3,971 states near it
```
