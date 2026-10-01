# The θ-b case and the non-S1 T3-stage states at f = 1: the other-needer swap

Workstream `proof/k4-thetab`. Closes (in part, see Status) `k4/dl13.md` §6 item 2. Builds on `k4/dl2.md` (Lemmas 1, 6,
7; refereed, K4.DL2.MOVES), `k4/dl13.md` (Lemmas 8, 11, Proposition T; refereed, PR #75), `k4/hall.md` §1 (Lemma H1,
K4.HALL.COVER) and `k4/c4x.md` §1 (𝒫, needs, frozen agents, slots, deficit). Nothing here changes K4.D or K4.T.

**Work in progress** (draft). Status of each statement is given where it is stated.

**Context.** The coordinator reports that DL_RT4 (and key-graph DL with single (T3)/(T4) edges) is refuted at n = 5,
f = 3 (cloud branches compute/k4-rt4-n5b, -n5c, `results/k4_rt4/n5*_FAILURES.md`; the ledger statuses are the
coordinator's to change); the new target relation is R_C = (T1) ∪ (T2) ∪ (T3⁺) ∪ (T4), with (T3⁺) the frozen-chain role
swap. At f = 1, (T3⁺) = (T3), so the question of this file is unchanged.

## 1. The target states (EVIDENCE)

`k4/thetab_targets.py` reads PR #75's dumps (`results/k4_dl13_stuck/stuck_*.jsonl.gz`) and keeps the T3-stage states
(no (T1), (T2) or (T4) move lowers the deficit) that none of C1, C2, C3 (`k4/dl13.md` §4) certifies: 1,343 records,
1,223 of them at f = 1:

| class | f = 1 | f = 2 |
|---|---|---|
| S1 shape, every triple θ-b | 1,199 | 43 |
| S1 shape, every triple θ-a | 2 | 0 |
| no S1 shape | 22 | 77 |

At f = 1 (x frozen on g):
- **1,219 of the 1,223 have exactly two needers of g, both big-top on g, and x has four goods and is not big-top**
  (all 1,154 at n = 3, 65 at n = 4). The other four are at n = 4: two θ-a states with three needers (4 + 4 + BT), one
  θ-b state with needers 4 + BT, one with 4 + BT + BT.
- **Every one of the 1,223 has a (T3) repair without helper whose best owner afterwards is a needer that did not move**
  (the *other-needer swap*): one needer z takes g, x takes one or two goods of J ∪ B_z, and another needer owns.

## 2. Lemma G: the plain swap seen from an unmoved owner

(Written proof below; to be refereed.)

## 3. Theorem N3: n = 3

(Written proof below; to be refereed.)

## 4. General n

## 5. Failed candidates

## 6. Reproduce

```
mkdir -p k4/suite/.cache/gapbench
git archive 245040b results/k4_gap | tar -x -C k4/suite/.cache/gapbench      # #53's catalogues (k4/strategy.md §4)
python3 k4/thetab_targets.py > results/k4_thetab/targets.log                    # §1, §4
```
