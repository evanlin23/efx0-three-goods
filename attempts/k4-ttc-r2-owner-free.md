# Failed: R2★ and R2-M (owner-free, or the chain's head as owner) as the proof target for R2

Workstream `proof/k4-ttc` (`k4/ttc.md` §14.6). **Status:**
- *Refuted at n = 4, exhaustively,* by the certifier (`compute/k4-oc1max-cert`, its message of 01:10; failing starts in
  `results/k4_oc1max/r2m_fails_n4.jsonl` there). Two of its examples are replayed here (`k4/ttc/r2_owner_check.py`,
  `results/k4_ttc/r2_owner_check.log`).
  - R2-M fails on 306 of the 1,002 n = 4 cores.
  - R2★ fails on 5 of the 20 R2-M failures re-verified by the certifier's raw brute force.
- *Not refuted:* R2 itself, which is CERTIFIED at n ≤ 4 (K4.SDC.R2.N4), and the target **R2-O** below, which holds on
  both replayed examples.

## The refuted targets

At a perfect serial-dictatorship start with |U| ≥ 2 receivers and no one-absorber completion at the picks, take a
canonical chain: x₀ dangerous, x₁ valuing y_{x₀} above y_{x₁}, ending at a receiver z. The two targets said that some
such chain is followed by:
- **R2★:** a completion in which every agent receives at most one junk good (no absorber);
- **R2-M:** Lemma M^c's S^c completion with owner x₀ and at most one junk good for it (`proof/k4-oc1max-multi` §9,
  `max_rest = 1`).

Sampled data had supported both (79/79 at n = 4, 466/466 at n = 6). The exhaustive n = 4 run did not.

## Smallest failing configuration (n = 4, m = 7)

| agent | goods (value) | pick |
|---|---|---|
| 0 | g0 (2), g5 (3), g6 (4) | g0 |
| 1 | g1 (2), g5 (3), g6 (4) | g1 |
| 2 | g2 (6), g3 (4), g4 (5), g5 (8) | g5 |
| 3 | g2 (6), g3 (5), g4 (4), g6 (8) | g6 |

**The start.** Picks (g0, g1, g5, g6), junk {g2, g3, g4}.
- The receivers are 0 and 1. Each holds its worst good, a private one, and wants g5 and g6, so agents 2 and 3 are
  frozen.
- The junk is a triangle shared by the dangerous agents 2 and 3: every pair beats 8.

**Why it is hard.** The three junk goods must go to the two receivers, and a bundle with two of them is envied.

**Every repairing move** is a canonical chain (2 or 3, then 0 or 1) in which the dangerous agent takes a pair of the
triangle and the receiver takes its pick.
- In every case the completion's absorber is **the other receiver**: owner 1 after a chain to 0, owner 0 after a
  chain to 1.
- The dangerous agent cannot take more junk (its pair plus anything is envied by the other sharer).
- The receiver z now holds a wanted pick, so it is frozen.
- So two junk goods remain for one free agent: an owner is needed.

A second example (sets [[0,2,6,7],[1,4,5,6],[3,6,7],[4,5,7]], vals [[4,2,10,7],[3,5,6,7],[2,3,4],[3,2,4]], picks
(g0, g6, g3, g7)) behaves the same way.

## What survives: R2-O

**R2-O.** Some canonical chain to a receiver z is followed by a one-absorber completion whose owner is *another*
receiver u ∉ the chain. That is the coordinator's original shape: one receiver is the chain's end, the other is the
owner.
- It holds on both examples.
- It holds on all the sampled data: "owner another receiver off the path: some", 79/79 at n = 4 and 466/466 at n = 6
  (`r2_shape_*.log`).
- An exhaustive n = 4 check was requested from the certifier.

## Reproduce

```
MC_DIR=<proof/k4-oc1max-multi checkout>/k4/oc1max_multi python3 k4/ttc/r2_owner_check.py   # MC_DIR only for the M^c column
```
