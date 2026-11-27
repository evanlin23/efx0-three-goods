# Failed: Conjecture R2 (two receivers ⟹ one move) is false at n = 5

Workstream `proof/k4-ttc` (`k4/ttc.md` §14.6). **Status:**
- **R2 is REFUTED at n = 5**, and R2-C with it. The certifier found it (`compute/k4-oc1max-cert`, commit b70dd88c, PR #120):
  five stored OC₁^max-failing starts with two receivers, on 5_pure idx 650, 655 (two profiles), 1014 and 1050
  (`results/k4_oc1max/n5/r2_two_receiver_fails_n5.jsonl` there).
- **Checked there:** `verify_r2.py`, and `brute_verify.py` with no repository code.
- **Replayed here:** idx 650, by the brute force `k4/ttc/refute_oc1.py` (no SAT, no shared code) and by SAT.
- **Still true:** R2 is CERTIFIED at n ≤ 4 (K4.SDC.R2.N4), as is R2-C at n = 4. RF and OC₂^max hold at all five
  starts.

## Smallest failing configuration (n = 5, m = 8), 5_pure idx 650

`results/k4_ttc/r2_cex_n5.json`

| agent | goods (value) | pick |
|---|---|---|
| 0 | g0 (3), g1 (6), g5 (7), g7 (5) | g5 |
| 1 | g0 (2), g5 (10), g6 (7), g7 (6) | g0 |
| 2 | g1 (2), g5 (8), g6 (4), g7 (3) | g1 |
| 3 | g2 (4), g3 (5), g4 (6), g6 (8) | g6 |
| 4 | g2 (5), g3 (4), g4 (6), g7 (8) | g7 |

**The start.** Order (0, 3, 4, 1, 2), picks (g5, g0, g1, g6, g7), junk {g2, g3, g4}.

**Core conditions.**
- `is_core4` returns [].
- ν = 5: a perfect start.
- No agent has two private goods: the K4.MC2 class.

**Receivers.** Agents 1 and 2 are the receivers. Agents 0, 3 and 4 are frozen, and the twins 3 and 4 are dangerous.

**OC₁ fails, the free form too** (`results/k4_ttc/refute_r2_cex_n5.log`). The picks have no free or one-absorber
completion, and neither do the bases after any of the 62 moves (14 additions, 32 chains, 16 rings).

## Why two receivers are not enough here

- The twins 3 and 4 share the junk triple {g2, g3, g4}, and every pair of it beats each twin's pick (8).
- Both receivers value no junk, so neither can make an addition.
- Three junk goods on two receivers put two of them next to a receiver's pick, and that bundle minus the pick is a
  danger pair for a twin.
- A move that repairs one twin uses a pair, and leaves the other twin threatened by the leftover good together with
  the goods the move releases.

This is the shared-pool (PW) mechanism with two sharers and two receivers. At k = 4, Lemma PL bounds the pool leftover
by one good for agents sharing two goods of H₀, but not the goods the chain releases.

## Reproduce

```
(cd k4/ttc && python3 refute_oc1.py ../../results/k4_ttc/r2_cex_n5.json 0)
```
