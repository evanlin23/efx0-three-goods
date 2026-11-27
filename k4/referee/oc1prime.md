# Referee report: K4.SDC.OC1PMAX, OC₁′^max refuted at n = 5 and holding at n = 4 (`k4/sdc.md` §31, `kgen/rounds.md` §4.6)

Referee: `proof/k4-referee`, 2026-11-27, at the coordinator's request.
- Read, on `origin/main` at `9cb9a45`:
  - `k4/sdc.md` §31 (the OC₁′^max paragraph);
  - `kgen/rounds.md` §1 (chains, completions) and §4.6 (the OC₁′ move);
  - the ledger row K4.SDC.OC1PMAX;
  - the definition of a k = 4 core (ledger K4.CORE).
- Check: `k4/referee/oc1p_ref.py`, log `results/k4_referee/oc1p_ref.log`.
  - It is my own code: the OC₁′ move generator is written from the definition. The §29 moves, the one-absorber
    completion and raw EFX₀ come from my certifier-referee helpers (`cert_ref.py`).
  - Nothing from `k4/sdc/` or `kgen/rounds/` was run or imported.
  - The certifier's n = 4 export (`results/k4_oc1max/two_move_starts_n4.json.gz` on `compute/k4-oc1max-cert`, sha256
    `6159e38d1e70ae16…`, as the note states) is read as data.

## Verdict

| claim | verdict |
|---|---|
| **n = 5: OC₁′^max is false** (5_pure idx 164, picks (7, 2, 3, 5, 4)) | **CONFIRMED** independently, every stated detail |
| The mechanism: two disjoint conflicts; the 9 value-dominating EFX₀ allocations; repaired by two moves or one round of two disjoint moves | **CONFIRMED** |
| **n = 4: OC₁′ holds at all 112,880 OC₁^max-failing starts** of the certifier's export | **CONFIRMED**, a third implementation, all 112,880 |
| **n = 4: OC₁′^max on every strict connected n = 4 core** | **CORRECT, conditional on the certifier's export being complete**. That rests on the certifier's OC₁^max certification at every other n = 4 start and its ordinal type reduction. I checked that certificate by sampling (item 21), not exhaustively. OC₁′ is type-invariant: SD picks, gains and EFX₀ all compare subset sums |

## 1. The n = 5 instance

The instance is sets [[0,2,3,7],[1,2,6,7],[3,4,5,6],[3,4,5,7],[4,5,6,7]] with values
[[1,8,6,4],[4,8,2,7],[6,7,3,5],[7,10,2,6],[7,5,3,6]], so n = 5 and m = 8.

**It is a strict connected k = 4 core (K4.CORE).**
- Every agent has 4 goods and is strictly balanced: 8 < 11, 8 < 13, 7 < 14, 10 < 15, 7 < 14.
- Private goods: 0 for agent 0 and 1 for agent 1 (one each); the others have none.
- Every good is relevant, and the incidence graph is connected.
- Every agent's type is strict: no two disjoint nonempty subsets have equal value (checked by enumeration).

**The start.**
- Exactly three orders give the picks (7, 2, 3, 5, 4): (1,4,2,0,3), (4,1,2,0,3) and (4,2,1,0,3), as stated. I checked
  all 120 orders.
- ν = 5, so the picks are a maximum matching. J = {0, 1, 6}.

**OC₁′ fails.**
- The picks have no one-absorber completion.
- My generator implements OC₁′ as additions, plus chains whose non-end agents may also take goods of the end's
  released base, with H sets inside the taker's relevant goods. It finds **21** move states, matching the note. **None
  has a one-absorber completion.**
- *Robustness check.* A wider generator also lets H sets include goods the taker values at 0 (124 states), and none of
  those completes either.
- The §29 official moves give the same 21 states. At singleton bases the widening adds nothing new here.

**The mechanism.** Brute force over all 5⁸ allocations:
- there are exactly **9** EFX₀ allocations that value-dominate the picks;
- in all 9, agent 0 gets good 2 and agent 1 gets goods 7 and 1, and agent 3 gets good 4 or good 3.

The stated one-round repair is the ring 0 ↔ 1 with junk 0, 1 plus the ring 3 ↔ 4 with junk 6, giving
({0, 2}, {1, 7}, {3}, {4}, {5, 6}).
- It is EFX₀, and every mover gains: 9 > 4, 11 > 8, 10 > 2, 8 > 7.
- Two sequential moves repair the start: the §29 search depth is 2. With OC₁′ moves, 9 of the 21 first moves can be
  followed by a repairing second move.

## 2. The n = 4 claim

**What I checked.**
- For each of the 112,880 starts in the certifier's export, my code confirms that the stored picks are the SD picks of
  a stored order.
- It then finds an OC₁′ move state with a one-absorber completion: **112,880 of 112,880**.
- In `liftn4_ref.log` (item 31), I had already found that the §29 moves do not repair any of these starts. So the
  widening is what repairs each one.

**What it rests on.**
1. The export lists *every* OC₁^max-failing (type profile, picks) pair on the 11 n = 4 hypergraphs. That is the
   certifier's CEGAR certification, which I refereed by sampling only (item 21: 35,858 sampled and 30,222
   near-counterexample starts, all covered by validated witnesses).
2. OC₁′ depends only on the agents' order types. SD picks compare single goods; gains and EFX₀ compare subset sums; so
   a type profile decides OC₁′. Correct.

So OC₁′^max at n = 4 has the same standing as the certifier's OC₁^max certificate. The 112,880 OC₁′ checks have now
been made by three independent implementations.
