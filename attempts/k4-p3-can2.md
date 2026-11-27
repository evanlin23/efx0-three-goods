# Attempt: at p ≤ 2, the canonical chain of some dangerous agent always repairs (Conjecture CAN₂), refuted at n = 4

Workstream `proof/k4-p3` (`k4/p3.md` §6). This file follows the `attempts/` format: what was tried, why it looked right,
how it fails, the smallest failing configuration, and a script that reproduces it.

## The claim

**Conjecture CAN₂.** Let every agent value at most four goods and every good at most two agents, with strict values.
At every perfect start (serial-dictatorship picks forming a maximum matching, every agent holding a pick) that has no
one-absorber EFX₀ completion, the following holds for some dangerous agent k and some H₀ ⊆ (J ∪ {Y_z}) ∩ R_k with
v_k(H₀) > p_k: the state after k's unique canonical chain P(k) = (k, w(k), w(w(k)), …, z) has a one-absorber
completion. Here w(i) is the unique agent that wants Y_i.

If true, CAN₂ would have reduced OC₁^max(2) to choosing k. Proposition KEEP₂ and Corollary U₂ (`k4/p3.md` §6, proved)
make that choice in most cases.

## Why it looked right

`k4/p3/keep2.py` was run on 22,677 hard p ≤ 2 starts:
- the 210 starts of `proof/k4-oc1max-multi`;
- 22,467 fresh starts from every multigraph core with n ≤ 6, with random strict profiles, by `k4/p3/t1_p2.py`.

Every one was repaired by some P(k). At p = 3 the start T3 needs a ring, so canonical chains looked like a special
feature of p ≤ 2.

## How it fails

Random profiles miss the failures. The same happened with the 11 OC₁^max failures at n = 4.

The exhaustive check was done with `k4/p3/can2cert.py`. It runs the ordinal CEGAR of `compute/k4-oc1max-cert` (commit
cfb3c18d, imported unmodified) with its moves restricted to canonical chains. The certificate is then re-checked by
that session's independent checker, restricted the same way. Results are in `results/k4_p3x/can2/`:
- **n = 2, 3:** all 26 multigraph cores are certified, and the checker covers all 26. So CAN₂ holds for n ≤ 3.
  - Negative test: the restricted checker rejects the OC₁^max certificate of the same hypergraphs at 20 of the 26
    (`negtest_cert_23_mg.log`). This shows the restriction actually removes moves.
- **n = 4:** 83 of the 112 multigraph cores are certified, and the checker covers all 83. The other **29 fail**.
- `k4/p3/can2_replay.py`, using my code only, replays all 29 failures (`replay_can2_4_mg.log`). Each one:
  - is a perfect SD start;
  - is hard, by SAT and by plain enumeration;
  - has no canonical chain with an improving set that leaves a completion;
  - is repaired by some official move, so OC₁^max holds there, as Proposition MG₅ says.

  All 29 have |D| = 2 and D_T = ∅. In all 279 move states of the 29 failures with m ≤ 8, SAT and enumeration agree.
- At 2 of the 29, **no ED chain repairs** with any one-absorber completion. (In an ED chain, `k4/oc1_hall.md`, the
  middle agents take exactly their predecessor's pick and only the head adds junk.) So at p ≤ 2 the junk taken by a
  middle agent is needed, even though OC₁^max holds.

- **n = 5:** 501 of the 686 multigraph cores are certified, and **185 fail**. All 185 are replayed and repaired by
  other official moves (`replay_can2_5_mg.log`).
  - 183 are crossed. The other 2 have several truly dangerous agents and are repaired only by chains whose receivers
    add junk.
  - 12 have no repairing ED chain.

## Smallest failing configuration (n = 4, m = 7)

A multigraph core in the official sense (`k4/check4.is_core`).

| agent | values (good: value) | pick | |
|---|---|---|---|
| 0 | 0: 4, 1: 2, 2: 3, 3: 8 | 0 | unfrozen (root); wants Y₃ = 3 |
| 1 | 0: 3, 2: 2, 5: 4 | 5 | frozen (agent 2 wants 5); dangerous, pick-dangerous |
| 2 | 1: 2, 4: 3, 5: 8, 6: 4 | 6 | unfrozen (root); wants Y₁ = 5 |
| 3 | 3: 4, 4: 2, 6: 3 | 3 | frozen (agent 0 wants 3); dangerous, pick-dangerous |

- The order is (1, 2, 3, 0), and also (1, 3, 0, 2) and others. It gives the picks (0, 5, 6, 3), and J = {1, 2, 4}.
- The two trees are 1 → 2 and 3 → 0.
- Agent 1's danger is junk 2 plus the *other* tree's root pick 0 (2 + 3 > 4). Agent 3's danger is junk 4 plus root 2's
  pick 6 (2 + 3 > 4).
- So neither canonical chain has an improving set. P(1) = (1, 2) has the pool {2}, worth 2 < 4. P(3) = (3, 0) has the
  pool {4}, worth 2 < 4.
- The picks have no one-absorber completion.
- The only repairing moves are three chains of four agents that cross both trees, for example 1 → 2 → 3 → 0:
  - agent 2 takes 5;
  - agent 3 takes 6 *plus junk 4* (3 + 2 > 4); it is a middle agent;
  - agent 0 takes 3;
  - agent 1 takes {0, 2}.

  This gives the bases [3], [0, 2], [5], [4, 6], and the EFX₀ allocation [1, 3], [0, 2], [5], [4, 6].
- No addition, no shorter chain, no ring and no ED chain repairs.

So the same start also refutes:
- my "sharpened" Conjecture OC₁^max(2) of `k4/p3.md` §6 (an addition or a chain of at most three agents);
- the "pure move" target there.

## Reproduce

```
python3 k4/p3/can2_smallest.py                     # the n = 4, m = 7 start, plain enumeration only (no SAT)
OC1CERT=/path/to/compute-k4-oc1max-cert python3 k4/p3/can2cert.py run 4_mg --jobs=2 --out=can2_4_mg.json.gz
OC1CERT=/path/to/compute-k4-oc1max-cert python3 k4/p3/can2cert.py check can2_4_mg.json.gz --lists=4_mg
python3 k4/p3/can2_replay.py can2_4_mg.json.gz     # the 29 failures, independent code
```

The list `4_mg` is written by `python3 k4/p3/mg_cores.py 4 CHECKOUT`. Expected output of `can2_smallest.py`: no
completion at the picks, no improving set on either canonical chain, and `repairing official moves (by enumeration):
{('chain', 4): 3}` (`results/k4_p3x/can2/can2_smallest.log`).
