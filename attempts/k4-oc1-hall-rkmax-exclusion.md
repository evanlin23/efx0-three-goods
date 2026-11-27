# RKMAX plan (a): "σ-maximality excludes one receiver with |D_T| ∈ {0, 2, 3} at n ≥ 5" is false

*Workstream* `proof/k4-oc1-hall`; notes in `k4/oc1_hall.md` §24.14.

*Idea* (the coordinator's RKMAX plan, item (a)). Conjecture RKMAX (`k4/sdc.md` §31, K4.SDC.RKMAX) says that OC₁ holds at
every maximum-matching SD vector whose rank signature σ = (#rank 1, …, #rank 4) is lexicographically maximal. A short
proof might first show that at n ≥ 5 such a vector never has exactly one receiver unless it has exactly one truly
dangerous agent. Corollary U1 covers that remaining case. The idea came from the n = 5 failure exports, where no other
one-receiver class occurs at σ-maximal vectors (§24.12).

*Why it fails.* On random strict profiles of the pure n = 5 cores, σ-maximal vectors of classes (1, 0) and (1, 2) occur.
The export profiles are biased toward the failing profiles of 9 hypergraphs.

*Smallest failing configuration found* (n = 5, m = 8):
- 5_pure idx 358, sets [[0,1,4,5],[1,3,6,7],[2,3,6,7],[2,4,5,7],[4,5,6,7]];
- values [[17,4,2,19],[13,14,20,16],[2,16,20,17],[5,17,15,7],[20,17,4,8]];
- 10 maximum-matching SD vectors. The σ-maximal ones are (5,7,6,2,4) and (5,6,7,2,4), with σ = (3,1,0,1);
- both have J = {0,1,3}, one receiver {3} and D_T = {0,1}, i.e. class (1, 2). OC₁ holds there after one move, so
  RKMAX itself is not refuted.

*Census* (`k4/oc1_hall/rf_rkmax_rand.py 60 2`, `results/k4_oc1_hall/rf_rkmax_rand.log`, 280,380 random profiles):
- one-receiver σ-maximal vectors: (1, 0) 161, (1, 1) 12, (1, 2) 5; (1, 3) not seen;
- no OC₁ failure at any σ-maximal vector.

*Repro:* `python3 attempts/k4_oc1_hall_rkmax_exclusion.py` (exit status 0 iff the configuration is as stated).
