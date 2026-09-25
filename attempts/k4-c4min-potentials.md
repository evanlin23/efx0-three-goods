# Potentials over configurations that do not work (k = 4)

Workstream `proof/k4-c4min` (`k4/c4min.md` §2–§4). Approach: over the configurations at the fewest frozen agents
(`k4/c4min.md` §1: frozen agents hold the needed set 𝒩, every other agent an admissible pair outside 𝒩, the rest is
the pool), take a maximum of a potential and show it has a valid owner. Theorem Z (f = 0) and Theorem F
(frozen-robust configurations) do this with (r, Λ) = (number of robust agents, sum of levels). Conjecture Φ uses
(−t, r, Λ) in general. The simpler potentials below fail: some maximum has no valid owner, although another
configuration of the same profile is completable (so C₄ᵐⁱⁿ itself holds there).

Each instance is replayed by both implementations: `k4/c4min.c` on the one profile, and the independent
`k4/c4min_cfg.py` (configurations, owners with the unfreezing clause, features from the definitions). For the
instances with n = 3 the replay also runs `k4/c4min.c` on every strict profile of every core with n = 2 (0 failures),
so n = 3 is the smallest n. The m of an instance is the first one found and is not claimed to be the smallest. Replay:
`python3 attempts/k4_c4min_attempts.py` (about a minute; log `results/k4_c4min_attempts.log`, ends "ALL CONFIRMED").

1. **The robust count r alone, f = 0.** n = 3, m = 7 (smallest n). Agents with goods {0, 2, 5, 6}, {1, 4, 5, 6},
   {3, 4, 5, 6} and values 0:10, 2:2, 5:6, 6:7 | 1:2, 4:7, 5:4, 6:8 | 3:3, 4:7, 5:6, 6:5. Of the 26 r-maxima (r = 1) one
   has no valid owner: pairs {0, 5}, {2, 6}, {1, 4}, pool {3}.
   - Agents 1 and 2 hold their tops with each other's worthless goods (2 is agent 0's, 1 is agent 1's) while agent 2's
     own good 3 sits in the pool.
   - Swapping them raises values but not r, so it is not pool-optimal.
   - Theorem Z adds Λ, which forces pool-optimality.
2. **Pool-optimality alone, f = 0.** n = 2, m = 5. Agents {0, 2, 3, 4} and {1, 2, 3, 4} with values 0:1, 2:4, 3:6, 4:8
   | 1:2, 2:4, 3:5, 4:8. The pool-optimal all-pairs allocation {0, 4} | {2, 3}, pool {1}, has no valid owner.
   - Neither agent is robust, and each threatens the other (the permutation of Lemma P).
   - The rotation of Lemma R (modified) gives agent 1 {4, 1} and agent 0 {2, 3}, both robust.
   - So r must be maximized too (5,624 profiles with n = 2).
3. **(r, Λ) and Λ alone, f = 1.** n = 3, m = 8 (smallest n). The all-4-good core {0, 2, 6, 7}, {1, 4, 6, 7},
   {3, 5, 6, 7} with values 0:3, 2:6, 6:10, 7:2 | 1:3, 4:6, 6:10, 7:2 | 3:2, 5:3, 6:10, 7:6.
   - Agent 2 is frozen on its top 6 and is of type a > b + c (threatened only by {3, 5, 7} together).
   - At a maximum of (r, Λ) all three sit in the pool, so agent 2 is threatened by every owner.
   - Conjecture Φ therefore puts −t, the number of frozen agents the pool alone threatens, first.
4. **(−t, Λ), f = 2.** n = 3, m = 6 (smallest n). Agents {0, 1, 2, 5}, {2, 3, 4, 5}, {3, 4, 5} with values 0:4, 1:3,
   2:2, 5:8 | 2:4, 3:1, 4:8, 5:6 | 3:2, 4:4, 5:3.
   - Three of the four maxima have no valid owner.
   - In them agent 0 is frozen on its top 5 and exposed (its goods 0, 1, 2 reach 9 > 8), and the only free agent must
     be the owner.
   - Putting r second, as Φ does, makes the maxima prefer keys whose frozen agents are robust.
5. **Pareto-maximality, f = 1.** n = 3, m = 7 (smallest n). Agents {0, 1, 2, 3}, {2, 4, 5, 6}, {3, 4, 5, 6} with values
   0:3, 1:2, 2:10, 3:6 | 2:8, 4:4, 5:2, 6:3 | 3:3, 4:2, 5:6, 6:10. Three of the five Pareto-maximal configurations have
   no valid owner. At f = 0 every Pareto-maximal configuration was completable on every profile tested
   (`results/k4_c4min_z_n3.log`), but the proof of Theorem Z uses r, not Pareto-maximality.
6. **Configurations without the unfreezing clause.** n = 2, m = 6. Agents {0, 1, 4, 5} and {2, 3, 4, 5} with values
   0:6, 1:3, 4:10, 5:2 | 2:4, 3:3, 4:8, 5:2.
   - Both agents have top 4, and f = 1.
   - Only the owner (the other agent) needs 4. The owner's bundle {2, 3} ∪ pool is worth more to it than 4.
   - So with the owner's needs taken from its bundle the holder of 4 is free, takes a slot good and is protected. No
     configuration is completable without this (720 profiles with n = 2, `results/k4_c4min_xcheck.log`), so Lemma 1
     needs the clause. For n = 3 and 4 no maximum of Φ needed it on the samples.

**Smallest failing configuration.** Instance 2 (n = 2, m = 5) for pool-optimality alone; instances 1, 3, 4 and 5 at
n = 3 for the others.
