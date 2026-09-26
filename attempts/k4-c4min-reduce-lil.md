# The local improvement lemma with a narrower move catalogue, and without the core rules (k = 4, f = 1)

Workstream `proof/k4-c4min-reduce` (`k4/c4min_reduce.md` §5.3, ledger row K4.C4MIN.RED.LIL). Found by the review of
PR #51 (the computational reviewer's narrow-catalogue runs and the referee's non-core instance), confirmed here.

**Approach.** Conjecture LIL says that every configuration at f = 1 without a valid owner has a move that raises
Φ_r = (r′, −t, Λ), among M1 (one free agent re-pairs inside its pair and the pool), M4 (rotation along a threat cycle)
and M5 (path move from a terminal to x). Two tempting simplifications fail:
1. **Narrow catalogue.** Take the rotations and path moves exactly as the written lemmas have them. The modified
   receiver is only Lemma R(iii)'s of `k4/c4min.md` and #50's (`k4/c4min_f1.md` §2, read at 5028edf): a receiver z of
   kind (R) (four goods, g ∉ R_z, holding a non-robust pair {p, q} ⊆ R_z ∖ {a_z}, fourth good s_z) with a_z in the pair
   it receives and s_z in the pool (in M5: in L ∖ P_x) takes {a_z, s_z}. In M5, x takes #50's best pair P_x inside
   (Q_{p_k} ∪ L) ∩ U_x, or any pair. Optionally add #50's recycling rule (the last receiver of kind (R) takes a_z with
   its better good of Q_{p_k} ∖ P_x).
2. **No core rules.** Drop the private-goods rule of k = 4 cores (a 4-good agent has at most two private goods).

**Why it fails.**
- The narrow catalogue leaves stuck configurations (`k4/red.c -L -Lr -L2 -Ln [-Lx] [-Lc]`, `results/k4_red_lil_narrow.log`;
  potential (r′, −t, Λ), no M2):

  | narrow catalogue | n ≤ 3, every profile | n = 4, one 4-good agent, every profile | n = 4, two 4-good agents, every profile | n = 4, three or four, 4,000 per core (seed 7) | n = 5 samples |
  |---|---|---|---|---|---|
  | x any pair | 4,208 | 0 | 992 | 128 | 79 |
  | x's best pair (#50) | 16,832 | 0 | 992 | 129 | 79 |
  | x any pair, with recycling | 0 | 0 | 992 | 128 | 79 |
  | x's best pair, with recycling | 0 | 0 | 992 | 128 | 79 |

  The n = 5 samples are those of `results/k4_red_lil.log` (3,000, 600, 200 profiles per core); the 79 are in the
  cores with three or more 4-good agents. Every stuck configuration at n ≤ 3 has a big-top x. The broad catalogue of `k4/c4min_reduce.md` §5.3 (one receiver
  exchanges one good of the pair it receives for any pool good, in M5 for any good of the new pool; x takes any pair)
  has 0 stuck configurations on the same scopes (`results/k4_red_lil.log`). The difference is that the broad exchange
  lets a receiver of a path move keep one of its own goods, which #50's modification (s from L ∖ P_x only) does not,
  and #50's recycling allows only for the last receiver of kind (R). PR #53's model finds the same necessity
  (`results/k4_red_lil_gapbench.log`: 6 counterexamples at n = 3 without `keep`).
- Without the core rules even the broad catalogue is stuck (instance NC below), while the global potential still works
  there (every Φ_r-maximum over all keys is completable, as Conjecture GLOB says). So a proof of LIL must use the
  private-goods rule; `k4/c4min_reduce.md` §5.3 says where (t = 1 with a big-top x).

**What it shows.** The move catalogue of a proof must contain the broad exchange (a receiver keeping a good of its own
or of the pool), and the proof must use the core's private-goods rule. The narrow catalogue's failures are not failures
of Conjecture LIL as stated (with the broad catalogue).

**Smallest failing configurations** (replayed by `attempts/k4_c4min_reduce_lil.py` with `k4/red_lil.py` on
`k4/red_lib.py` and with `k4/red.c`; for each catalogue both count the same stuck configurations on the profile; log
`results/k4_red_lil_attempts.log`, "ALL CONFIRMED"):
- **N1** (narrow catalogue, n = 3, m = 7; core 43 of `results/k4_certs_3.json.gz`). Agents {0, 3, 4, 6}, {1, 3, 5, 6},
  {2, 4, 5, 6}, values 0:4, 3:2, 4:8, 6:5 | 1:2, 3:6, 5:10, 6:3 | 2:1, 4:6, 5:8, 6:4. Key (5, 1) (x = 1, big-top),
  pairs Q_0 = {0, 6}, Q_2 = {2, 4}, pool {1, 3}: not completable, Φ_r = (1, 0, 19), stuck for the narrow catalogue
  with either choice of P_x. The broad catalogue raises it by a path move to the key (5, 2) in which agent 0 keeps its
  good 6 with the good 4 it receives (pairs {4, 6}, {0, 3}, pool {1, 2}, Φ_r = (2, 0, 21)); recycling does the same.
- **N2** (narrow catalogue with recycling, n = 4, m = 9; core 283 of `results/k4_certs_4_n4_2.json.gz`). Agents
  {0, 2, 6, 7}, {1, 4, 6, 8}, {3, 5, 8}, {5, 7, 8}, values 0:3, 2:7, 6:5, 7:6 | 1:2, 4:3, 6:4, 8:8 | 3:2, 5:3, 8:4 |
  5:2, 7:3, 8:4. Key (8, 2) (x = 2, three goods), pairs Q_0 = {2, 5}, Q_1 = {1, 6}, Q_3 = {4, 7}, pool {0, 3}: not
  completable, Φ_r = (2, 0, 14), stuck with recycling (either choice of P_x). The broad catalogue raises it by a path
  move to the key (8, 1) (pairs Q_3 = {4, 7}, Q_0 = {1, 2}, Q_2 = {0, 5}, pool {3, 6}, Φ_r = (2, 0, 15)).
- **NC** (no core rules; the referee's instance, n = 3, m = 9). Agents x = {0, 1, 2, 3} with values 0:10, 1:5, 2:4,
  3:2; τ₁ = {0, 4, 5, 6} with 0:10, 4:5, 5:4, 6:2; τ₂ = {0, 6, 7, 8} with 0:10, 7:5, 8:4, 6:2. f = 1 and every key is
  big-top. At the key (0, 0), τ₁ holding {4, 5}, τ₂ holding {7, 8} and the pool {1, 2, 3, 6} form a pool-optimal
  configuration with t = 1, not completable, Φ_r = (2, −1, 19), stuck for the broad catalogue (the only stuck
  configuration of the profile, in both implementations). Every Φ_r-maximum over all keys ((2, 0, 18)) is completable
  (C: `pot[r,mt,lamR]_every`). x has the three private goods 1, 2, 3; a 4-good agent of a k = 4 core has at most two.

Replay: `python3 attempts/k4_c4min_reduce_lil.py` (seconds).
