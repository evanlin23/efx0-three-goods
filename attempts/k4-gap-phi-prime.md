# Attempt: Conjecture Φ′ (every Φ′-maximum has a valid owner) is false at n = 4 (compute/k4-gap)

**Statement tried.** Conjecture Φ′ of `k4/c4min.md` §4 (PR #41, ledger K4.C4MIN.PHI). Take any strict profile of any
k = 4 core with ω ≥ 1. Then every configuration at the fewest frozen agents that maximizes Φ′ = (−t, r, Λ, −p)
(lexicographic) has a valid owner (§1 of `k4/c4min.md`). Here:
- t is the number of frozen agents threatened by the pool alone;
- r is the number of robust agents;
- Λ is the sum of the levels;
- p = Σ over frozen x of |L ∩ U_x|.

The conjecture holds on every profile with n ≤ 3 and on every profile of the n = 4 cores with one 4-good agent
(`k4/gap.md` §2, and #41's own runs).

**It fails on two pure n = 4 profiles.** They were found by the hunt over 400,000 random profiles per pure n = 4 core
(`results/k4_gap_hunt_n4_pure_s400k.log`: 4,483,858 gap profiles, 2 in category N). The smaller is core 104 of
`results/k4_certs_4_pure.json.gz` (0-based position), with m = 8.

| agent | goods and values | at the Φ′-maximum |
|---|---|---|
| 0 | 0:2, 2:3, 5:6, 7:10 (big-top: 10 > 6 + 3) | frozen on 7 (its top); U_0 = {0, 2, 5} worth 11 > 10, exposed |
| 1 | 1:3, 4:2, 6:6, 7:10 | free, Q_1 = {1, 6}, robust; needs 7 |
| 2 | 2:6, 3:10, 4:3, 6:2 | free, Q_2 = {2, 4}, robust; needs 3 |
| 3 | 3:8, 5:4, 6:5, 7:2 | frozen on 3 (its top); U_3 = {5, 6} worth 9 > 8, exposed |

- **The maximum.** f = 2 and ω = 2. The pool is L = {0, 5}, and Φ′ = (0, 2, 25, −3). This configuration is the unique
  Φ′-maximum among the 36 configurations of the 3 keys, and it is Pareto-maximal.
- **No valid owner.** Owner 1 (X = {1, 6, 0, 5}) threatens the frozen agent 3: goods 5 and 6 are worth 9 > 8. Owner 2
  (X = {2, 4, 0, 5}) threatens the frozen agent 0: goods 0, 2 and 5 are worth 11 > 10. Both threats are local (class L
  of `k4/hall.md` Lemma H7). No withheld set C helps: the unfreezing bound allows none. Each owner's bundle is worth
  at most 9 to it, so it still needs its own frozen neighbour's good (7 for owner 1, 3 for owner 2), and the other
  frozen good is needed by the other free agent.
- **C₄ᵐⁱⁿ still holds.** 34 of the 36 configurations have a valid owner, and some min-frozen pre-allocation has
  removal-only deficit ≤ 0. The best completable configurations have Φ′ = (0, 2, 24, −3), one unit of Λ below the
  maximum.
- **What repairs it.**
  - #52's downgrade swap: agent 0 gives 7 to agent 1 and takes a pair of L ∪ Q_1, for example {0, 5}. The result has
    owners and Φ′ = (0, 2, 24, −3).
  - Exchange cycles through the big-top agent 0 (cycle 0 → 1 → 3 → 2), as #52's K4.HALL.BTCYC predicts.

The second profile (core 183, m = 10, f = 2, ω = 4) has the same structure: a unique Φ′-maximum, two frozen agents,
each owner blocked by one local threat, and 91 of 125 configurations with a valid owner.

**How often.** The final hunt counts, per profile, whether some Φ′-maximum has no valid owner (the counter `phibad` of
`k4/gap.c`). It finds 33 such profiles: 30 among the 4,483,858 pure n = 4 gap profiles and 3 among the 5,826,602 with
three 4-good agents (`results/k4_gap_hunt_n4_*.log`). They have 55 such maxima in all, re-derived by gap_model
(`results/k4_gap_bench_hard_hunt.log`, statement PHI_PRIME). In 31 of them another Φ′-maximum has a valid owner, so
only the "every maximum" form fails there. The two profiles above are the ones where no maximum has one. `phibad` is 0
on every profile with n ≤ 3, on every profile at n = 4 with one or two 4-good agents, and on the n = 5 samples.

**Checked three times, by independent implementations** (`results/k4_gap_phi_prime.log`):
1. `k4/gap.c` (C, the catalog enumerator);
2. `k4/gap_model.py` (Python, independent of gap.c);
3. #41's own `k4/c4min_cfg.py` and `k4/c4min_lib.py` (another author; its `phi_key()` is Φ, and p is appended).

All three find the same numbers: 36 (125) configurations, 34 (91) with a valid owner, a unique Φ′-maximum with the
value above, and no valid owner at it.

**What survives.**
- C₄ᵐⁱⁿ on these profiles.
- The existence and reachability forms: from each non-completable Pareto-maximum, exchange cycles and downgrade swaps
  reach a configuration with a valid owner (bench statement REACH_EACH).
- The first form Φ = (−t, r, Λ) was already false at n = 4 (#41). The data now say that no potential of this family
  whose maxima are the Φ′-maxima can work at n = 4 without a further term or a different order.
- Smallest known: n = 4, m = 8 for the form "no Φ′-maximum has a valid owner" (category N, this core). The
  weaker form "every Φ′-maximum has a valid owner" already fails at n = 4, m = 7 (pure core 53, one of three maxima;
  `results/k4_gap_hard_hunt.log`). No failure exists with n ≤ 3 (exhaustive) or at n = 4 with one 4-good agent
  (exhaustive). The pure n = 4 class was sampled, not searched exhaustively.

**Reproduce.**
```
python3 attempts/k4_gap_phi_prime.py            # the three implementations, both profiles (exit status 0 if all agree)
python3 k4/gap_bench.py --profile='{"sets": [[0,2,5,7],[1,4,6,7],[2,3,4,6],[3,5,6,7]], "vals": [[2,3,6,10],[3,2,6,10],[6,10,3,2],[8,4,5,2]], "m": 8}' --only=PHI_PRIME,REACH_EACH,BTCYC
python3 k4/gap_run.py results/k4_certs_4_pure.json.gz --sample=400000 --seed=44 --rec=0 --out=hunt.json.gz   # the hunt (~15 min on 4 CPUs)
```
