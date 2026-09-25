# Reduction (b): Theorem Z's argument at a fixed key with x protected (k = 4, f = 1)

Workstream `proof/k4-c4min-reduce` (`k4/c4min_reduce.md` §4.2). Approach: at a fixed key (g, x) of a profile with
f = 1, rerun the proof of Theorem Z′ (`k4/c4min_reduce.md` §2) on the configurations, with the constraint t = 0 first.
t = 0 means the pool alone does not threaten x. Maximize (−t, r′, Λ′) and expect Lemma P and Lemma R to go through.
Then Lemma C (`k4/c4min_reduce.md` §3) would handle x.

**Why it fails.** Pool improvements that would release one of x's goods into the pool and raise t are no longer moves.
So Lemma Z1's pool-optimality holds only for the moves that keep t = 0.
- A non-robust free agent y whose improvement is blocked this way can have its own lower goods in the pool. It is then
  threatened by every owner, and Lemma P's injectivity fails.
- If every owner threatens someone, no owner is free-valid.

Measured (`results/k4_red_n3.log`, `results/k4_red_n4.log`, `results/k4_red_n5.log`, counters `tmax_*`):
- every maximum of (−t, r′, Λ′) at every key has a free-valid owner at n ≤ 3 (17,603,288 maxima);
- it fails on 2 maxima in the second n = 4 sample and on 6 in the n = 5 sample of pure cores.

The failing profiles are completable at other keys, so the repair is a different frozen agent (`k4/c4min_reduce.md`
§5).

**Smallest failing configuration** (smallest n = 4, since n ≤ 3 has none; m = 11 is the first found, not claimed
smallest). Instance B1, core 214 of `results/k4_certs_4_pure.json.gz`:
- agents {0, 2, 7, 10}, {1, 5, 8, 10}, {3, 6, 9, 10}, {4, 7, 8, 9};
- values 0:4, 2:3, 7:2, 10:8 | 1:4, 5:5, 8:6, 10:8 | 3:3, 6:2, 9:4, 10:8 | 4:4, 7:8, 8:1, 9:6.

At the key (10, 1) (x = agent 1, flat: 8 < 4 + 5), one maximum of (−t, r′, Λ′) is:
- pairs {0, 2} (agent 0), {1, 9} (agent 2), {7, 8} (agent 3), pool {3, 4, 5, 6}.
- Agent 2 (top 10 = g) holds its top 9 of U_2 with x's good 1 as a filler. Its lower goods 3, 6 (3 + 2 > 4) are in the
  pool, so every owner threatens it.
- Swapping 1 for 3 would put 1 into the pool next to x's good 5, and 4 + 5 > 8 gives t = 1.
- No owner is free-valid. The keys (10, 0) and (10, 2) (big-top agents) have completable maxima.

Replay: `python3 attempts/k4_c4min_reduce_attempts.py` (log `results/k4_red_attempts.log`).
