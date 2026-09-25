# Reduction (c): one role swap with a terminal (k = 4, f = 1)

Workstream `proof/k4-c4min-reduce` (`k4/c4min_reduce.md` §4.3). Approach: when the (r′, Λ′)-maximum at a key (g, x) has
no valid owner, take a terminal z of it (a free agent needing g). By Lemma T, z's top is g. Move to the key (g, z):
z freezes on g and x becomes free. Two variants:
- **narrow:** x takes an admissible pair inside L ∪ Q_z, everyone else keeps its pair; the result should be completable;
- **two-level:** every (r′, Λ′)-maximum at the key (g, z) should be completable.

**Why it fails.**
- The narrow swap fails on 24 of the 392 non-completable (r′, Λ′)-maxima of a 6,000-per-core n = 3 sample
  (`attempts/k4_c4min_reduce_rules.py`, `results/k4_red_rules.log`). x's best lower good is held by a third agent, so a
  longer exchange cycle is needed.
- The two-level rule holds for 424,168 of the 424,552 non-completable (r′, Λ′)-maxima with n ≤ 3
  (`results/k4_red_n3.log`, counters `swap_*`). It fails for 384, all in the core H★ of `attempts/k4-c4min-reduce-a.md`,
  where every key fails.

**What it shows.** Swapping the frozen agent is necessary but must be combined with optimizing the new key's
configuration under an x-aware potential. `k4/c4min_reduce.md` §5 does both at once by maximizing one potential over
all keys.

**Smallest failing configuration.** Instance A2 of `attempts/k4-c4min-reduce-a.md` (n = 3, m = 8, core 46 of
`results/k4_certs_3.json.gz`). Every non-completable (r′, Λ′)-maximum there has two terminals, and their keys fail too.
Replay: `python3 attempts/k4_c4min_reduce_attempts.py` (log `results/k4_red_attempts.log`).
