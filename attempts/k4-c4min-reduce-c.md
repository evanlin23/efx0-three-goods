# Reduction (c): one role swap with a terminal (k = 4, f = 1)

Workstream `proof/k4-c4min-reduce` (`k4/c4min_reduce.md` §4.3). Approach: when the (r′, Λ′)-maximum at a key (g, x) has
no valid owner, take a terminal z of it (a free agent needing g). By Lemma T, z's top is g. Move to the key (g, z):
z freezes on g and x becomes free. Two variants:
- **narrow:** x takes an admissible pair inside L ∪ Q_z, everyone else keeps its pair; the result should be completable;
- **two-level:** every (r′, Λ′)-maximum at the key (g, z) should be completable.

**Why it fails.**
- The narrow swap fails on 24 of the 392 non-completable (r′, Λ′)-maxima of a 6,000-per-core n = 3 sample
  (`attempts/k4_c4min_reduce_rules.py`, `results/k4_red_rules.log`; the failures are printed in
  `results/k4_red_rules_ties.log`, all with m = 7). x's best lower good is held by a third agent, so a longer exchange
  cycle is needed. It succeeds on H★ (instance A2 of `attempts/k4-c4min-reduce-a.md`): at the key (7, 0), the maximum's
  terminal 1 freezes and x takes {0, 6}.
- The two-level rule holds for 424,168 of the 424,552 non-completable (r′, Λ′)-maxima with n ≤ 3
  (`results/k4_red_n3.log`, counters `swap_*`). It fails for 384, among them those of H★, where every key fails.

**What it shows.** Swapping the frozen agent is necessary but must be combined with optimizing the new key's
configuration under an x-aware potential, or with longer exchanges. `k4/c4min_reduce.md` §5 does both at once by
maximizing one potential over all keys.

**Smallest failing configurations.**
- Two-level rule: instance A2 of `attempts/k4-c4min-reduce-a.md` (H★; n = 3, m = 8, core 46 of
  `results/k4_certs_3.json.gz`). Every non-completable (r′, Λ′)-maximum there has two terminals, and their keys fail
  too.
- Narrow swap: instance **C1** (n = 3, m = 7, core 33 of `results/k4_certs_3.json.gz`): agents {0, 1, 2, 3},
  {2, 4, 5, 6}, {3, 4, 5, 6}, values 0:3, 1:2, 2:10, 3:6 | 2:8, 4:2, 5:5, 6:4 | 3:3, 4:6, 5:10, 6:8. At the key
  (2, 0) the (r′, Λ′)-maximum with pairs Q_1 = {4, 5}, Q_2 = {3, 6} and pool {0, 1} is not completable. Its only
  terminal is agent 1; x's goods in L ∪ Q_1 = {0, 1, 4, 5} are 0 and 1, and {0, 1} is not admissible for x, since its
  good 3 (with agent 2) is worth more. All 24 failures of the sample have n = 3, m = 7.

Replay: `python3 attempts/k4_c4min_reduce_attempts.py` (log `results/k4_red_attempts_v2.log`; the narrow swap is
checked by the Python implementation only, and the C tool confirms the profile's counters).
