# Reduction (a): remove the frozen agent, apply Theorem Z, reinsert (k = 4, f = 1)

Workstream `proof/k4-c4min-reduce` (`k4/c4min_reduce.md` §1–§4.1). Approach: on a strict profile with fewest frozen
agents f = 1 (`k4/c4min.md`), take a key (g, x): x frozen on its top g.
1. Remove x and g. The configurations at the key are the all-pairs allocations of I′ = I − x − g, and Theorem Z′
   (`k4/c4min_reduce.md` §2) gives a maximum of (r′, Λ′) with a free-valid owner.
2. Reinsert x with {g}, and hope that some free-valid owner does not threaten x.

**Why it fails.**
- **A fixed key can be hopeless.** Some keys have no completable configuration at all: 62,208 of the 14,259,424 keys of
  the f = 1 profiles with n ≤ 3 (`results/k4_red_n3.log`, `key_noncompletable`). Instance A1 below. x's private goods
  are worthless in I′, so nothing keeps them out of the pool. With ω = 1 one of them must go there, and every free-valid
  owner holds another good of x.
- **No rule for the key that looks only at x works with (r′, Λ′)** (`attempts/k4_c4min_reduce_rules.py`,
  `results/k4_red_rules.log`, `results/k4_red_rules_ties.log`; 6,000 random profiles per n = 3 core, 8,402 with f = 1).
  Pick the keys whose x maximizes a score, then require every (r′, Λ′)-maximum there to be completable. The first
  column counts a rule as failing on a profile if *any* of the keys tied for the best score fails (the script's
  count). The second counts the profiles on which the best key is unique and fails, so that no tie-break can rescue the
  rule (here these are exactly the profiles on which every tied key fails):

  | score of x | failures (any tied key) | failures (tie-independent) |
  |---|---|---|
  | level of its top | 241 | 88 |
  | fewest private goods | 239 | 19 |
  | a / v(U_x) | 215 | 130 |
  | a / v(U_x) minus the private share | 157 | 132 |
  | least value of private goods | 145 | 110 |
  | best (r′, Λ′)-maximum of I′ | 120 | 11 |

  Any rule at all fails on H★ below, where every key fails.

- **Even the best key fails with Theorem Z's potential.** Instance A2, the core H★ (every agent has top 7, is of type
  a > b + c, and has a private pair):
  - every agent can be the frozen one;
  - at each key the (r′, Λ′)-maximum is unique;
  - the free agents take their private pairs, both robust;
  - so the pool holds all three lower goods of x (t = 1), and every owner threatens x.
  
  128 profiles with n ≤ 3 have no key at which every (r′, Λ′)-maximum is completable, all in this core
  (`results/k4_red_hstar_cores.log`). As the maxima
  are unique, no tie-break after (r′, Λ′) helps. A completable configuration exists at every key, e.g. at key (7, 0):
  agent 1 holds {1, 6}, agent 2 holds {3, 5}, pool {0, 2, 4}, owner 2.

**What it shows.** Theorem Z's potential on I′ does not see where x's goods lie, and x's private goods are junk in I′.
Some x-aware term (t, as in #41's Φ) must come before Λ′. The key must be chosen together with the configuration:
`k4/c4min_reduce.md` §5 maximizes one potential over all keys.

**Smallest failing configurations** (both replayed by `k4/red_lib.py` and `k4/red.c`):
- **A1** (a hopeless key; smallest n = 3, and m = 2n = 6, ω = 1). Core 17 of `results/k4_certs_3.json.gz`: agents
  {0, 1, 4, 5}, {2, 3, 4, 5}, {2, 3, 4, 5}, values 0:4, 1:2, 4:7, 5:8 | 2:2, 3:3, 4:4, 5:8 | 2:3, 3:4, 4:6, 5:8. The
  key (5, 0) has no completable configuration; the keys (5, 1) and (5, 2) have one.
- **A2** (no key works with (r′, Λ′); smallest n = 3, and the only failing core with n ≤ 3, m = 8). Core 46 of
  `results/k4_certs_3.json.gz`: agents {0, 2, 6, 7}, {1, 4, 6, 7}, {3, 5, 6, 7}, values 0:3, 2:4, 6:2, 7:8 | 1:4, 4:3,
  6:2, 7:8 | 3:3, 5:4, 6:2, 7:8.

Replay: `python3 attempts/k4_c4min_reduce_attempts.py` (logs `results/k4_red_attempts.log` and, with instance C1 and
the checks added at review, `results/k4_red_attempts_v2.log`; "ALL CONFIRMED").
