# The exposed-frozen gap of C₄ᵐⁱⁿ: catalog, hard instances, lemma bench (compute/k4-gap)

EVIDENCE only (PROMPT.md §5 rule 3); ledger rows K4.GAP.*. This file maps the one case of conjecture C₄ᵐⁱⁿ that
Theorems Z and F of `k4/c4min.md` (PR #41) leave open, and describes a test bench for the lemmas proposed to close it.
Definitions are those of `k4/c4min.md` §1, §3.6 and §4, `k4/c4x.md` §1 (PR #36) and `k4/hall.md` §5 (PR #46).

## 0. The gap

Fix a strict profile of a k = 4 core. f is the fewest frozen agents over 𝒫, and ω = f − (2n − m). A *key* is the pair
(F, φ) of a min-frozen P ∈ 𝒫: its frozen agents and their one-good bases. 𝒩 = φ(F) is the needed set, and U_i = R_i ∖ 𝒩.
A configuration of a key gives every free agent a pair Q_y ⊆ M ∖ 𝒩, with Q_y ∩ U_y admissible; the rest is the pool L.
A frozen agent x is *exposed* if v_x(U_x) > v_x(φ(x)).

The profile is **in the gap** if f ≥ 1, ω ≥ 1 and every key has an exposed frozen agent. Frozen robustness depends
only on the key, so this is the same as "no configuration at the fewest frozen agents is frozen-robust". The other
profiles with ω ≥ 1 are covered by Theorem Z (f = 0) or Theorem F. Every profile with f = 1 is in the gap.

For each configuration the catalog records:
- **valid owners** (`k4/c4min.md` §1): a free o and a set C ⊆ X = Q_o ∪ L such that
  - X ∖ C contains an admissible set of o;
  - |C| is at most the number of frozen agents that o's bundle unfreezes;
  - no x ≠ o strongly envies X ∖ C while holding H_x.

  For each valid owner the catalog keeps the least |C|. A configuration is **simple** if some owner is valid with
  C = ∅: nothing is withheld and nothing is unfrozen.
- **Φ′** = (−t, r, Λ, −p) and **pool-optimality** (`k4/c4min.md` §3.1, §4).
- **Threat edges** o → x, with C = ∅.
- **The class of Lemma H7** (`k4/hall.md` §5) of each threatened frozen agent. The configuration corresponds to the
  pre-allocation of Lemma 1(a): B_y = Q_y ∩ U_y, with junk J_P = M ∖ 𝒩 ∖ ⋃ B_y. A big-top agent has four goods,
  holds its top a, and has a > b + c. The classes are:
  - **G**: x is big-top and R_x ∖ {a} ⊆ J_P.
  - **G1**: not G; o is a chain end of x (a free agent reached from x by need edges through frozen agents); x is
    big-top and R_x ∖ {a} ⊆ J_P ∪ B_o.
  - **L**: not G or G1; o is not a chain end, and the goods of R_x in X ∖ B_o are worth at most v_x(φ(x)), so the
    threat uses a good of B_o.
  - **O**: none of these. Lemma H7 says this cannot happen at a Pareto-maximum.
- **needers** of each φ(x).
- **threat multiplicity**: the number of owners that threaten a frozen agent.

## 1. Tools

- **`k4/gap.c`.** Written from the definitions; it shares no code with `k4/c4min.c`, `k4/hall.c` or `k4/c4x.c`. It
  enumerates 𝒫 (early exit when some P has no need), f, ω, the keys and the class. For every gap profile it enumerates
  every configuration of every key and tests every owner and every C. `-D` adds the removal-only deficit of every
  min-frozen P (`k4/c4x.md` §1) and compares "some P has deficit ≤ 0" with "some configuration has a valid owner"
  (Lemma 1 of `k4/c4min.md`). `-C` dumps every configuration as JSON.
- **`k4/gap_run.py`.** The driver over the certificate files (`check4.core_domains`: every strict balanced type,
  smallest integer representative). It runs every profile or a seeded sample per core, prints the counters with the
  command and the SHA-256 of gap.c, and writes the catalogs `results/k4_gap/*.json.gz`.
- **`k4/gap_model.py`.** A Python model of the same objects: Profile, Config, owners, Φ′, kinds, H7, and the moves of
  `k4/c4min.md` §4 (pool moves; one step along a cycle of the exchange digraph). It shares no code with gap.c.
- **`k4/gap_bench.py`.** The lemma bench (§4).
- **`k4/gap_hard.py`.** The smallest instances per hardness category (§3).

**Cross-checks.**
- Every class count equals #41's table (`k4/c4min.md` §4), computed by different code. The rows that match are n = 2,
  n = 3 and n = 4 with one 4-good agent, where both runs cover every profile.
- The deficit test and the configuration test agree on every gap profile of every run with `-D`: n ≤ 3, all 7,285,840
  profiles; n = 4 with one 4-good agent, all 44,388.
- gap.c and gap_model agree configuration by configuration on the key set, f, ω, Φ′, pool-optimality, the valid owners
  with their least |C|, the threat edges and the H7 classes: every n = 2 gap profile, and 2,971 n = 3 gap profiles
  (every 25th catalog record) (`results/k4_gap_selftest.log`).
- Every counterexample the bench reports is re-derived from scratch by gap_model (its own 𝒫, keys and configurations).

## 2. The catalog

Every class (`results/k4_gap_*.log`; the classes of the certificate files; samples are seeded, per core):

| class | profiles with ω ≥ 1 | Z (f = 0) | F | gap, f = 1 | gap, f ≥ 2 | configurations (with a valid owner) | Φ′-maxima | W | N, X | deficit mismatches | catalog `results/k4_gap/…json.gz` |
|---|---|---|---|---|---|---|---|---|---|---|---|
| n = 2, every profile | 105,120 | 103,824 | 0 | 1,296 | 0 | 8,496 (8,496) | 2,272 | 720 | 0 | 0 | gap_n2 (all) |
| n = 3, every profile | 119,640,516 | 112,040,608 | 315,364 | 7,284,544 | 0 | 138,471,840 (112,919,696) | 8,989,292 | 0 | 0 | 0 | gap_n3 (every 100th + hard) |
| n = 4, one 4-good agent, every profile | 102,434 | 31,104 | 26,942 | 28,478 | 15,910 | 1,439,336 (1,423,291) | 86,300 | 0 | 0 | 0 | gap_n4_1 (all) |
| n = 4, two, 4,000 per core | 166,150 | 122,027 | 7,959 | 32,912 | 3,252 | 1,634,284 (1,586,630) | 60,153 | 0 | 0 | — | gap_n4_2_s4000 (all) |
| n = 4, three, 4,000 per core | 414,292 | 349,138 | 6,793 | 55,338 | 3,023 | 3,790,656 (3,549,001) | 82,423 | 0 | 0 | — | gap_n4_3_s4000 (all) |
| n = 4, pure, 4,000 per core | 408,441 | 360,206 | 3,134 | 43,334 | 1,767 | 4,504,315 (3,919,786) | 57,319 | 1 | 0 | — | gap_n4_pure_s4000 (all) |
| n = 5, one, 100 per core | 898 | 100 | 251 | 216 | 331 | 57,945 (57,736) | 1,343 | 0 | 0 | — | gap_n5_1_s100 (all) |
| n = 5, two, 100 per core | 18,953 | 8,903 | 2,337 | 5,427 | 2,286 | 1,162,069 (1,152,957) | 15,356 | 0 | 0 | — | gap_n5_2_s100 (all) |
| n = 5, three, 100 per core | 104,461 | 67,788 | 5,483 | 25,622 | 5,568 | 6,539,357 (6,389,148) | 54,286 | 0 | 0 | — | gap_n5_3_s100 (all) |
| n = 5, four, 100 per core | 210,107 | 157,431 | 5,402 | 41,613 | 5,661 | 14,144,816 (13,449,830) | 71,439 | 0 | 0 | — | gap_n5_4_s100 (all) |
| n = 5, pure, 100 per core | 157,719 | 126,442 | 2,191 | 26,402 | 2,684 | 12,924,091 (11,724,026) | 39,838 | 0 | 0 | — | gap_n5_pure_s100 (all) |

The columns:
- **Z**, **F** and **gap**: the profiles covered by Theorem Z, by Theorem F, and neither.
- **W**, **N**, **X**: the categories of §3.
- **deficit mismatches**: gap profiles where "some min-frozen P has deficit ≤ 0" and "some configuration has a valid
  owner" differ (runs with `-D`).

Every gap profile has a completable configuration, and in all but the 721 profiles of category W some Φ′-maximum has a
valid owner with C = ∅. At the Φ′-maxima:

| class | Φ′-maxima not pool-optimal | with t > 0 | with a frozen agent threatened by two owners | H7 at the maxima: G / G1 / L / O | H7, all configurations: G / G1 / L / O | exposed (key, agent): 3-good / 4-good / big-top |
|---|---|---|---|---|---|---|
| n = 2, every profile | 64 | 0 | 0 | 0 / 1,120 / 0 / 0 | 1,536 / 4,080 / 0 / 0 | 0 / 0 / 2,592 |
| n = 3, every profile | 4,672 | 0 | 0 | 0 / 163,788 / 3,988,852 / 0 | 11,609,424 / 8,823,696 / 40,521,600 / 13,618,752 | 80,884 / 5,873,760 / 8,302,188 |
| n = 4, one 4-good agent, every profile | 0 | 0 | 0 | 0 / 0 / 37,642 / 0 | 948 / 1,288 / 628,947 / 118,947 | 93,198 / 17,194 / 12,734 |
| n = 4, two, 4,000 per core | 0 | 0 | 89 | 36 / 107 / 22,722 / 0 | 22,950 / 8,748 / 561,649 / 141,717 | 38,298 / 19,414 / 17,007 |
| n = 4, three, 4,000 per core | 27 | 0 | 375 | 52 / 474 / 34,601 / 0 | 153,621 / 65,382 / 1,238,781 / 387,760 | 29,609 / 48,127 / 40,055 |
| n = 4, pure, 4,000 per core | 64 | 0 | 645 | 19 / 874 / 26,856 / 0 | 421,114 / 151,324 / 1,408,701 / 561,006 | 0 / 49,968 / 42,865 |
| n = 5, one, 100 per core | 0 | 0 | 1 | 0 / 0 / 468 / 0 | 32 / 0 / 23,670 / 4,068 | 1,649 / 237 / 150 |
| n = 5, two, 100 per core | 0 | 0 | 24 | 0 / 8 / 4,436 / 0 | 4,722 / 2,218 / 361,139 / 78,074 | 12,792 / 4,874 / 3,236 |
| n = 5, three, 100 per core | 0 | 0 | 161 | 39 / 59 / 16,098 / 0 | 106,018 / 31,057 / 1,891,640 / 510,133 | 30,268 / 26,595 / 16,998 |
| n = 5, four, 100 per core | 11 | 0 | 423 | 12 / 180 / 22,683 / 0 | 500,043 / 156,279 / 3,960,586 / 1,278,137 | 21,500 / 51,525 / 33,395 |
| n = 5, pure, 100 per core | 3 | 0 | 411 | 22 / 207 / 13,981 / 0 | 871,679 / 236,641 / 3,552,596 / 1,471,037 | 0 / 38,266 / 26,332 |

What the tables say:
- **t = 0 at every Φ′-maximum.** Roadmap step (i), second half.
- **Pool-optimality at a maximum fails**, rarely: n = 2, 3, 4, 5. Roadmap step (i), first half; see §4.
- **Frozen agents threatened by two owners** occur at maxima from n = 4 on. Roadmap step (iv).
- **Every threat on a frozen agent at a Φ′-maximum** is of class G, G1 or L. Class O occurs only away from the
  maxima.
- **At n = 3 the exposed frozen agents are almost all 4-good** (big-top or not). At n = 4 with one 4-good agent they are
  mostly 3-good.

**The records.** Each catalog record is one gap profile. It has:
- the core and the values;
- f, ω and the keys (−1 marks a free agent);
- the numbers of configurations, completable configurations and simple configurations;
- Φ′ at the maximum, and the maxima's counts: completable, simple, pool-optimal, t = 0, and threatened by two owners;
- the largest threat multiplicity, over all configurations and at the maxima;
- the H7 class counts;
- the category;
- the deficit result (`def`: 1 or 0, −1 if not computed);
- one Φ′-maximum in full (`ex`): key, pairs, pool, owners with a least C, threat edges with their H7 class, and the
  needers of each φ(x).

The bench (§4) rebuilds every configuration of any record. The n = 3 catalog keeps every 100th gap profile and every
hard one: 74,256 of 7,284,544. `k4/gap_run.py` regenerates the rest in 91 s.

## 3. The smallest hard instances

(filled in below)

## 4. The lemma bench

(filled in below)

## Reproduce
```
python3 k4/gap_run.py results/k4_certs_2.json.gz -D --rec=1 --out=results/k4_gap/gap_n2.json.gz     # seconds
python3 k4/gap_run.py results/k4_certs_3.json.gz -D --rec=100 --out=results/k4_gap/gap_n3.json.gz   # 91 s on 4 CPUs
python3 k4/gap_run.py results/k4_certs_4_n4_1.json.gz -D --rec=1 --out=results/k4_gap/gap_n4_1.json.gz
python3 k4/gap_run.py results/k4_certs_4_n4_2.json.gz --sample=4000 --seed=4 --rec=1 --out=results/k4_gap/gap_n4_2_s4000.json.gz
python3 k4/gap_bench.py --selftest --catalog=results/k4_gap/gap_n2.json.gz
python3 k4/gap_bench.py --catalog=results/k4_gap/gap_n2.json.gz,results/k4_gap/gap_n3.json.gz
python3 k4/gap_hard.py results/k4_gap/*.json.gz --show=2
```
Every log under `results/k4_gap_*.log` starts with its command.
