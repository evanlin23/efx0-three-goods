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
  - **G**: the plain test of `k4/hall.md` Lemma H7 as revised in #46. Two or more goods of R_x lie in J_P, and
    together they are worth more to x than φ(x).
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

**The hunt** (`results/k4_gap_hunt_*.log`). Larger runs that keep only the hard records, the ones of categories W, N
and X or with a flagged maximum (`results/k4_gap/hunt_*.json.gz`):

| class | profiles | ω ≥ 1 | gap (f = 1 / f ≥ 2) | W | N | X | Φ′-maxima | not pool-optimal | two owners on a frozen agent |
|---|---|---|---|---|---|---|---|---|---|
| n = 4, two 4-good agents, every profile | 724,847,616 | 54,488,316 | 10,723,372 / 1,543,950 | 0 | 0 | 0 | 19,989,556 | 0 | 33,756 |
| n = 4, three, 400,000 per core | 135,600,000 | 41,409,949 | 5,516,567 / 310,035 | 2 | 0 | 0 | 8,213,208 | 1,624 | 41,121 |
| n = 4, pure, 400,000 per core | 87,600,000 | 40,809,834 | 4,307,373 / 176,485 | 113 | **2** | 0 | 5,690,458 | 8,408 | 68,464 |
| n = 5, three, 2,000 per core | 19,722,000 | 2,085,678 | 512,222 / 108,073 | 0 | 0 | 0 | 1,080,864 | 44 | 3,187 |
| n = 5, four, 2,000 per core | 19,692,000 | 4,195,843 | 829,179 / 114,355 | 0 | 0 | 0 | 1,428,110 | 142 | 8,222 |
| n = 5, pure, 2,000 per core | 9,348,000 | 3,155,718 | 527,194 / 53,342 | 0 | 0 | 0 | 794,588 | 315 | 8,536 |

- **Φ′ fails.** In 33 hunt profiles some Φ′-maximum has no valid owner (the counter `phibad`): 30 pure and 3 with three
  4-good agents, with 55 such maxima in all (`results/k4_gap_bench_hard_hunt.log`, re-derived by gap_model). In 2 of
  them, the category-N profiles, no Φ′-maximum has a valid owner (`attempts/k4-gap-phi-prime.md`, confirmed by gap.c,
  gap_model and #41's own `k4/c4min_cfg.py`). Every other run has `phibad` = 0, including every profile with n ≤ 3 and
  every profile at n = 4 with one or two 4-good agents.
- **C₄ᵐⁱⁿ in configuration form holds.** No profile anywhere is in category X.
- **The records.** `results/k4_gap/hard_hunt.json.gz` collects the 144 hunt profiles of categories W, N or PHI.

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

Categories of a gap profile (`k4/gap.c`, `k4/gap_hard.py`). A Φ′-maximum is *simple* if it has a valid owner with
C = ∅: nothing is withheld and nothing unfrozen.

| category | meaning |
|---|---|
| S | some Φ′-maximum is simple |
| W | none is simple, but some Φ′-maximum has a valid owner (it must withhold goods, which needs unfreezing) |
| N | no Φ′-maximum has a valid owner, but some configuration has one |
| X | no configuration has a valid owner (C₄ᵐⁱⁿ fails in configuration form) |
| PHI | some Φ′-maximum has no valid owner: a counterexample to Conjecture Φ′ (N is the case where all do) |
| T2 | some Φ′-maximum has a frozen agent threatened by two owners |
| NPO | some Φ′-maximum is not pool-optimal |
| F2 | f ≥ 2 |

The smallest found, by n, then m, then the number of configurations (full lists with every Φ′-maximum re-derived by
gap_model: `results/k4_gap_hard_base.log` for the catalogs, `results/k4_gap_hard_hunt.log` for the hunt):
- **X: none anywhere.**
- **PHI and N: n = 4, m = 8.** This is pure core 104 (`attempts/k4-gap-phi-prime.md`), found by the hunt.
  - The unique Φ′-maximum has two exposed frozen agents, and each owner is blocked by one local threat.
  - Every profile with n ≤ 3, and every profile of n = 4 with one or two 4-good agents, is free of PHI (exhaustive).
- **W: n = 2, m = 5**, with 720 profiles at n = 2 (#41 found them too). The smallest has sets {0, 2, 3, 4},
  {1, 2, 3, 4} and values 0:2, 2:3, 3:6, 4:10 and 1:2, 2:3, 3:6, 4:10.
  - Both Φ′-maxima have one frozen agent on good 4, which only the owner needs.
  - The owner completes only by withholding its partner's private good into the unfrozen agent's slot.
  - For n ≥ 3 the smallest W is n = 4: pure core 179 (m = 10, f = 2) in the sample, and 113 pure and 2 three-4-good
    profiles in the hunt. So #41's `-U0` observation ("no unfreezing at n ≥ 3") fails at n = 4.
- **T2: n = 4, m = 8**, core 204 of `k4_certs_4_n4_2`. The values are 0:3, 2:4, 5:6, 6:8 / 1:5, 5:4, 6:8, 7:6 /
  3:2, 5:3, 7:4 / 4:2, 6:3, 7:4.
  - Frozen agent 1 (on good 6) is threatened by owners 2 and 3, both class L.
  - The maximum is still simple, with owner 0.
  - No T2 exists at n ≤ 3.
- **NPO: n = 2, m = 6.** The sets are {0, 1, 4, 5} and {2, 3, 4, 5}, with values 3, 6, 2, 10 for each agent.
  - The maximum keeps good 4 out of the pool. Agent 0's pool improvement would put 4 in the pool and raise t.
- **F2 (the gap with f ≥ 2): n = 4, m = 7**, core 93 of `k4_certs_4_n4_2`. No gap profile with n ≤ 3 has f ≥ 2.
- **BT counterexamples.** These are Pareto-maximal configurations without a valid owner and without a frozen big-top
  agent:
  - #52's pure n = 4, m = 7 profile. It is in the gap with f = 2, and both implementations confirm it
    (`results/k4_gap_bt4.log`).
  - A second one found here: n = 5, m = 10, sets {0, 2, 4, 8}, {1, 3, 7, 9}, {4, 6, 9}, {5, 6, 7, 9}, {5, 8, 9},
    values 2, 4, 5, 8 / 3, 2, 6, 10 / 2, 3, 4 / 8, 6, 4, 3 / 4, 3, 2 (`results/k4_gap_bt5.log`). Its frozen agents
    are the 3-good agent 2 (on 9) and agent 3 (on 5). Two owners are blocked by class-L threats, and the third owner's
    threat falls on a free agent.

  In both, exchange cycles alone never reach a configuration with a valid owner, and a downgrade swap does.
- **Configurations that no needed-set-preserving move improves: n = 4, m = 8**, sets {0, 2, 4, 5}, {1, 3, 6, 7},
  {4, 5, 6, 7}, {5, 6, 7}, values 6, 3, 2, 10 / 2, 3, 6, 10 / 4, 6, 3, 8 / 2, 4, 3.
  - The configuration has frozen 0 on 5, frozen 1 on 7, Q₂ = {0, 4}, Q₃ = {1, 6} and L = {2, 3}. It has no valid owner.
  - Every configuration of larger Φ′ has the needed set {6, 7} instead of {5, 7}. So no pool, cycle or two-agent move
    and no downgrade swap raises Φ′ (§4, SAME_N).

## 4. The lemma bench

`k4/gap_bench.py` runs a predicate over the catalog profiles. For each profile it rebuilds every configuration with
`gap.c -C`. The configuration objects are those of `k4/gap_model.py`, so every property is computed by the Python
model. Each reported counterexample is then re-derived from scratch by gap_model, with its own 𝒫, keys and
configurations.
```
import sys; sys.path.insert(0, 'k4'); import gap_bench as gb
def my_lemma(prof, c):                 # prof: gap_model.Profile, c: gap_model.Config
    if c.completable: return None      # None: hypothesis not met, skipped
    return any(c2.phi > c.phi for _, _, c2 in c.pool_moves())      # True holds, False counterexample
res = gb.check(my_lemma, scope='all', catalogs=['results/k4_gap/gap_n3.json.gz'])
print(res.summary()); res.counterexamples[0]          # (prof, config, detail), smallest first
```

**Scopes:**
- `all`: every configuration;
- `max`: the Φ′-maxima;
- `max0`: the maxima of the first form Φ = (−t, r, Λ);
- `noncompl`: the configurations without a valid owner;
- `pareto`: the configurations that are Pareto-maximal (values of the holdings) among all configurations of the
  profile;
- `profile`: the predicate gets (prof, cfgs) once per profile;
- a callable (prof, cfgs) → subset.

**What a configuration offers:**
- structure and values: `.key`, `.frozen`, `.free`, `.N`, `.Q`, `.L`, `.H(i)`, `.hv(i)`, `.U(i)`, `.needs(i)`,
  `.needers(g)`;
- owners: `.threatens(o, x, C)`, `.owner(o)` (the least |C|), `.owners`, `.completable`, `.simple`, and
  `.p_completable` (the pre-allocation of Lemma 1(a) is removal-only completable; weaker, since it lets the owner
  withhold into any free slot);
- potentials: `.t`, `.r`, `.Lam`, `.p`, `.phi`, `.phi0`, `.pool_optimal`;
- classification: `.kind(i)` (robust, T, D, R, frozen-exposed, frozen-robust), `.exposed`, `.bigtop(x)`,
  `.threat_edges`, `.need_edges`, `.chain_ends(x)`, `.h7(x, o)`, `.mult(x)`;
- moves:
  - `.pool_moves()`;
  - `.cycle_moves(general, keep)`: one step along a cycle of the exchange digraph. The default gives best pairs with
    the receivers in every order; `general` allows any admissible pairs; `keep` lets receivers keep part of their pair;
  - `.two_agent_moves()`: re-partitions of two free agents' pairs and the pool;
  - `.downgrade_swaps()`: #52's move;
  - `.pool_closure()`.

**CLI.** `python3 k4/gap_bench.py [--catalog=…] [--only=…] [--every=E]` runs the seeded statements; `--list` lists them,
`--profile='{"sets": …, "vals": …}'` runs them on one profile, and `--selftest` compares gap.c with gap_model.

**The seeded statements** (the candidate steps of `k4/c4min.md` §4 (#41) and of `k4/hall.md`, `k4/hall_bt.md` (#46,
#52)). The table after this list gives the results.
- **PHI_PRIME**: Conjecture Φ′, every Φ′-maximum has a valid owner.
- **PHI_FIRST**: the same for Φ = (−t, r, Λ).
- **MAX_SIMPLE**: #41's `-U0` observation, some Φ′-maximum has a valid owner with C = ∅.
- **Roadmap step (i)**, and step (i) as a local lemma:
  - **I_POOLOPT**: every Φ′-maximum is pool-optimal;
  - **I_T0**: every Φ′-maximum has t = 0;
  - **I_POOL_LOCAL**, **I_T_LOCAL**: a configuration without a valid owner that is not pool-optimal (resp. has t > 0)
    has a Φ′-raising pool or cycle move.
- **The f = 1 roadmap.** Its setting is f = 1, the frozen x 3-good, no valid owner, pool-optimal, t = 0.
  - **SIGMA_INJ**: every agent is threatened by at most one owner.
  - **II_T0**, **II_PHI**: with x threatened, and once no cycle move avoiding x raises Φ′, some cycle move through x
    (best pairs or any pairs, e.g. the plain rotation) leaves t = 0, resp. raises Φ′.
  - **III_NO_R**: the threat path into x has no agent of kind (R).
- **Roadmap step (iv)**: at Φ′-maxima (**IV_MAX**), resp. in the proof's setting (**IV_SETTING**), a frozen agent is
  threatened by at most one owner.
- **The local improvement lemma**: every configuration without a valid owner has a Φ′-raising move. The catalogues:
  - **LOCAL**: pool moves and cycle moves;
  - **LOCAL_EXT**: also any-pair cycle moves and two-agent re-partitions;
  - **LOCAL_CLOSURE**: also a cycle move followed by the pool closure;
  - **LOCAL_ALL**: also #52's downgrade swaps.
- **SAME_N**: at every configuration without a valid owner, some configuration with the same needed set has larger Φ′.
  Every catalogue that keeps the needed set needs this.
- **#52**:
  - **BTCYC**: at a Pareto-maximal configuration without a valid owner that has an exposed frozen big-top agent, some
    cycle through it (any pairs, receivers may keep part) gives a removal-only completable pre-allocation.
  - **REACH_EACH** (**REACH_EACH_CYC**): from each Pareto-maximal configuration without a valid owner, cycles and
    downgrade swaps (cycles alone) reach a configuration with a valid owner or a completable pre-allocation.
  - **REACH**: the coordinator's form, from some Pareto-maximum.
- **#46**:
  - **BT**: a Pareto-maximal configuration without a valid owner has a frozen big-top agent;
  - **H7**: at Pareto-maximal configurations every threat on a frozen agent is of class G, G1 or L.

**Results** (`results/k4_gap_bench_n23.log`, `_n4.log`, `_n5.log`, `_hard_hunt.log`). The columns are:
- all n = 2 profiles plus the n = 3 catalog (75,552 profiles);
- every 5th record of the n = 4 catalogs (36,803);
- every 10th of the n = 5 catalogs (11,581);
- the 144 hunt profiles of categories W, N or PHI (`results/k4_gap/hard_hunt.json.gz`).

Each entry counts the cases the statement's hypothesis selects: configurations, maxima or profiles.

| statement | n ≤ 3 | n = 4 (every 5th) | n = 5 (every 10th) | hard hunt profiles |
|---|---|---|---|---|
| PHI_PRIME | holds (97,146) | holds (57,340) | holds (18,022) | **fails** (55 of 277) |
| PHI_FIRST | holds (106,782) | **fails** (2 of 75,036) | holds (24,643) | **fails** (67 of 311) |
| MAX_SIMPLE | **fails** (720 of 75,552) | holds (36,803) | holds (11,581) | **fails** (117 of 144) |
| I_POOLOPT | **fails** (4,736 of 97,146) | **fails** (23 of 57,340) | **fails** (11 of 18,022) | **fails** (30 of 277) |
| I_T0 | holds (97,146) | holds (57,340) | holds (18,022) | holds (277) |
| I_POOL_LOCAL | **fails** (488 of 304,315) | **fails** (102 of 176,128) | **fails** (31 of 201,505) | **fails** (131 of 4,928) |
| I_T_LOCAL | **fails** (384 of 45,699) | holds (32,238) | holds (38,072) | holds (2,958) |
| SIGMA_INJ | holds (11) | holds (156) | holds (6) | — (no case) |
| II_T0 | holds (8) | holds (18) | holds (1) | — (no case) |
| II_PHI | holds (8) | holds (18) | holds (1) | — (no case) |
| III_NO_R | holds (11) | **fails** (5 of 154) | holds (6) | — (no case) |
| IV_MAX | holds (97,146) | **fails** (225 of 57,340) | **fails** (83 of 18,022) | holds (277) |
| IV_SETTING | **fails** (1,927 of 11,427) | **fails** (211 of 1,158) | **fails** (58 of 130) | holds (134) |
| LOCAL | **fails** (891 of 320,282) | **fails** (109 of 179,770) | **fails** (33 of 204,278) | **fails** (198 of 5,160) |
| LOCAL_EXT | **fails** (4 of 320,282) | **fails** (7 of 179,770) | holds (204,278) | **fails** (60 of 5,160) |
| LOCAL_CLOSURE | holds (320,282) | **fails** (7 of 179,770) | holds (204,278) | **fails** (60 of 5,160) |
| LOCAL_ALL | holds (320,282) | **fails** (7 of 179,770) | holds (204,278) | **fails** (55 of 5,160) |
| SAME_N | holds (320,282) | **fails** (7 of 179,770) | holds (204,278) | **fails** (55 of 5,160) |
| BTCYC | holds (5,139) | holds (711) | holds (158) | **fails** (1 of 185) |
| REACH | holds (75,552) | holds (36,803) | holds (11,581) | holds (144) |
| REACH_CYC | holds (128) | — (no case) | — (no case) | — (no case) |
| REACH_EACH | holds (5,139) | holds (711) | holds (159) | holds (186) |
| REACH_EACH_CYC | holds (5,139) | holds (711) | holds (159) | **fails** (2 of 186) |
| BT | holds (5,139) | holds (711) | **fails** (1 of 159) | **fails** (1 of 186) |
| H7 | holds (92,682) | holds (88,449) | holds (35,811) | holds (767) |

What the table says:
- **Only existence and reachability survive everywhere.**
  - C₄ᵐⁱⁿ in configuration form (no category X) holds everywhere.
  - REACH_EACH holds everywhere: from each Pareto-maximal configuration without a valid owner, exchange cycles and
    downgrade swaps reach one with a valid owner or a completable pre-allocation.
  - Every potential-maximum form fails from n = 4 on: Φ′ fails, and Φ already failed.
  - Every local-improvement catalogue fails at n = 4. LOCAL_ALL, the largest (with downgrade swaps), fails exactly
    where SAME_N fails. So there no move that keeps the needed set can raise Φ′, and the next catalogue needs moves that
    change the needed set.
- **The f = 1 roadmap holds wherever its setting occurs**, but that setting is rare (1 to 156 cases).
  - SIGMA_INJ and (ii), tested in its own setting, hold.
  - (iii) fails at n = 4 (5 cases).
  - (iv) fails from n = 4 at the maxima and from n = 3 in the proof's setting.
- **Roadmap step (i).** t = 0 holds at every maximum. Pool-optimality fails at every n, rarely, and its local forms
  fail too.
- **#46 and #52.**
  - H7's trichotomy holds everywhere.
  - BT fails at n = 4 (#52's instance, and one hunt profile) and at n = 5 (`results/k4_gap_bt5.log`).
  - BTCYC fails at n = 4 (`attempts/k4-gap-btcyc.md`).

## 5. The instance suite (for reuse)

`results/k4_gap/instances_v1.json` is the versioned suite of every hard instance found here and in #46/#52. It is
written once by `k4/gap_instances.py` and never edited; a new version gets a new file. It contains:
- #52's instance files `k4/hall_instances/{bt4,local3,cyc6}.inst`;
- the named counterexamples of this workstream: the two Φ′ profiles, the BTCYC profile, the n = 5 BT profile and the
  SAME_N configuration;
- the two smallest instances per n of every category of §3 (from the final catalogs and the hunt).

Each instance has n, m, the goods and values of every agent, tags, its provenance (file, core position, type indices,
run) and, where there is one, the configuration it is about (key, pairs).

The entry point evaluates any predicate on every instance:
```
import sys; sys.path.insert(0, 'k4'); import gap_bench as gb
res = gb.check_instances(lambda prof, c: <predicate>, scope='pareto')   # or 'all', 'max', 'noncompl', 'profile', ...
python3 k4/gap_bench.py --instances [--only=BT,BTCYC]                   # the seeded statements on the suite
```
For every instance, gap.c and gap_model first build the configurations independently and must agree on the class, f,
ω, the keys, and every configuration's Φ′, pool-optimality, owners (least |C|), threat edges and H7 classes. The result
lists per instance: the mismatches (0 on every instance), the cases tested and skipped, the failing configurations, and
the outcome on the highlighted configuration. `results/k4_gap_instances_v1.log` has every seeded statement on the
suite.

## Reproduce
```
python3 k4/gap_run.py results/k4_certs_2.json.gz -D --rec=1 --out=results/k4_gap/gap_n2.json.gz     # seconds
python3 k4/gap_run.py results/k4_certs_3.json.gz -D --rec=100 --out=results/k4_gap/gap_n3.json.gz   # 91 s on 4 CPUs
python3 k4/gap_run.py results/k4_certs_4_n4_1.json.gz -D --rec=1 --out=results/k4_gap/gap_n4_1.json.gz
python3 k4/gap_run.py results/k4_certs_4_n4_2.json.gz --sample=4000 --seed=4 --rec=1 --out=results/k4_gap/gap_n4_2_s4000.json.gz
python3 k4/gap_bench.py --selftest --catalog=results/k4_gap/gap_n2.json.gz
python3 k4/gap_bench.py --catalog=results/k4_gap/gap_n2.json.gz,results/k4_gap/gap_n3.json.gz
python3 k4/gap_hard.py results/k4_gap/gap_*.json.gz --show=2                                     # section 3
python3 k4/gap_run.py results/k4_certs_4_pure.json.gz --sample=400000 --seed=44 --rec=0 --out=results/k4_gap/hunt_n4_pure_s400k.json.gz
python3 k4/gap_run.py results/k4_certs_4_n4_2.json.gz --rec=0 --out=results/k4_gap/hunt_n4_2_all.json.gz   # 13 min on 4 CPUs
python3 k4/gap_instances.py; python3 k4/gap_bench.py --instances                                  # section 5
python3 attempts/k4_gap_phi_prime.py; python3 attempts/k4_gap_btcyc.py                            # the refutations
```
Every log under `results/k4_gap_*.log` starts with its command.
