# k = 4: CEGAR counterexample search for TARGET₄ (workstream proof/k4-hunt)

Angle: settle TARGET₄ negatively if it is false, by a complete search per core instead of random or adversarial
profiles. For a fixed k = 4 core H, decide whether some strict balanced type profile (equivalently, by K4.OT and
K4.MC0(c), some valuation with these relevant sets) admits **no** complete EFX₀ allocation. Status of everything here:
see "Results" (each claim names its artifact; nothing in LEDGER.md is changed by this workstream).

## Summary (burst 1)

- **No counterexample.** Every core searched has an EFX₀ allocation under every strict profile of its (possibly cut)
  domains. Nothing here is random testing: each "certified" core is a complete search with a certificate checked by an
  independent implementation.
- **K4.MC7 without the literature** (§3.1): the 6 graphical all-P4 cores (n = 6, m = 15, 288⁶ profiles each) are
  certified directly in 1.6–7 s each; K4.MC7 had left them to the multigraph theorem.
- **A complete per-core search that reaches n = 8** (§1): the ordinal outer encoding (comparison bits) is ~100× faster
  than the DFS scanners on dense n = 6 cores; a glued GM4 core with n = 8, m = 12, β = 13 (288⁸ ≈ 4.8·10¹⁹ profiles) is
  certified in 409 s (§3.3).
- **n = 6** (§3.2), both independently checked:
  - every connected core with n = 6, m = 10 and exactly two 4-good agents (28,502) is certified under every strict
    profile; with K4.MC7 and Mahara's theorem, **every core with n = 6 and at most two 4-good agents has an EFX₀
    allocation**;
  - all 30,337 minimal-counterexample candidates with n = 6 and β = 5 (K4.MC2/MC3/MC5 cuts) are certified: **a minimal
    counterexample with n = 6 has β ≥ 6** (and at least three 4-good agents).
  - The rest of n = 6 is 366,743 candidates (β = 6–9, m ≥ 10), sampled in §3.4.
- **Patterns** (§4): certificate size as a hardness measure; agents with two private goods and goods of very high
  degree make cores easier; the hardest are all-P4/Q4 cores and cores with twin agents.

## 1. Method (`k4/hunt/cegar.py`)

2QBF-style CEGAR, "∃ profile ∀ allocation: not EFX₀":
- **outer SAT** (CaDiCaL): find a profile under which every allocation found so far violates EFX₀;
- **inner SAT** (`search4.Core.inner(None, None)`: full EFX₀, no shape limit, type activation literals): find an
  EFX₀ allocation for that profile;
- repeat until the outer is UNSAT (the core is **certified for every profile**) or the inner is UNSAT (a
  counterexample candidate, to be re-checked by two independent encodings).

The new ingredient is the **ordinal outer encoding**. Agent i is unsafe in X iff some maximal threat set T of X
(T = X_j ∩ R_i if X_j holds a good outside R_i; else (X_j ∩ R_i) ∖ h for h ∈ X_j, |X_j| ≥ 2) satisfies
v_i(T) > v_i(X_i ∩ R_i). Each such comparison is one Boolean b(i, O, T), defined from the one-hot type variables
(b ⇔ OR of the types with v(T) > v(O)). An allocation then adds the short clause OR_i OR_T b(i, O_i, T)
(typically 10–30 literals), and the solver's learned clauses are statements about comparisons, which generalise across
types. The DFS scanners of `k4/search4.py` / `k4/frontier/scan2.c` walk the product of the type domains instead.
Measured on the same cores (n = 6, m = 10, model ANY, both full EFX₀):

| core | scan2 CEGAR | ordinal CEGAR |
|---|---|---|
| [[0,2,4,5],[1,3,6,7],[2,4,6,8],[3,5,7,9],[6,8,9],[7,8,9]] (four 4-good agents) | 408 s (404 s scanning) | 3.2 s |
| [[0,2,6,8],[1,5,7,9],[3,6,7,9],[4,5,8,9],[4,7,8,9],[5,6,8,9]] (six 4-good agents) | 93 s | 6.7 s |

Automorphism images of each allocation are added as clauses too (sound for any allocation; the certificate stores
every allocation whose clause was added). The inner and outer encodings are cross-checked on every proposal (the
allocation found must be safe, by the outer's threat sets, for the proposed types; an assertion).

## 2. Checking (`k4/hunt/check.py`)

Written separately from `cegar.py` and `search4.py`: its own type enumeration ([1,16]^d keyed by the signs of
v(A) − v(B) over disjoint nonempty A, B; 6 and 288 types), the raw definition v_i(X_i) ≥ v_i(X_j) − v_i(h) for every
j ≠ i, h ∈ X_j, and two coverage engines: `k4/check4_fast.py`'s C loop fed with these safety rows (default), and a
one-hot SAT encoding solved by Glucose 4 (`--engine=sat`, or `--sat-sample=K` on K random cores). For a whole class
it checks completeness by orbit counting against `check4.labeled_count` and pairwise non-isomorphism.

## 3. Runs and results

### 3.1 The six graphical all-P4 cores of K4.MC7: certified directly (no literature)

K4.MC7 (`k4/MINCEX.md` §8) proves TARGET₄ for β ≤ 4 *provided* the 6 graphical all-P4 cores with n = 6, m = 15
(288⁶ ≈ 5.7·10¹⁴ profiles each) have an EFX₀ allocation under every strict profile; it covered them by the multigraph
theorem of Afshinmehr et al., since the scan2 CEGAR ran an hour on one without finishing. The ordinal CEGAR
certifies all six, every strict profile, full EFX₀:

| core (order of `k4/MINCEX.md` §8) | time | allocations found | clauses (with automorphism images) | automorphisms |
|---|---|---|---|---|
| MC7-1 | 3.0 s | 118 | 770 | 8 |
| MC7-2 | 7.0 s | 69 | 2,250 | 48 |
| MC7-3 | 2.2 s | 68 | 1,568 | 32 |
| MC7-4 (prism) | 2.8 s | 64 | 768 | 12 |
| MC7-5 (K₃,₃) | 1.6 s | 11 | 792 | 72 |
| MC7-6 | 3.5 s | 113 | 1,340 | 16 |

Certificate `results/k4_hunt/named_mc7.json.gz` (log `results/k4_hunt/named_mc7.log`); independent check
`results/k4_hunt/check_named_mc7.log` (`check.py --engine=sat2`: own types, raw definition, Glucose; 6/6 covered).
Two independent encodings agree on the UNSAT (CaDiCaL on comparison bits; Glucose on raw unsafe sets). check4_fast's
DFS loop, fed with the same rows, did not finish within ~20 min on the first core (the same wall as before).
**So K4.MC7 holds without the multigraph theorem: TARGET₄ for β ≤ 4 rests only on the repository's own
certificates** (for the coordinator to integrate; the ledger is not edited here). Not checked: the D2 shape (not
needed for TARGET₄; the allocations are arbitrary EFX₀ allocations).

### 3.2 n = 6: every minimal-counterexample candidate (in progress)

Why n = 6 first: a minimal counterexample to TARGET₄ is a connected k = 4 core with strict types (K4.MC0), β ≥ 5
(K4.MC7, now without the literature: §3.1), n ≥ 6, and if n = 6 at least two 4-good agents (K4.R5*, K4.R6a). At
n = 6, β = 19 − m + (n₄ − 6) + … reduces to m = 8 + n₄ − (β − 5) − … ; concretely, for β = 5 the classes are
m = 9 + (n₄ − 1): (n₄, m) = (1, 9), (2, 10), (3, 11), (4, 12), (5, 13), (6, 14).

Two complementary runs:
- **the whole class n = 6, m = 10, n₄ = 2** (28,502 cores, every strict profile, no K4.MC restriction): `run.py 6 10
  --n4=2`. Together with K4.MC7 (β ≤ 4 covers n₄ = 2, m ≥ 11) and Mahara (m ≤ 9), this settles every core with n = 6
  and exactly two 4-good agents.
- **the minimal-counterexample candidates** (`mc_n.py 6`: `k4/mincex_shapes.py`'s generator restricted to n = 6,
  every β ≥ 5, with K4.MC2, K4.MC3 and the K4.MC5 domain cuts), searched by `run_mc.py` with the cut domains and
  checked by `check_mc_n.py`, which regenerates the list with `k4/check_mincex_cores4.py`'s independent code (orbit
  counting of G′, its own type enumeration and cuts) and decides coverage by SAT on its raw-definition masks.

**Result of the class run** (`results/k4_hunt/n6_m10_n42.log`): all 28,502 cores certified under every strict
profile (1.07·10⁸ profiles per core without two-private agents), 0 counterexamples; 29,069 CPU-s (mean 1.0 s, max
5.2 s per core, on a shared machine); allocations found per core: mean 110, median 107, max 262 (idx 20215,
[[0,3,5,8],[1,4,7,9],[2,7,8],[3,6,7],[4,8,9],[5,6,9]]: every agent has one private good, three goods of degree 3).
Certificate `results/k4_hunt/cert_n6_m10_n42.json.gz` (3.8 MB: one allocation per orbit of the core's automorphism
group, `orbits.py`; the checkers expand the orbits with their own automorphism computation); independent check
`results/k4_hunt/check_n6_m10_n42.log`: **RESULT OK** (`check.py`: completeness of the class by orbit counting and pairwise
non-isomorphism, coverage by check4_fast's C loop on this file's raw-definition rows, the one-hot SAT engine on a
sample of 100).

With K4.MC7 (β ≤ 4, i.e. m ≥ 11 when n₄ = 2) and Mahara's theorem (m ≤ n + 3 = 9), this gives: **every connected k = 4
core with n = 6 and exactly two 4-good agents has an EFX₀ allocation** (with K4.R6a: at most two), for the
coordinator to integrate.

β = 5 candidates at n = 6 (`results/k4_hunt/mc_n6_candidates_b5.log`; profile counts of the cut domains):

| m | n₄ | listed | left after K4.MC5 | largest profile space |
|---|---|---|---|---|
| 9 | 1 | 4,049 | 3,488 | 2.2·10⁶ (already K4.R6a) |
| 10 | 2 | 10,896 | 8,992 | 1.1·10⁸ (inside the class run) |
| 11 | 3 | 13,041 | 10,360 | 5.2·10⁹ |
| 12 | 4 | 7,295 | 5,839 | 2.5·10¹¹ |
| 13 | 5 | 1,827 | 1,490 | 1.2·10¹³ |
| 14 | 6 | 168 | 168 | 5.7·10¹⁴ |

All β at n = 6 (`results/k4_hunt/mc_n6_candidates_b6up.log`; files `mc_n6_b<β>.json.gz` regenerated by `mc_n.py 6`
in ~10 min, not committed except β = 5): the candidates with m ≥ 10 (m ≤ n + 3 is Mahara's theorem; at n = 6 and
m ≥ 10, n₄ = β + m − 13) are

| β | m = 10 | m = 11 | m = 12 | m = 13 | m = 14 | total |
|---|---|---|---|---|---|---|
| 5 | 8,992 | 10,360 | 5,839 | 1,490 | 168 | 26,849 |
| 6 | 40,171 | 34,374 | 13,213 | 1,927 | – | 89,685 |
| 7 | 77,784 | 44,529 | 9,206 | – | – | 131,519 |
| 8 | 71,047 | 21,388 | – | – | – | 92,435 |
| 9 | 26,255 | – | – | – | – | 26,255 |

366,743 in all (β ≥ 10 forces m ≤ 9). At the measured 0.1–5 s per candidate this is 10²–10³ CPU-hours, beyond one
session; β = 5 is run in full, β = 6–9 by a sample of 150 per (β, m) group (`sample_mc.py`).

### 3.3 Glued GM4 gadgets (n = 8)

`glue.py`: two GM4 cores of the DE4 screen set (`k4/gm4.md`: n = 4, a Pareto-maximal partial EFX₀ allocation that
cannot be completed) glued by identifying s goods, every strict profile searched. Probe (`results/k4_hunt/glue_probe*.json`):

| glued core | n | m | β | mode | result |
|---|---|---|---|---|---|
| GM4-C + GM4-S, s = 1 | 8 | 12 | 10 | every profile | certified, 162 s, 1,360 allocations |
| GM4-D + GM4-P, s = 1 | 8 | 13 | 12 | gadget types fixed off the glue | certified, 1.4 s |
| GM4-C + GM4-Q, s = 1 | 8 | 13 | 10 | fixed | certified, 1.5 s |
| GM4-C + GM4-Q, s = 2 | 8 | 12 | 11 | fixed | certified, 18 s |
| GM4-D + GM4-P, s = 2 | 8 | 12 | 13 | every agent touches a glued good, so every profile (288⁸ ≈ 4.8·10¹⁹) | **certified, 409 s, 2,402 allocations** (`named_glue_hard1_cores.json.gz`; independent check `check_named_glue_hard1.log`, sat2) |

The last core has goods of degree 7 and 6 (every agent values one of the two glued goods).

**Result of the β = 5 candidate run** (`results/k4_hunt/mc_n6_b5.log`): all 30,337 candidates certified (every
profile of the cut domains), 0 counterexamples; 27,585 CPU-s; per m: 9: max 1.8 s; 10: 2.2 s; 11: 3.5 s; 12: 6.4 s;
13: 8.4 s; 14: 13.2 s (the m = 14 cores are all-P4/Q4, no cuts, 288⁶ profiles); largest certificate 4,792 allocations
(images included). Independent check (`check_mc_n.py`): the regeneration with `k4/check_mincex_cores4.py`'s code
gives the same 30,337 candidates, orbit counting OK for every G′ class, and every one is covered (1.06·10¹⁷ profiles
in all): `results/k4_hunt/check_mc_n6_b5_full.log` on the full certificate (every image listed, 22 MB, not committed)
and `results/k4_hunt/check_mc_n6_b5.log` (**RESULT OK**) on the committed orbit-compressed one
(`results/k4_hunt/cert_mc_n6_b5_orb.json.gz`, 11 MB). With K4.MC7: **a minimal counterexample to TARGET₄ with n = 6 has β ≥ 6** (for the coordinator).

### 3.3b Structured families from the suite (`k4/suite/`)

| core | n | m | β | result |
|---|---|---|---|---|
| c4-H2 (`k4/c4.md` §7, H_t with t = 2; seven PP4 agents) | 9 | 23 | 5 | **certified under every strict profile**, 395 s, 1,111 allocations, 256 automorphisms (`named_suite_H2.json.gz`, check `check_named_suite_H2.log`, sat2: OK) |

### 3.4 Samples beyond the complete runs (hunting; each sampled core is still a complete search)

| set | sampled | certified | slowest | certificate / check |
|---|---|---|---|---|
| n = 6, β = 6–9, m ≥ 10: 150 per (β, m) group, 10 groups | 1,500 of 366,743 | 1,500 | 22 s (Q4⁵P4, m = 11, 288⁶ profiles) | `cert_mc_n6_sample_b6to9_orb.json.gz` / `check_mc_n6_sample_b6to9.log` (OK) |
| n = 7, β = 5: 100 per m (all 75 at m = 17) | 675 of 122,006 | 675 | 53 s (P4⁷, m = 17, 288⁷ ≈ 1.6·10¹⁷ profiles) | `cert_mc_n7_sample_b5_orb.json.gz` / `check_mc_n7_sample_b5.log` (OK) |

The n = 7, β = 5, m = 17 group (75 candidates, every agent P4 or Q4) is thereby **complete**. The independent
regeneration of the n = 7, β = 5 list gives the same 122,006 candidates (orbit counting OK).

Cost of finishing (mean time per candidate in the sample × group size, shared CPUs): n = 6, β = 6–9 ≈ 430
CPU-hours (β = 6: 59, β = 7: 145, β = 8: 161, β = 9: 65); n = 7, β = 5 ≈ 50 CPU-hours (m = 11: 3.7, 12: 8.9, 13: 14.5,
14: 11.7, 15: 9.0, 16: 2.4, 17: 0.5). Both are one dedicated multi-day run on 4 CPUs, resumable (`run_mc.py`
checkpoints), and n = 7, β = 5 is the cheaper next step.

### 3.5 Hypergraph climb with exact evaluation (`climb_h.py`)

From the three β = 5 candidates with the largest certificates at m = 12, 13, 14 (`climb_starts_b5.json`), 60 random
moves each (swap, add or drop one good of one agent; the result must be a connected core without an agent holding two
private goods, with a good of degree ≥ 3), every move evaluated by a complete search over all strict profiles, accepted
if the certificate (base allocations, images not counted) does not shrink by more than 5. 150 cores evaluated
(`results/k4_hunt/climb_b5.jsonl`): all certified, none timed out. The climbs all drift to dense cores of Q4 agents with
few goods: from scores 50–131 to 1,878–2,160 base allocations at n = 6, m = 10–11, β = 8–9, e.g.
[[0,7,8,9],[3,5,6,8],[0,1,3,5],[2,3,7,8],[2,4,6,9],[1,2,4,5]] (every agent Q4, every good of degree 2 or 3; 2,160).
Certificate size grows with the number of 4-good agents and β; no evaluated core has a profile without an EFX₀
allocation (certificate size measures how varied the allocations must be, not closeness to a failure).

## 4. Patterns

Certificate size (allocations the CEGAR needs to cover every profile of a core) as a hardness measure; random or
"few certificate allocations" profiles are not a good proxy for few EFX₀ allocations
(`attempts/k4-hunt-cert-size-proxy.md`).
- n = 6, m = 10, n₄ = 2 (28,502 cores): mean 110 allocations. Cores **without** an agent holding two private goods need
  the most (mean 126; with one such agent 98; with two 52), as K4.MC2 (such agents reduce away) suggests. Goods of
  very high degree make cores easier (largest degree 6: mean 63; degree 3–4: 99). The largest certificates (250–262)
  belong to cores in which every agent has one private good and the shared goods have degree 3.
- β = 5 candidates: the largest certificates are on cores with twin agents (identical relevant sets), e.g.
  Q4 Q4 P3 P3 P3 P3 [[0,1,2,4],[0,1,2,4],[3,5,6],[3,5,7],[3,5,8],[4,5,9]] (1,116 allocations, images included).
- Dense glued cores (n = 8, β = 13) need thousands (2,402).

## Reproduce

```
python3 k4/hunt/run.py 6 10 --n4=2 --jobs=3 --tag=n6_m10_n42          # ~1 h on 3 CPUs
python3 k4/hunt/check.py results/k4_hunt/n6_m10_n42_p0of1.json.gz --sat-sample=50
python3 k4/hunt/named.py mc7                                           # the 6 cores of K4.MC7, ~20 s
python3 k4/hunt/check.py results/k4_hunt/named_mc7.json.gz --engine=sat2
python3 k4/hunt/test_check.py results/k4_hunt/named_mc7.json.gz --cores=6 --engines=sat2      # sensitivity
python3 k4/hunt/mc_n.py 6 --bmin=5 --bmax=5 --write=results/k4_hunt/mc_n6.json.gz             # candidates, ~20 min
python3 k4/hunt/run_mc.py results/k4_hunt/mc_n6_b5.json.gz --tag=mc_n6_b5
python3 k4/hunt/check_mc_n.py 6 results/k4_hunt/mc_n6_b5.json.gz --bmin=5 --bmax=5
```
