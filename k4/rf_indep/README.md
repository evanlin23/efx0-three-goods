# Independent check of Conjecture RF at n = 5

Workstream `compute/k4-rf-indep`. The coordinator asked for an RF checker written from the statement alone, without
reading the existing checkers (`k4/oc1_hall/rf_n5*.py`, `k4/sdc/receiver_first_*.py`, `oc_absorb.py`, `de_free.py`, the
certifier). It was run on the certifier's n = 5 failure exports and compared with `k4/oc1_hall.md` §24.10.

## What is checked

**Conjecture RF** (`k4/sdc.md` §31 end, as amended 2026-11-27 04:22 UTC). Take a maximum-matching SD start Y where OC₁
fails, and any receiver u of Y. Then:
- (a) some order with u first gives a maximum matching;
- (b) every order with u first that gives a maximum matching satisfies OC₁.

(b) is tested at the picks Y′ of all (n − 1)! = 24 u-first orders, not only at the rotation (u, o − u). Each distinct
(profile, Y′) pair is tested once.

**Own code.** This workstream's own code covers each ingredient.
- *SD.* Each agent takes its best remaining relevant good, with ties broken by lower good index. An agent with no
  relevant good left gets nothing. A fast version is cross-checked against `k4/d1/d1lib.py`.
- *Maximality.* ν comes from augmenting paths, cross-checked by brute force and against the export's `nu`. Y′ is a
  maximum matching iff ν agents hold a pick.
- *Receivers.* u holds a pick and no j ≠ u has v_j(Y_u) > v_j(Y_j).
- *OC₁* (`k4/sdc.md` §29). Either the picks have a one-absorber completion, or one improving chain leaves bases that
  have one.
  - A *one-absorber completion* is a complete raw-EFX₀ allocation extending the bases. One agent receives any number of
    junk goods, and every other agent at most one.
  - An *improving chain* is a list of distinct agents x₀, …, x_t with t ≥ 1. It comes with disjoint sets
    H₀ ⊆ (J ∪ B_{x_t}) ∩ R_{x₀} and H_i ⊆ J ∩ R_{x_i}. The conditions are v_{x₀}(H₀) > v_{x₀}(B_{x₀}) and
    v_{x_i}(B_{x_{i−1}} ∪ H_i) > v_{x_i}(B_{x_i}).
  - Only chains are used, not de_free's separate additions or rings. A ring is a chain with B_{x_t} ⊆ H₀. Using fewer
    moves makes every "OC₁ holds" answer conservative.

**Trust.**
- The search is `rf_oc1.c`. Every positive answer carries a witness, meaning the chain and the final allocation.
- `rf_check.py` re-checks each witness: the chain conditions above, that the allocation extends the bases with the
  one-absorber shape, and raw EFX₀ through `d1lib.efx0`.
- A negative answer is re-checked by a pure-Python exhaustive search (`py_oc1`, chains by `itertools` and
  `d1lib.one_absorber`). That search is a second implementation.

## Run

```
D=<dir>; for f in two_move_starts_n5_sel2.json.gz two_move_starts_n5_partial6.json.gz \
                  5_pure_s5o0_summary.jsonl.gz 5_pure_s5o1_summary.jsonl.gz; do
  git show origin/compute/k4-oc1max-cert:results/k4_oc1max/n5/$f > $D/$f; done
python3 k4/rf_indep/rf_check.py --data $D --orig all --orig-py 100      # about 4 min on 4 CPUs
```

`--orig all` also runs the OC₁ search at every failing start Y itself, where it should answer F. `--orig-py 100`
re-checks 100 of those F answers per hypergraph in pure Python. The log is `results/k4_rf_indep/rf_check_n5.log`; the
input files' SHA-256 prefixes are printed at its top.

## Results (2026-11-27, `results/k4_rf_indep/rf_check_n5.log`, 224 s on 4 CPUs)

**Data.**
- The certifier's exports cover 9 hypergraphs with 1,285,930 failing starts:
  - complete lists (`sel2`): 5_pure #38, #419 and #447;
  - partial, time-limited lists (`partial6`): #164, #374, #379, #464, #778 and #808.
- The stored failures `oc1_fails` of 5_pure_s5o0/s5o1 add 568 starts, 5 of them with two receivers.

Every hypergraph has ν = 5, and all three computations of ν agree.

**Consistency with the export**, at every one of the 1,285,930 starts:
- The listed orders (7,608,052) are exactly the orders whose SD picks are Y.
- Y is a maximum matching.
- There is one receiver, and it is the export's.

**RF (a).** It holds at all 1,285,930 export (start, receiver) pairs and all 573 stored ones.

**RF (b), every u-first order:**

| data | distinct u-first vectors | maximum matchings (tested) | P | one chain, t = 1 | t = 2 | t = 3 | F |
|---|---|---|---|---|---|---|---|
| complete exports (#38, #419, #447) | 1,676,160 | 1,676,160 | 1,575,360 | 100,800 | 0 | 0 | 0 |
| partial exports (6 hypergraphs) | 3,534,433 | 3,471,829 | 2,842,457 | 559,740 | 62,172 | 7,460 | 0 |
| stored failures | 2,745 | 2,700 | 2,143 | 486 | 71 | 0 | 0 |

- All 5,150,689 witnesses verify.
- t is the shortest repairing chain, because the search tries increasing t. The 7,460 vectors with t = 3 are on #374
  (960) and #164 (6,500).
- 62,604 export u-first vectors are not maximum matchings, so RF excludes them. They are on #374 (9,237) and #379
  (53,367).

**Comparison with `k4/oc1_hall.md` §24.10.** All of Hall's counts are reproduced exactly:

| quantity | here | Hall |
|---|---|---|
| distinct rotation (u, o − u) RF starts | 1,530,083 | 1,530,083 |
| rotation RF starts that are maximum matchings | 1,526,623 | 1,526,623 |
| pickless rotations | 3,460 | 3,460 |
| u-first maximum-matching vectors behind them | 26,524 | 26,524 |
| stored maximum-matching RF starts | 650 | 650 |
| stored pickless rotations | 16 | 16 |

Every maximum-matching rotation vector is a u-first vector above, so all 1,526,623 (and the 650 stored) satisfy OC₁, as Hall found.

**OC₁ at the failing starts themselves.** The search answers F at all 1,285,930 export starts, agreeing with the
certifier. 100 per hypergraph were re-checked by the pure-Python search, which also gives F.

**What this does and does not establish.**
- This is EVIDENCE for RF at n = 5. The partial lists are not all failing starts of their hypergraphs, and n = 5 has
  many other cores.
- For #38, #419 and #447 the check covers every failing (type profile, picks) pair. That relies on two things not
  re-derived here: the certifier's completeness flag, and the type reduction, under which SD, receivers, maximality and
  OC₁ compare only single agents' subset sums.

## Conjecture RKMAX on the n = 5 lists (`rkmax_check.py`)

**Statement** (`k4/sdc.md` §31 end on claude/kind-lamport-y8fdme). rank_i(Y) is 1 plus the number of i's relevant
goods valued above Y_i, and an agent with no pick has rank 5. Let σ(Y) = (#rank 1, …, #rank 4). Every maximum-matching
SD vector whose σ is lexicographically maximal among the profile's maximum-matching SD vectors must satisfy OC₁.

**Method.** The script was written without reading `k4/sdc/extremal_rank_check.py`, `extremal_rank_n5.py` or
`oc1_mc2_rand`. For each profile it takes the SD picks of all 120 orders, keeps the maximum matchings, and tests OC₁ at
each σ-maximal one. It uses the same OC₁ search and witness checks as above.

**Results** (`results/k4_rf_indep/rkmax_check_n5_sel2.log`, `rkmax_check_n5_partial6.log`, about 1 min each):

| lists | profiles | σ-maximal vectors | P | one chain (t = 1) | F |
|---|---|---|---|---|---|
| sel2, complete (#38, #419, #447) | 583,680 | 1,004,160 | 1,004,160 | 0 | 0 |
| partial6 (6 hypergraphs) | 700,500 | 1,305,032 | 1,299,946 | 5,086 | 0 |

- Every export failing start has a maximum-matching SD vector of larger σ. That is the "proof shape" form of RKMAX.
- No profile has a tie between two single goods of one agent.
- This is a second implementation for the coordinator's sel2 count, 583,680 of 583,680. Calling it a certificate on
  #38, #419 and #447 still relies on the certifier's completeness flag and on the type reduction.

## RKMAX on random strict profiles of every pure n = 5 core (`rkmax_rand.py`)

**Setup.**
- Cores: all 4,674 pure n = 5 cores of `results/k4_certs_5_pure.json.gz`, named (m, idx) as there. The certifier's
  "5_pure #k" with m goods is the core (m, k).
- Profiles are strict: each agent's four values are a random 4-subset of 1..V, with all 16 subset sums distinct.
  V = 20 is the distribution of Hall's census (`k4/oc1_hall.md` §24.14, which used 60 profiles per core).
- For each profile: all 120 orders, the maximum matchings among them, then OC₁ at every σ-maximal one.

**Results** (`results/k4_rf_indep/rkmax_rand_n5_v20_s1.log`, `rkmax_rand_n5_v250_s1.log`, about 4 min each):

| V | profiles | σ-maximal vectors | P | one chain, t = 1 / 2 / 3 | F |
|---|---|---|---|---|---|
| 20 | 2,804,400 | 4,224,072 | 4,217,075 | 6,961 / 36 / 0 | 0 |
| 250 | 2,804,400 | 4,225,553 | 4,218,988 | 6,526 / 37 / 2 | 0 |

- 600 profiles per core is 10× Hall's census at each V. No RKMAX counterexample was found, and every witness verifies.
- Receivers of the σ-maximal vectors at V = 20 (0 / 1 / 2 / 3 / 4 / 5 receivers): 2,160 / 1,822 / 100,578 / 992,685 /
  2,184,604 / 942,223.
  - One-receiver vectors: 1,822, about 10× Hall's 178. 525 of them need a chain, the largest share of any class.
  - At V = 250: 1,764 one-receiver vectors, 486 of them needing a chain.
- *Definition.* Here a maximum matching has ν picks. The single core with m = 4 has ν = 4, and its vectors are counted.
  Hall reports 60 profiles with "no maximum-matching vector" there, so the census apparently required n picks.

**One-receiver σ-maximal vectors** (for the rkmax session). Each line of
`results/k4_rf_indep/rkmax_rand_n5_v20_s1_one_receiver.jsonl.gz` (1,822 lines) and `..._v250_s1_one_receiver.jsonl.gz`
(1,764 lines) holds one vector:
- `core_m`, `core_idx`, `sets`, `vals`, `picks`, `sigma` and `receivers`;
- `oc1`, the search's answer: `P o X…`, or `C t x… H… o X…` (masks, as in `rf_oc1.c`).

They come from rerunning the two hunts with `--dump`, which gave identical counts. Breakdown: at V = 20, P 1,297, one
chain t = 1 493, t = 2 32; at V = 250, 1,278 / 455 / 31.

**Hall's counterexample to plan (a), replayed** (`rkmax_replay.py`, `results/k4_rf_indep/rkmax_replay_358.log`). The
core is 5_pure (8, 358). My code gives the same picture as Hall's:
- 10 maximum-matching SD vectors;
- σ-maximal vectors (5, 6, 7, 2, 4) and (5, 7, 6, 2, 4), with σ = (3, 1, 0, 1);
- receivers {3} and junk {0, 1, 3};
- OC₁ after one verified chain 0 → 3: agent 0 takes {0, 1}, agent 3 takes good 5.

## RKMAX climb at n = 5 (`rkmax_climb.py`)

**Setup.**
- *Seeds:* the 1,011 one-receiver σ-maximal vectors of the two random hunts whose picks do not complete (525 at
  V = 20, 486 at V = 250).
- *Target:* a σ-maximal maximum-matching SD vector (all 120 orders) with one receiver, whose picks do not complete.
- *Score* (lower is harder): the hardest target's pair (number of repairing post-chain states, number of
  (absorber, placement) completions over them). A post-chain state is repairing if it has a one-absorber completion.
  It comes from `rf_oc1.c count`, which is exhaustive.
- *Mutation:* change one value (resample, a nudge of ±1..3, or a swap of two values of one agent), keeping the profile
  strict.
- *Acceptance:* the profile must still have a target and the score must not rise. With probability 0.05 the
  repairing-state count may rise by 1.
- *Failure detection:* every σ-maximal vector is tested at every step, so any OC₁ failure would be caught.

**Results** (`results/k4_rf_indep/rkmax_climb_n5.log`, `rkmax_climb_n5_best.jsonl.gz`; 375 s on 4 CPUs):
- 1,011 seeds × 5,000 steps: about 5.05M profiles evaluated and 3.04M moves accepted. There was **no OC₁ failure** at
  any σ-maximal vector, so no RKMAX counterexample.
- Repairing post-chain states of the hardest target, before → after the climb:
  - before: 1 at 175 seeds, 2 at 383, ≥ 3 at 453;
  - after: 1 at 566 seeds, 2 at 401, ≥ 3 at 44.
- The tightest profiles score (1, 4): of 7 to 10 post-chain states, exactly one has a completion, and only 4
  (absorber, placement) pairs complete it.
  - For example, core (9, 221): sets [[0,2,4,8],[1,4,7,8],[3,5,6,8],[4,5,6,7],[5,6,7,8]], vals
    [[4,3,13,15],[6,15,11,18],[10,18,16,11],[16,22,18,3],[5,17,16,14]], σ-maximal picks (8, 4, 5, 7, 6), receiver 3.
  - So RKMAX at these one-receiver σ-optima holds with almost no slack. A proof will need the exact repairing move.

## RKMAX at n = 6 (`rkmax_rand.py --any-n`)

**Cores.** The 𝒦 list at n = 6, β = 5 of the twins/rf-min session is `results/k4_rfmin/mc_n6_b5_mc9.json.gz` on
proof/k4-rf-min, PR #156. Its sha256 prefix 22ef143abaee16b1 is in the log, and the file itself is not copied here.
- I kept the 18,044 cores with at least two 4-good agents (`--min4 2`), which is 𝒦's count in `k4/RFMIN.md`.
- They have m = 10–14 and ν = 6. A core is named by its position in the list.

**Method.** 30 strict profiles per core at each V; each agent's values are a random subset of 1..V of its set's size.
All 720 orders, and OC₁ at every σ-maximal maximum-matching vector.

| V | profiles | σ-maximal vectors | P | one chain (t = 1) | F |
|---|---|---|---|---|---|
| 20 | 541,320 | 864,508 | 864,408 | 100 | 0 |
| 250 | 541,320 | 864,206 | 864,114 | 92 | 0 |

- Logs: `results/k4_rf_indep/rkmax_rand_n6_b5_v20_s1.log` and `..._v250_s1.log`, about 160 s each.
- There is no RKMAX counterexample, and every witness verifies.
- One-receiver σ-maximal vectors almost vanish at n = 6: 1 at V = 20 (it needs a chain; it is in
  `rkmax_rand_n6_b5_v20_s1_one_receiver.jsonl.gz`) and 0 at V = 250. At n = 5 they were 1,822 and 1,764.
- The vectors needing a move have 2–4 receivers: 99 of the 100 at V = 20 and all 92 at V = 250.

## RF off the exports (workstream compute/k4-rf-offexport; `rf_rand.py`, `rf_climb.py`)

**What is tested.** At every OC₁-failing maximum-matching SD start Y found, the script lists Y's receivers u. It then
tests three statements:
- (a) the every-order form of RF (K4.SDC.RF as amended): every u-first maximum-matching order satisfies OC₁;
- (b) Hall's RF-rot∃ (`k4/oc1_hall.md` §24.15 on claude/k4-oc1-hall): some order o giving Y has the rotation
  (u, o − u) whose picks are a maximum matching satisfying OC₁. If the rotation leaves an agent pickless, the
  variant (u, d, o − u − d) is used, with d the RF path's end;
- (c) RF∃: some u-first maximum-matching order satisfies OC₁.

Every u-first or rotation vector is an SD vector of the profile, and OC₁ is computed at all of them. Witnesses are
re-checked.

**Data** (`results/k4_rf_offexport/`):
- Uniform random strict profiles of all 4,674 pure n = 5 cores, 600 per core at V = 20 and at V = 250, 5.6M profiles in
  all (`rf_rand_n5_v*_s1.log`). They gave 0 and 1 failing starts: OC₁^max failures are rare, about 10⁻⁷ of the type
  profiles of #419.
- Uniform random profiles of the 277 failure-capable cores, 10,000 per core at V = 10 and V = 20, 5.54M profiles
  (`rf_rand_n5cap_v*_s1.log`). 12 failing starts, 3 with two receivers.
  - A core is failure-capable when the certifier's chunk summaries s5o0/s5o1 (1,870 of the 4,674 cores) show
    OC₁^max-failing pairs: `capable_cores.py`, `n5_failure_capable_cores.json.gz`. 9 of these cores are the export
    hypergraphs.
- A walk inside the failing region (`rf_climb.py --seeds-file`, `rf_walk_n5_stored.log`, dump
  `rf_walk_n5_stored_fails.jsonl.gz`).
  - It starts from each of the certifier's 568 stored failing starts and makes 3,000 value mutations.
  - A move is accepted only if the profile keeps an OC₁-failing maximum-matching start.
  - Failing starts are deduplicated by core, ordinal type of every agent, and picks.
  - It reached **241,728 distinct failing starts on all 277 cores**: 232,325 on the 268 non-export cores, 3,267 of
    them with two receivers, giving 244,995 (start, receiver) pairs.

| data | failing starts | (start, receiver) pairs | (a) | (b) | (c) |
|---|---|---|---|---|---|
| uniform, all pure cores | 1 | 1 | 1 | 1 | 1 |
| uniform, failure-capable cores | 12 | 15 | 15 | 15 | 15 |
| walk from the stored failures | 241,728 | 244,995 | **244,951** | 244,995 | 244,995 |

**The every-order form of RF is false at k = 4** (`verify_rf_every_cex.py`, `verify_rf_every_cex.log`). The 44 (a)
failures are 22 profiles of one core, with two failing starts each.

- Core (8, 440): sets [[0,3,5,7],[1,2,3,6],[1,2,6,7],[4,5,6,7],[4,5,6,7]]. Agents 3 and 4 are set-twins.
- For example, vals [[5,19,13,10],[9,6,17,12],[3,5,7,6],[14,1,7,4],[18,4,11,5]], which are strict.
  - Y = (3, 6, 7, 4, 5), the SD picks of (0, 1, 2, 3, 4), is a maximum matching and OC₁ fails there. Its only receiver
    is 4.
  - The 4-first order (4, 0, 1, 2, 3) gives the maximum matching Y′ = (3, 6, 7, 5, 4). That is the twins' pick swap,
    and OC₁ fails there too.
  - Symmetrically, Y′ is a failing start with receiver 3, and (3, 0, 1, 2, 4) leads back to Y.
- Three implementations agree on every failure at all 44:
  - `rf_oc1.c`;
  - `rf_check.py_oc1` (d1lib's raw EFX₀ and one-absorber enumeration);
  - `brute()`, written inline from §29.
- The same script checks the core list, strictness, SD orders, maximality and receivers.
- At these starts (b) and (c) hold: 5 of the 6 distinct 4-first maximum-matching vectors satisfy OC₁. So the
  some-order forms survive, and the every-order form needs the twin case excluded.

**n = 6** (the 18,044 𝒦 cores of K4.SDC.RKMAX.RAND6X, all 720 orders):
- Uniform: 100 strict profiles per core at V = 20, 1,804,400 profiles (`rf_rand_n6_b5_v20_s1.log`). There is no
  OC₁^max-failing start: all 5,940,266 maximum-matching SD vectors satisfy OC₁ (P 5,799,607, one chain 140,659).
- Climb toward a failing start (`rf_climb.py`, `rf_climb_n6_b5.log`): 400 random seeds × 1,000 steps, about 400,000
  profiles evaluated. It reached no failing start. 143 seeds end with a single repairing post-chain state at their
  closest vector, and 211 with two.
- So (a)–(c) are never exercised at n = 6 here. What this does show is EVIDENCE for OC₁^max on these cores. Testing
  RF there needs known n = 6 failing starts to walk from; at n = 5 the walk worked only from the certifier's stored
  failures.
