# COVER and COVER⁺ on large data, and a hunt for counterexamples (compute/k4-cover)

Workstream `compute/k4-cover`, branched from proof/k4-f2 (PR #82). Everything here is EVIDENCE: random,
exhaustive-per-core and annealed data. Nothing is proved, and no ledger row is changed.

## Verdicts

**COVER⁺ is false as stated** (`FAILURES.md`).
- The statement: at every f ≥ 2 key with def* > 0, some maximum of (r′, Λ′) has Lemma A⁺ (any j), B⁺ (threat path 1),
  C⁺ or C′⁺ (any k) applying at P_Q.
- 1,280 distinct uncovered keys were found, at n = 4 (f = 2) and n = 5 (f = 2, 3). The smallest is n = 4, m = 7, f = 2.
  `k4/cover_indep.py` confirms every one. It re-codes the lemma tests from the written statements and uses
  k4/rt4_n5_indep.py's deficits and move kinds. Of the 7,449 uncovered n = 5 profiles from the hunts, it checked
  1 in 25.
- **DLKey held at all 1,280 uncovered keys.**
- **Theorem Z′⁺'s conclusion held at all 1,280**: at some maximum, one move from P_Q reaches deficit ≤ 0.
  - At 1,271 it is a plain (T3) move with one helper. None of A⁺, C⁺, C′⁺ allows that shape, and B⁺ allows it only
    along a threat path into the helper.
  - At 9 it is a (T3⁺) move with |W| = 1 and no helper.
- The obstructions, in PR #80's sx_f2 terms, are four:
  - a crossed pair: x's admissible base needs a good of another leaf's pair;
  - a leaf threatening two or three frozen agents;
  - an (R) leaf with its fourth good in the pool on B⁺'s path, the missing f ≥ 2 form of Lemma B′;
  - only B⁺ with threat path 2 (one key).
- How often: 0 of 262,768 keys in the exhaustive n = 3 and n = 4 (≤ 2 four-good agents) runs. 3 of 9,517 (n = 4, three
  4-good agents, random), 26 of 7,687 (n = 4 pure, random), 6 of 1,155 (n = 5, 2,000 per core) and 21 of 84,172 (the
  dumps).

**COVER (f = 1) held everywhere tested**, with 0 uncovered keys:
- 64,944 distinct keys in the reproduction of PR #80's data (66,166 counted per input; with its semantics);
- 1,459 new keys of the large data (n = 4, 5);
- 125,445 f = 1 profile evaluations of the hunts (n = 4, 5; each with a def* > 0 key).

At 2 new keys only the exact hypotheses work. The hunts found thousands of profiles whose keys only C′, or only B1′ with
its exact hypothesis, covers. None went further.

## Keys tested (keys with def* > 0; each key once per distinct profile)

| input | profiles screened | f = 1 keys | f = 2 keys | f = 3 keys | f = 4 keys | uncovered |
|---|---|---|---|---|---|---|
| Phase 1: PR #80's f = 1 inputs (n = 3 every profile; n = 4, 5 hunts; compute/k4-rc's 45; T1-stuck) | (theirs) | n3 62,208; n4 2,679; n5 57 | | | | 0 |
| Phase 1: PR #80/#82's f ≥ 2 inputs (counted with repeats, as k4/f2_cc.py) | (theirs) | | n3 126; n4 132 | n4 4; n5 27 | | 0 |
| n = 3, every strict profile of every core | 299,837,376 | (= Phase 1) | 193,744 | | | **0** |
| n = 4, one 4-good agent, every strict profile | 7,247,232 | 0 | 146 | 140 | | **0** |
| n = 4, two 4-good agents, every strict profile | 724,847,616 | 0 | 30,306 | 38,432 | | **0** |
| n = 4, three 4-good agents, 200,000 per core (seed 2026) | 67,800,000 | 269 | 5,889 | 3,628 | | 3 (f = 2) |
| n = 4, pure, 2,000 + 200,000 per core (seeds 2026, 2027) | 44,238,000 | 1,170 | 5,151 | 2,536 | | 26 (f = 2) |
| n = 5, every certificate file, 200 per core; pure also with big-top types only (seed 2026) | 7,251,600 | 2 | 39 | 90 | | 0 |
| n = 5, n4_4 and pure 2,000 per core, pure big-top 2,000 per core (seed 3031) | 38,388,000 | 18 | 318 | 763 | 74 | 6 (2 f = 2, 4 f = 3) |
| n = 6, one 4-good agent, 50 per core | 1,343,300 | 0 | 0 | 0 | 0 | 0 |
| dumps of compute/k4-rt4, k4-dl13 (main), k4-rc, k4-portfolio, f ≥ 2 profiles | 203,442 distinct read | | n3 7,806; n4 11,340; n5 2,836; n6 366 | n4 31,730; n5 25,148; n6 4,600 | n5 336; n6 10 | 21 (8 f = 2, 13 f = 3) |

Phase 3 hunts (`k4/cover_hunt.py`; 20 runs of up to 30 min; counts are evaluations, with repeats):

| target | seeds | evaluations | uncovered | notes |
|---|---|---|---|---|
| COVER at f = 1, n = 4 | 7 n = 4 keys covered only by C′ or by B1′ (exact), m = 10, 11 | 55,009 | **0** | 12,219 profiles whose keys only C′ or only B1′ (exact) covers |
| COVER at f = 1, n = 5 | 5 n = 5 keys of the validation (m = 11, 12) | 70,436 | **0** | least margin 1 throughout |
| COVER⁺, ZMOVE, n = 4 | K4.F2.X (2) (m = 10), K4.SX.X (3) (m = 8), two m = 7 uncovered keys | 167,326 | 926 distinct keys beyond Phase 2's, all confirmed | every uncovered key has a repair move from P_Q; on the m = 7 cores the hardest still had 16 such moves |
| COVER⁺, ZMOVE, n = 5, 6 | the n5c path-swap key (m = 12), two n = 5 uncovered keys (m = 9, 10), one n = 6 key (m = 13) | 46,025 | 7,449 profiles at n = 5 (298 keys confirmed, 1 in 25); 0 at n = 5 m = 12 and at n = 6 | no ZMOVE failure |

## Coverage per lemma (keys with the lemma at some maximum)

| input | A / A⁺ | B1 / B⁺ (k = 1) | B1′ | C / C⁺ | C′ / C′⁺ | keys |
|---|---|---|---|---|---|---|
| f = 1, Phase 1 (PR #80's semantics) | 59,931 | 13,556 | 34 | 20,542 | 20,111 | 64,944 |
| f = 1, new data (n = 4, 5) | 1,407 | 173 | 27 | 623 | 168 | 1,459 |
| f ≥ 2, n = 3 every profile | 193,744 | 0 | | 0 | 55,224 | 193,744 |
| f ≥ 2, n = 4 (≤ 2 four-good agents) every profile | 68,944 | 80 | | 28,132 | 5,032 | 69,024 |
| f ≥ 2, n = 4 random (three, four 4-good agents) | 14,958 | 112 | | 10,014 | 3,301 | 17,204 |
| f ≥ 2, n = 5 random | 1,047 | 21 | | 1,175 | 606 | 1,284 |
| f ≥ 2, dumps | 80,557 | 2,670 | | 40,879 | 25,249 | 84,172 |

(From `final_phase2.txt`, `final_validate_*.txt`. Keys covered by exactly one lemma: see there.) A⁺ dominates at f ≥ 2.
C⁺ / C′⁺ are needed alone at 2,169 + 31 + 230 + 3,523 keys of the random n = 4, 5 data and the dumps. B⁺ (k = 1) alone
covers 80 + 15 + 52 keys.

## Uncovered keys

- **COVER (f = 1): none.**
- **COVER⁺: 1,280 distinct keys** (`uncovered_phase2.*`, `uncovered_hunt_n4.*`, `uncovered_hunt_n5_every25.*`;
  one JSON line per key: the profile, key, def*, maxima, the best move from each P_Q with k4/rt4_n5_indep.py's deficit
  and kind, DLKey, PR #80's obstruction reasons).
  - 56 come from Phase 2's data: 35 at n = 4, f = 2; 4 at n = 5, f = 2; 17 at n = 5, f = 3.
  - 1,224 come from the hunts: 926 at n = 4 and 298 at n = 5 (1 in 25).
  - def* = 1 at 1,241 keys, def* = 2 at 39.
  - Obstructions (keys, PR #80's sx_f2 reason at the maxima):
    - free needers off the path to the leaf (the crossed pair): 796;
    - an (R) leaf with s in L on B⁺'s path: 411;
    - a leaf threatening 2 or 3 frozen agents: 72;
    - only B⁺ with a threat path of length 2: 1 (n = 5).
  - **DLKey held at every one of the 1,280.** The best edge out of the key is a (T3) move without helper at 1,072,
    a (T3) move with helper at 205, and a (T3⁺) move with |W| = 1 at 3 (`k4/cover_check.py`'s dlkey records).
  - **Theorem Z′⁺'s conclusion held at all 1,280**: a (T3) move with one helper from P_Q to deficit ≤ 0 at 1,271,
    a (T3⁺) move with |W| = 1 and no helper at 9.
- Smallest: n = 4, m = 7, f = 2, ω = 1, sets [[0,2,3,6],[1,3,4,5],[2,4,5,6],[4,5,6]], values
  [[2,4,8,5],[1,4,6,8],[2,8,4,3],[3,4,2]], key (agent 2 on 5, agent 3 on 4), def* = 1. It is an (R) leaf with s in L
  (`FAILURES.md`, `failure_n4_m7.log`). The first one found is the crossed pair at n = 4, m = 10 (`failure_n4_m10.log`).
  A def* = 2 one at n = 5, m = 12, f = 3 is in `failure_n5_m12_def2.log`.

## The smallest key covered by only one lemma, per lemma (by n, m, sum of values; `final_all.txt`)

| lemma | f | smallest key it alone covers |
|---|---|---|
| A | 1 | n = 3, m = 6: [[0,3,4,5],[1,3,4,5],[2,3,4,5]], [[3,5,6,7],[2,3,4,8],[2,3,4,8]], key (agent 0 on 5) |
| B1 | 1 | n = 3, m = 7: [[0,1,2,3],[2,4,5,6],[3,4,5,6]], [[2,3,8,4],[8,3,2,4],[2,4,7,8]], key (agent 0 on 2) |
| B1′ | 1 | n = 4, m = 11: [[0,2,7,8],[1,5,7,10],[3,6,9,10],[4,8,9,10]], [[5,2,4,8],[3,5,6,7],[2,3,6,10],[2,3,4,8]], key (agent 1 on 10) |
| C | 1 | n = 4, m = 9: [[0,2,4,5],[1,3,4,8],[3,6,7,8],[5,6,7,8]], [[4,5,8,2],[3,4,2,8],[6,2,3,10],[6,3,5,7]], key (agent 3 on 8) |
| C′ | 1 | n = 4, m = 10: [[0,2,7,9],[1,5,8,9],[3,6,8,9],[4,7,9]], [[5,4,6,8],[4,3,2,8],[3,4,2,8],[4,3,2]], key (agent 0 on 9) |
| A⁺ | 2 | n = 3, m = 5: [[0,1,3,4],[2,3,4],[2,3,4]], [[2,3,8,4],[2,3,4],[2,3,4]], key (0 on 4, 2 on 3) |
| A⁺ | 3 | n = 4, m = 6: [[0,2,4,5],[1,4,5],[3,4,5],[3,4,5]], [[2,3,8,4],[2,3,4],[4,2,3],[4,2,3]], key (0 on 5, 2 on 3, 3 on 4) |
| B⁺ (k = 1) | 2 | n = 4, m = 7: [[0,2,3,4],[1,5,6],[2,3,5,6],[4,5,6]], [[2,5,4,8],[2,3,4],[2,3,8,4],[2,3,4]], key (1 on 5, 2 on 6) |
| C⁺ | 2 | n = 4, m = 7: [[0,3,5,6],[1,4,5,6],[2,3,4,5],[2,3,4,6]], [[4,3,10,8],[3,2,10,6],[6,5,3,7],[7,4,2,8]], key (2 on 5, 3 on 6) |
| C′⁺ | 2 | n = 4, m = 8: [[0,2,4,6],[0,2,5,6],[1,3,4,7],[1,3,5,7]], every agent 2,3,8,4, key (0 on 4, 1 on 5): K4.SX.X (3) |
| C′⁺ with q = φ(w) only | 2 | n = 4, m = 10: [[0,2,4,8],[1,3,7,9],[4,5,6,7],[5,6,8,9]], [[2,4,8,3],[3,4,2,8],[8,4,3,2],[2,3,4,8]], key (0 on 4, 1 on 9) |

## Phase 1: one checker, validated

`k4/cover_check.py` reproduces PR #80's and PR #82's counts exactly (`validate/README.md`).
- f = 1: 62,208 keys (n = 3, every strict profile), 2,661 (n = 4 hunts), 11 (n = 5 hunts), 45 (compute/k4-rc) and
  1,241 (T1-stuck).
  - The per-maximum first lemmas agree as well: A 104,372, B1 7,824, C 4,052 at n = 3.
  - At n = 4 one maximum moves from B1′x to C′. That is PR #80's post-review sx_zprime; its logs predate the change.
- f ≥ 2: 289 keys. A⁺ or B⁺ covers 193; the other 96 (174 maxima) need C⁺ or C′⁺.
- Deficits:
  - every min-frozen state's Lemma H1 deficit is checked against main's model.py direct removal-only deficit, in every
    run except the hunts;
  - the whole deficit table is checked against k4/rt4_n5_indep.py on the n = 5 validation inputs.
- `k4/cover_indep.py` agrees with the checker:
  - at all 639 f ≥ 2 validation maxima, and at 896 of 897 sampled f = 1 maxima. The one difference is Lemma C with a
    θ-b terminal τ₁ that is not a leaf: the statement allows it, PR #80's tool tests leaves only, and
    `cover_check.py` now tests it too (`lemma_c_nonleaf`; the Phase 2 and 3 runs use it);
  - on a 1-in-10 sample of the dump verdicts (n ≤ 4): 1,553 profiles, 4,696 keys, 12,078 maxima × 4 lemmas, with
    0 differences;
  - at all 1,280 uncovered keys.
- `k4/cover_screen.c` (the C screen for keys with def* > 0 at any f) reproduces red.c's key_noncompletable counts
  exactly: 240 in the same 240 profiles of n4_pure_r40k, and 62,208 at n = 3.
- The checker's own assertions (the libraries assert every repair they claim): none failed anywhere (0 LEMMA-ASSERT).
  `k4/cover_indep.py` re-verified each claimed repair it found (def ≤ 0 and the move kind) with no failure.

## Cuts (time)

- compute/k4-rc's two fail10 hill-climb dumps (`dump_hunt_fail10*.jsonl.gz`, 21,131 n = 5 profiles of a few cores) were
  checked 1 in 8. Its 45 n = 10 glue profiles were not checked: Python enumeration at n = 10 is out of reach.
- n = 4 with three 4-good agents and pure: random samples, not every profile (35 and 1,022 billion profiles).
- n = 5: 200 per core for every file and 2,000 per core for n4_4 and pure; n = 6: 50 per core of one file.
- The n = 5 hunts' 7,449 uncovered profiles: 1 in 25 confirmed by the second implementation; the rest rest on
  `cover_check.py` alone.
- The hunts skip the model.py deficit check (`--verify`) for speed. Every uncovered key they report is re-confirmed as
  above.

## Tools (all new files; EVIDENCE tooling)

| file | what it does |
|---|---|
| `k4/cover_check.py` | the checker: per profile, every key with def* > 0, its maxima of (r′, Λ′), at each the lemmas that apply (PR #80's `sx_zprime` / `sx_f2` and PR #82's `f2_cc.test_max`, unchanged, called once per maximum; plus Lemma C with a non-leaf τ₁), the key's verdict; at uncovered keys DLKey and the moves from P_Q |
| `k4/cover_indep.py` | second implementation: every lemma hypothesis re-coded from the written statements, with k4/rt4_n5_indep.py's states, deficits and move kinds; each claimed repair re-verified |
| `k4/cover_screen.c`, `k4/cover_screen_run.py` | C screen for profiles with a non-completable key at any f (k4/c4min.c's code; red.c's generator) |
| `k4/cover_inputs.py` | collects the explicit profiles of other workstreams' dumps and screens them |
| `k4/cover_hunt.py` | annealing hunt (least cover margin over the keys, rare-lemma bonus, uncovered keys, ZMOVE failures) |
| `k4/cover_uncovered.py` | every uncovered key: confirmation by `cover_indep.py`, the best move from each P_Q, DLKey, obstruction reasons |
| `k4/cover_failure.py` | the full detail of one failing profile |
| `k4/cover_summary.py` | the counts above |

## Reproduce

```
# PR #80's files in k4/suite/.cache/sx/ (see k4/cover_check.py's docstring), then:
sh k4/cover_validate_runs.sh NAME            # Phase 1; NAME in n3 n4a n4b n5 rc stuck1 cat stuck2 n5c
python3 k4/cover_inputs.py results/k4_cover/inputs/dumps_f2.jsonl.gz --f=2:99 FILES...   # the dumps (list in its log)
sh k4/cover_runs.sh; sh k4/cover_runs2.sh    # Phase 2 screens (n = 3: cover_screen_run.py on k4_certs_3, --rand=0)
sh k4/cover_runs.sh check NAME PARTS         # k4/cover_check.py on a screen's profiles
python3 k4/cover_check.py OUT INPUT --fmin=2 [--part=i/N] [--done=GLOB]                  # the dump checks
sh k4/cover_hunt_runs.sh NAME MINUTES [SEED] # Phase 3 hunts
sh k4/cover_final.sh                         # final_*.txt and uncovered_*.{jsonl.gz,log}
```
