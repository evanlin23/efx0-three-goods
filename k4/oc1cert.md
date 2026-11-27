# OC₁^max for every strict profile: ordinal CEGAR certification, and a refutation at n = 4

Workstream `compute/k4-oc1max-cert`. The question is Conjecture OC₁^max (K4.SDC.OC1MAX, `k4/sdc.md` §29 and §31),
asked for **every** strict profile of the small k = 4 cores (`results/k4_certs_{2,3,4,5}*.json.gz`), not for random
profiles. Code is in `k4/oc1cert/`, data in `results/k4_oc1max/`.

## 1. Results

**OC₁^max is false at k = 4, already at n = 4** (`results/k4_oc1max/oc1max_cex_n4.json`).
- It fails on 11 of the 1,002 n = 4 core hypergraphs (4_n4_3 idx 58 and 77; 4_pure idx 20, 21, 23, 24, 26, 29, 36,
  38 and 45). Nine have m = 7 and two have m = 8.
- Every failing (type profile, picks) pair was enumerated: the CEGAR runs to UNSAT with each failure blocked
  exactly. There are 80 to 46,080 per hypergraph:

  | hypergraph | 4_n4_3 #58 | #77 | 4_pure #20 | #21 | #23 | #24 | #26 | #29 | #36 | #38 | #45 |
  |---|---|---|---|---|---|---|---|---|---|---|---|
  | failing pairs | 1,280 | 80 | 46,080 | 2,560 | 640 | 40,320 | 640 | 1,440 | 6,400 | 12,800 | 640 |

  These are out of 288³·6 to 288⁴ (1.4·10⁸ to 6.9·10⁹) profiles, a density of about 10⁻⁵. That is why the random
  tests (1,500 random n = 4 profiles, K4.SDC.OC1) never met one.
- Every failing start is a **perfect start**: ν = 4 and every agent holds a pick.
- In every one, neither the picks nor any of the 20–51 states one official move reaches has any EFX₀ completion,
  **not even a free one** (any number of absorbers). So OC^max fails too, and so does OC₁ at perfect starts (the form
  Lemma RED reduces to).
- None of the 11 has an agent with two private goods, so all lie in the K4.MC2 class.
- Each failure is verified twice: `k4/sdc/oc1_mc2_rand.Inst.check` returns 'OC1 fails', and an own brute force from
  the raw definitions agrees (`k4/oc1cert/brute_verify.py`, `results/k4_oc1max/brute_verify_cex_n4.log`). That brute
  force enumerates every allocation and every one-move state, with no repository code.

Smallest example (4_n4_3 idx 58):
- relevant sets [[0,1,2,5],[1,2,5,6],[3,4,5,6],[3,4,6]];
- values [[2,10,4,7],[10,3,4,8],[3,5,6,7],[3,2,4]] (strict and balanced);
- order (0,3,2,1), and two other orders, give the picks 0←1, 3←6, 2←5, 1←2; the junk is {0, 3, 4}.

The mechanism:
- Agent 1 is left with its worst good (2, worth 3). It prefers each of the other three picks (worth 10, 4 and 8 to it)
  and values no junk good.
- So no other pick holder can take a junk good: removing the junk good leaves a pick agent 1 envies.
- Then agent 1 must absorb all the junk, and {2, 0, 3, 4} violates agent 2's EFX₀.
- No single move escapes this, as the exhaustive check above shows. The instance has 14 EFX₀ allocations, so TARGET₄
  is not affected.

**One pattern in all 11** (`diag.py` (c); "frozen" means some other agent prefers its pick, and a "danger pair" of
agent x is two junk goods worth more to x together than x's pick):
- exactly one agent is unfrozen, and the other three are frozen;
- two of the frozen agents share a single danger pair of junk goods;
- there are 3 or 4 junk goods.

In 6 of the 11 (58, 20, 21, 24, 36, 38) the unfrozen agent holds its worst good, prefers all three other picks and
values no junk, as in the example above.

This is the k = 5 mechanism of PW5 (`k4/sdc.md` §31: frozen agents sharing a junk danger set) at a smaller scale. It
does not need a large danger set, only a single available receiver. So the "k − 3 count" of §31 ("at k = 4 a danger
set has at most three junk goods, and one chain leaves at most one") does not by itself give OC₁^max at k = 4.

**Diagnostics on the 11** (`k4/oc1cert/diag.py`, `results/k4_oc1max/diag_cex_n4.log`; raw checker only):
- *Two moves repair every one.* 2–6 of the two-move states have a one-absorber completion, and the free completion
  gives the same counts.
- *An ∃-order form survives.* Under each failing profile, only 1–3 of the 24 orders fail, and every other order
  satisfies OC₁. All 24 orders give maximum matchings there.
- *The R1-priority order class fails too:* 2–3 of the 24 R1-priority orders fail on each of the 11.

**Every n = 4 failing start, exported** (`results/k4_oc1max/two_move_starts_n4.json.gz`, `k4/oc1cert/export_fails.py`):
- 112,880 (type profile, picks) pairs on the 11 hypergraphs, each with integer values, every order giving it, and its
  receivers;
- `Inst.check` gives 'OC1 fails' on all 112,880, and a raw two-move check on 2,261 sampled pairs repairs every one;
- the list is exactly complete: `check.py` with the pairs excluded confirms that every other pair is covered
  (`results/k4_oc1max/two_move_starts_n4_cert.json.gz`, `check_two_move_starts_n4.log`).
- **R2 at n = 4:** every one of the 112,880 has exactly one receiver (a pick holder whose pick nobody else prefers).
  So TTC's Conjecture R2 (`k4/ttc.md` §14.3: with at least two receivers, OC₁^max holds) is true at n = 4,
  exhaustively.

**The ∃-order form OC₁^∃max (K4.SDC.OC1EXMAX) holds for every strict profile on all 1,002 n = 4 cores.**
OC₁^∃max: some SD order's maximum-matching picks satisfy OC₁.
- On the 991 OC₁^max-certified cores it follows from that certificate and K4.SDC.MAXSD.
- On the 11 failing cores it is certified by `k4/oc1cert/exists.py`, an ∃-CEGAR over types only. Its entries
  (order, picks, repair) block the box of profiles under which that order gives those picks and that repair works.
  - Certificate: `results/k4_oc1max/exists_4_fail11.json.gz` (log `exists_4_fail11.log`).
  - Independent check: `k4/oc1cert/check_exists.py`, which uses check.py's own types, raw SD per order, raw move rules
    and raw EFX₀, and runs Glucose with one literal per agent mask (`check_exists_4_fail11.log`).
  - A dense engine with no SAT agrees with it on a sensitivity sample.
- n = 5, first 5_pure chunk (935 cores, stride 5 offset 0): OC₁^∃max holds for every strict profile on all 935.
  - 798 follow from their OC₁^max certificates, as above.
  - The other 137, every core of the chunk with an OC₁^max failure, are certified by `exists.py`
    (`k4/oc1cert/exists_n5.py`; `results/k4_oc1max/n5/exists_5_pure_s5o0.json.gz`, 230,031 entries, log
    `exists_5_pure_s5o0.log`).
  - Independent check: `check_exists.py` passes all 137 with 0 invalid entries (`check_exists_5_pure_s5o0.log`).
- **Which orders are good** (`k4/oc1cert/good_orders.py`, raw `Inst` code only).
  - What it does: at each failing start, it runs all n! SD orders, keeps the maximum-matching ones (ν picks) and
    groups them by pick vector. Each pick vector gets the raw OC₁ result, its orders, receivers, frozen agents and
    junk.
  - Chunk 1's 280 stored failing starts, at least one per failing core (`results/k4_oc1max/n5/good_orders_5_pure_s5o0.json.gz`,
    log `good_orders_5_pure_s5o0.log`):
    - Every start has 7–25 good pick vectors and 1–4 bad ones.
    - Every bad pick vector has exactly one receiver.
    - Every start has a pick vector with ≥ 2 receivers, and every such pick vector is good.
    - Every order that starts with the failing start's receiver is good.
    - The nearest good pick vector always differs from the failing one in exactly 2 agents.
    - The most frequent pick vector is good at 279 of the 280.
  - Every 50th start of the six partial exports, 14,045 starts (`good_orders_partial6_s50.json.gz`, `.log`):
    - every observation above holds at all 14,045;
    - here the most frequent pick vector is good at every start too.
  - The receiver-first rule is the coordinator's Conjecture RF (K4.SDC.RF).
    - From now on `run.py --depth=2` checks it at every OC₁^max-failing pair the CEGAR meets (summary field `rf`).
    - `rf_chunk.py` reruns the failing cores of chunks run before that.
    - `good_orders.py --rf` checks it at every start of an export.

**OC₁′^max (kgen-rounds' move, `kgen/rounds.md` §4.6 on proof/kgen-rounds) holds at n ≤ 4 and fails at n = 5.**
- The move: as OC₁'s, except that every non-end chain agent may also take goods of the end's base that it values.
- The generator (`cegar.py --prime`) agrees exactly with kgen-rounds' `one_chain_prime` on 400 random starts
  (`k4/oc1cert/xcheck_prime.py`, `results/k4_oc1max/xcheck_prime.log`). Their code has no rings; mine keeps the official
  rings.
- n = 4: certified for every strict profile on all 1,002 cores (`results/k4_oc1max/cert_4_prime.json.gz`), with an
  independent check (`check.py` with OC1_PRIME=1, `check_4_prime.log`). n ≤ 3 follows from OC₁^max.
- n = 5: 24 of the first 137 n = 5 OC₁^max failures (5_pure) have no OC₁′ repair, rings included.
  - All 24 are verified with kgen-rounds' own raw brute force (`one_chain_prime` + `completion`) and with `Inst` for
    rings (`k4/oc1cert/verify_prime_fails.py`, `results/k4_oc1max/oc1prime_cex_n5_partial.jsonl`,
    `oc1prime_cex_n5_verify.log`).
  - 13 are MC2-class; each is a perfect start.
  - Example: 5_pure idx 164, sets [[0,2,3,7],[1,2,6,7],[3,4,5,6],[3,4,5,7],[4,5,6,7]], values
    [[1,8,6,4],[4,8,2,7],[6,7,3,5],[7,10,2,6],[7,5,3,6]], picks (7,2,3,5,4).

**OC₂^max with S*-shaped completions holds for every strict profile on every core with n ≤ 4**
(`k4/oc1_hall.md` §2 on claude/k4-oc1-hall).
- The S* shape: one owner (any agent) takes any number of junk goods; an unfrozen holder of at most one base good takes
  at most one; every other agent takes none.
- Files: `results/k4_oc1max/cert_4_sstar.json.gz` and `cert_23_sstar.json.gz`, checked by `check.py` with OC1_SSTAR=1
  (`check_4_sstar.log`, `check_23_sstar.log`).
- One S* move suffices everywhere except at the starts of the 11 OC₁^max-failing cores, so the proof plan can stay
  inside S*.
- In the CEGAR, an S* witness fixes every pick and the owner, and carries each junk-receiving holder's "nobody wants my
  base" comparisons, which depend on the types.

**TTC's R2 forms at n ≤ 4** (`k4/ttc.md` §14.6 on claude/k4-ttc).
- The setting: perfect SD starts with no one-absorber completion of the picks and at least two receivers, over every
  strict profile of all 1,002 n = 4 cores. A receiver is a pick holder whose pick no other agent prefers.
- Code: CEGAR `--r2=…`, checker `OC1_R2=…`, raw brute force `k4/oc1cert/verify_r2.py`.
- A canonical chain starts at x₀ ∈ D (frozen, valuing junk), has x₁ preferring x₀'s pick to its own, follows the
  official rules and ends at a receiver.

| form | the chain, then | n = 4 cores where it fails |
|---|---|---|
| R2-C | any one-absorber completion | **none: certified** (n ≤ 3 too; row K4.SDC.R2C.N4) |
| R2-O′ | one absorber, owner a receiver other than the end, or no owner | 9 |
| R2-O, generous | owner a receiver off the chain, or no owner | 9 (the same) |
| R2★ | nobody takes two junk goods | 230 |
| (S) or (L) | (S), or (L): a middle agent dangerous at the start takes junk and some middle agent is a receiver; then any one-absorber completion | 48 |
| R2-E | the chain is the earliest-wanter chain E(k) of some SD order giving the start; k takes an improving T | 273 |
| (S) | no junk past the head (x₁, …, x_t take only the previous base), then any one-absorber completion | 273 |
| R2-M | S^c with owner x₀, max_rest 1 | 306 |
| R2-O, strict | owner a receiver off the chain (one must exist) | 308 |

All 9 R2-O′ failures, 20 R2-M failures and the first R2-E failure are re-verified by `verify_r2.py`.
So are all 48 "(S) or (L)" failures (`results/k4_oc1max/r2sl_fails_n4.jsonl`, `verify_r2sl_fails_n4.log`, one start
per core): at each of them R2-M, R2★, generous R2-O, R2-O′ and R2-C repair, and strict R2-O and R2-E fail.

**OC₁^max holds for every strict profile on**:
- every core with n = 2 (5) and n = 3 (51);
- 991 of the 1,002 n = 4 cores.

**OC₂^max holds for every strict profile on every core with n ≤ 4.** OC₂^max: the picks, or the bases after at most
two official moves in sequence, have a one-absorber completion. That is 1,058 hypergraphs.
- Only 36 two-move witnesses are needed in all n = 4 runs, so the failing region is small.

| n | cores | OC₁^max certified | OC₁^max fails | OC₂^max certified | certificate | independent checks |
|---|---|---|---|---|---|---|
| 2 | 5 | 5 | 0 | 5 | `cert_2.json.gz` | SAT checker; exhaustive brute-force coverage; raw `Inst` on every profile, no certificate |
| 3 | 51 | 51 | 0 | 51 | `cert_3.json.gz` | SAT checker; exhaustive brute-force coverage (1.8·10⁹ profile × order pairs); raw `Inst` on every profile, no certificate, on the 33 cores with ≤ 6·10⁵ profiles |
| 4 | 1,002 | 991 | 11 | 1,002 | `cert_4.json.gz` (depth 1), `cert_4_depth2.json.gz` | SAT checker on both |
| 5 | 31,584 | see §4 | | | | |

## 2. Method (`k4/oc1cert/cegar.py`)

Every comparison OC₁ needs is between disjoint sets of goods:
- SD picks compare single goods;
- an improving condition compares a new base with a disjoint old base;
- EFX₀ compares X_i with X_j minus a good.

So the statement depends on a profile only through the agents' strict balanced order types (K4.OT: 6 for 3 goods,
288 for 4, with (C4) for two-private agents). The question per hypergraph is a 2QBF: does some (types τ, picks Y)
exist such that every repair fails? It is solved by CEGAR.

- **Outer SAT (CaDiCaL)** over one-hot types and one-hot picks:
  - Y is a matching with ν picks.
  - Y is an SD outcome under τ. Every good an agent prefers to its pick (every relevant good, if it has none) is
    picked, and the digraph "i prefers Y_j to Y_i" is acyclic. A reverse topological order then produces Y.
  - Every witness found so far fails at (τ, Y).
  - Type comparisons enter through comparison bits [v_i(A) > v_i(B)], one per pair of disjoint sets, as in the hunt
    session's ordinal CEGAR (`claude/k4-hunt-cegar`, `k4/hunt.md`).
- **A witness** is (F, Y\*_F, B′_F, imp, X):
  - the agents F that the move or moves touch, with their picks;
  - their final bases;
  - the improving comparisons;
  - a complete allocation X containing the final bases.

  It repairs every (τ, Y) with:
  - Y = Y\* on F;
  - Y_j ∈ X_j (or no pick) off F;
  - at most one agent holding two or more goods of X outside its final base;
  - all comparisons true under τ, and X EFX₀ under τ.

  Given the first two conditions, the goods the moves add are junk at Y: they lie in movers' X bundles, and every
  other pick lies in its holder's bundle. So the same moves are legal from Y and produce the same bases on F. The
  negation is one clause over pick literals, comparison bits and pairs of pickless agents. One witness therefore blocks
  every (τ, Y) it repairs, across matchings as well as types. Automorphism images are added too.
- **Inner search.** It takes the integer representative of τ and works as follows:
  - an incremental SAT solver for one-absorber EFX₀ completions, with type and base assumptions;
  - the picks first;
  - then every official move (additions, chains that never hand on an empty base, rings; the rules of
    `oc1_mc2_rand.Inst.moves`);
  - with `--depth=2`, then every second move.

  The most general witnesses (largest type volume) are kept.
- **Output.** If the outer is UNSAT, the hypergraph is certified. The certificate keeps an UNSAT core of the witness
  clauses. If the inner finds nothing, the pair is re-checked at once with `Inst` (`run.py`).

Sanity check: with the maximum-matching constraint removed, the CEGAR finds a failing non-maximum start on the TTC
n = 5 core in about a second, and `Inst` confirms it.

## 3. Independent checks

- **`k4/oc1cert/check.py`** (SAT, Glucose 4) shares no code with the CEGAR. For every maximum matching Y separately
  (found by brute force), it asks whether some type profile and some order π satisfy SD(π, τ) = Y with no witness
  repairing.
  - Types: its own enumeration of the grid [1, 16]^d by sign vectors, giving 6 and 288.
  - SD is encoded through π itself: a strict total order, and every preferred good held by an earlier agent.
  - Witness legality is re-derived from the concrete Y by the raw move rules. EFX₀ and the improving conditions are
    evaluated raw on integer representatives.
  - The types an agent's masks treat alike are merged, which is an exact reduction.
  - The witnesses' recorded picks are used only to skip witnesses, which is sound.
- **`k4/oc1cert/brute.py cover`** (n ≤ 3, no SAT) checks every profile explicitly:
  - for every Y and order, the SD region is a box over the types, and so is each witness;
  - the union of the witness boxes is computed densely (boolean matrix products);
  - every region box must lie inside it.
- **`k4/oc1cert/brute.py raw`** (no certificate) runs the coordinator's raw checker `Inst.check` on every SD outcome
  of every order, for every profile. It is limited to profile spaces ≤ 6·10⁵.
  - It covered all 5 n = 2 cores and 33 of the 51 n = 3 cores: 7.4·10⁶ profiles, 0 failures
    (`results/k4_oc1max/brute_raw_2_3.log`).
  - The other 18 n = 3 cores (1.2–2.4·10⁷ profiles each, about 10 CPU-hours) are covered by the two checks above.
- **`k4/oc1cert/test_check.py`** (sensitivity): certificates with one witness dropped are usually rejected (they
  are UNSAT cores, not minimal ones); certificates with every X perturbed are always rejected. Where both checkers
  run, the SAT checker accepting implies the brute force accepting. The converse can fail, because the brute force
  does not use the picks filter.

## 4. n = 5

The run is in progress: `k4/oc1cert/n5_driver.sh`, at depth 2 (OC₂^max), in chunks of about 1,000 hypergraphs.
- A depth-2 run also locates every hypergraph where OC₁^max fails. The inner search uses a second move only at a
  (profile, picks) pair where no single move works, and every such pair is re-checked with `Inst`.
- Per chunk, `results/k4_oc1max/n5/` gets:
  - the run log and the summary (every hypergraph's result and statistics, without witnesses);
  - the independent check log;
  - the certificates of the hypergraphs where OC₁^max fails, plus every 50th certificate.
- The full certificates (about 340 MB) are not committed. The CEGAR is deterministic (fixed seeds), so
  `n5_driver.sh` regenerates them, about 7 h on 4 CPUs.
- Measured on a 161-hypergraph sample (stride 200): every one is OC₂^max-certified, 3.3 CPU-s per hypergraph, and 5
  of the 161 need a second move somewhere.
- The pure 4-good list is much slower: about 35 min per 500 hypergraphs on 4 CPUs. The run order is therefore
  5_n4_1 (done), 5_pure, 5_n4_4, 5_n4_3, 5_n4_2.
- Positive control: the TTC session's n = 5 OC₁^max counterexample (outside MC2) is 5_pure idx 280 (m = 9), in
  chunk 5_pure_s5o2.
- Done so far, each with an independent check:
  - 5_n4_1 (1,735 cores) and chunk 5_pure_s5o0 (935 cores): OC₂^max is certified for every strict profile on all of
    them.
  - 137 of those 935 pure cores have OC₁^max failures. Every recorded failing start is perfect, has exactly one
    receiver, and gives 'OC1 fails' under `Inst`.
- The checker was made about 10× faster at n = 5 (an exact bitset prefilter of witnesses by picks, and mask literals)
  and regression-checked on every n ≤ 4 certificate.
- Two-move starts of six chosen 5_pure cores (`results/k4_oc1max/n5/two_move_starts_n5_partial6.json.gz`):
  - 702,250 starts, from partial lists cut at 7 min per core;
  - every one has exactly one receiver;
  - 28,093 raw-checked, all 'OC1 fails', and 7,024 sampled two-move raw checks, all repair.
- **Complete** two-move start lists of 5_pure (m = 10) idx 419, (m = 11) idx 447 and (m = 9) idx 38, the RSD-IND and
  REC-S cases (`results/k4_oc1max/n5/two_move_starts_n5_sel2.json.gz`, input `two_move_starts_n5_sel2_input.jsonl`,
  log `two_move_starts_n5_sel2.log`):
  - The counts: 276,480, 115,200 and 192,000 starts. Each is one (type profile, picks) pair, stored as a valuation
    representing the types.
  - Every start has exactly one receiver.
  - Every 50th start was raw-checked: all 11,674 give 'OC1 fails', and 2,919 sampled two-move raw checks all repair.
  - Completeness: `two_move_starts_n5_sel2_cert.json.gz` is an OC₁^max certificate of the three cores with exactly
    these pairs excluded, and `check.py` checks it (`check_two_move_starts_n5_sel2.log`).

## Reproduce

```
python3 k4/oc1cert/run.py 2 --out=results/k4_oc1max/cert_2.json.gz                         # < 1 s
python3 k4/oc1cert/run.py 3 --out=results/k4_oc1max/cert_3.json.gz                         # ~5 s
python3 k4/oc1cert/run.py 4_n4_1,4_n4_2,4_n4_3,4_pure --out=results/k4_oc1max/cert_4.json.gz              # ~5 min, 4 CPUs
python3 k4/oc1cert/run.py 4_n4_1,4_n4_2,4_n4_3,4_pure --depth=2 --out=results/k4_oc1max/cert_4_depth2.json.gz   # ~6 min
python3 k4/oc1cert/check.py results/k4_oc1max/cert_4_depth2.json.gz --lists=4_n4_1,4_n4_2,4_n4_3,4_pure   # ~2 min
python3 k4/oc1cert/brute.py cover results/k4_oc1max/cert_3.json.gz                         # ~1 min
python3 k4/oc1cert/brute.py raw 2,3 --maxprof=600000
python3 -I k4/oc1cert/brute_verify.py < cex.jsonl          # one {"sets", "vals", "picks"} per line
python3 k4/oc1cert/diag.py                                  # the diagnostics on the 11 counterexamples
python3 k4/oc1cert/test_check.py results/k4_oc1max/cert_3.json.gz 25 1
```
