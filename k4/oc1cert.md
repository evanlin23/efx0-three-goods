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

**Diagnostics on the 11** (`k4/oc1cert/diag.py`, `results/k4_oc1max/diag_cex_n4.log`; raw checker only):
- *Two moves repair every one.* 2–6 of the two-move states have a one-absorber completion, and the free completion
  gives the same counts.
- *An ∃-order form survives.* Under each failing profile, only 1–3 of the 24 orders fail, and every other order
  satisfies OC₁. All 24 orders give maximum matchings there.
- *The R1-priority order class fails too:* 2–3 of the 24 R1-priority orders fail on each of the 11.

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
