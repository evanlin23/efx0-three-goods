# k = 4: CEGAR counterexample search for TARGET₄ (workstream proof/k4-hunt)

Angle: settle TARGET₄ negatively if it is false, by a complete search per core instead of random or adversarial
profiles. For a fixed k = 4 core H, decide whether some strict balanced type profile (equivalently, by K4.OT and
K4.MC0(c), some valuation with these relevant sets) admits **no** complete EFX₀ allocation. Status of everything here:
see "Results" (each claim names its artifact; nothing in LEDGER.md is changed by this workstream).

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

## Reproduce

```
python3 k4/hunt/run.py 6 10 --n4=2 --jobs=3 --tag=n6_m10_n42          # ~1 h on 3 CPUs
python3 k4/hunt/check.py results/k4_hunt/n6_m10_n42_p0of1.json.gz --sat-sample=50
```
