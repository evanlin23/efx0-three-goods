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
python3 k4/rf_indep/rf_check.py --data $D --orig all --orig-py 100      # about 20 min on 4 CPUs
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

All rotation vectors are among the u-first vectors above, so they all satisfy OC₁, as Hall found.

**OC₁ at the failing starts themselves.** The search answers F at all 1,285,930 export starts, agreeing with the
certifier. 100 per hypergraph were re-checked by the pure-Python search, which also gives F.

**What this does and does not establish.**
- This is EVIDENCE for RF at n = 5. The partial lists are not all failing starts of their hypergraphs, and n = 5 has
  many other cores.
- For #38, #419 and #447 the check covers every failing (type profile, picks) pair. That relies on two things not
  re-derived here: the certifier's completeness flag, and the type reduction, under which SD, receivers, maximality and
  OC₁ compare only single agents' subset sums.
