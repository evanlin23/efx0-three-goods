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
