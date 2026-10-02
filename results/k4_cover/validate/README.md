# Phase 1: k4/cover_check.py on PR #80's and PR #82's inputs (compute/k4-cover)

Made by `k4/cover_validate_runs.sh` (one name per run) from the copies of origin/proof/k4-sx in `k4/suite/.cache/sx/`.
Summaries: `summary_f1.txt`, `summary_f2.txt` (`k4/cover_summary.py`; f >= 2 with `--nodedup`, as k4/f2_cc.py counts).
These runs used the checker before `lemma_c_nonleaf` was added (Lemma C with a θ-b terminal τ₁ that is not a leaf), so
they reproduce PR #80's own semantics; the later runs include that case.

| input | ours | PR #80 / PR #82 |
|---|---|---|
| f = 1, n = 3, every strict profile | 62,208 keys, 116,248 maxima: first lemma A 104,372, B1 7,824, C 4,052; uncovered 0 | the same (k4/sx.md §4.2) |
| f = 1, n = 4 hunts (n4_3_r40k, n4_pure_r40k, n4_pure_r400k) | 2,661 keys, 4,210 maxima: A 3,884, B1 193, B1′ 18 (+2 exact only), C 78 (+2 exact only), C′ 33; uncovered 0 | 2,661 keys; A 3,884, B1 193, B1′ 18 (+3), C 78 (+2), C′ 32: one maximum moves from B1′x to C′ because PR #80's post-review sx_zprime (commit bfa0f99) tests C′ when τ₁ is not a leaf, and its zprime logs predate that commit |
| f = 1, n = 5 hunts | 11 keys, 13 maxima, all A | the same |
| f = 1, compute/k4-rc's 45 profiles | 45 keys, 45 maxima, all A | the same (k4/sx.md §4.4) |
| f = 1, T1-stuck profiles | 1,241 keys, 1,756 maxima: A 1,133, B1 80, C 539, C′ 4 | the same (k4/sx.md §4.3) |
| f >= 2: n = 4 catalogues and hunts / T1-stuck / compute/k4-rt4-n5c | 67 / 196 / 26 keys = 289; A⁺ or B⁺ at some maximum: 18 / 156 / 19 = 193; only C⁺/C′⁺: 49 / 40 / 7 = 96 (174 maxima); uncovered 0 | the same (k4/f2.md §5) |

Deficits: every min-frozen state's Lemma H1 deficit (k4/dl2_classify) was checked against k4/suite/model.py's direct
removal-only deficit (`--verify`, every profile), and the whole deficit table against k4/rt4_n5_indep.py on the n = 5
inputs (`--indep`). `results/k4_cover/indep/validate_*.log`: k4/cover_indep.py (a second implementation of every
lemma test, from the written statements, with k4/rt4_n5_indep.py's deficits and move kinds) agrees at all 639 f >= 2
maxima and at 896 of 897 sampled f = 1 maxima; the one difference is Lemma C with a non-leaf τ₁ (see above).
