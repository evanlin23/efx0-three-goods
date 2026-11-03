# Other state spaces for DE4 (k = 4): which fail

Workstream `proof/k4-de4` (`k4/de4.md` §8, ledger K4.DE4.SS). After DE4 was refuted (`attempts/k4-de4.md`), state
spaces of the same kind were screened: the empty set, single goods and upper sets as in DE4, plus a choice of other
two-good holdings with their levels, and extra validity rules. Validity always includes (V1) and (V2) of `k4/de4.md`
§1; the order is the level sum, then value-Pareto; the claim tested is that every maximum has an EFX₀ completion.

Types of two-good holdings of a 4-good agent a ≻ b ≻ c ≻ d: the lower pair LP = {c, d} with v(b) < v(c) + v(d) < v(a);
CD = {c, d} with v(c) + v(d) < v(b); BC = {b, c} and BD = {b, d} worth less than v(a). Rules: (V3) a holder of its
lower pair has its b held by some agent; (V3f) its b is held alone by an agent.

The screen (`python3 k4/de4/ss_screen.py`, `results/k4_de4/ss_screen.log`): 168 instances, namely the DE4 and
tie-break counterexamples (A131, B131, C127, D3 of `attempts/k4-de4.md`), the GM₄ instances of
`k4/gm4_counterexample.py`, and the suite instances with n ≤ 5, m ≤ 11.

| variant | fails on (smallest) | no completable maximum at all |
|---|---|---|
| DE4 (LP at level 3) | A131 (n = 4, m = 7) | no |
| DE4 + (V3) | **none** | no |
| DE4 + (V3f) | D3 (n = 3, m = 6) | no |
| LP at level 2.5 (below b), with or without (V3) | D3 | no |
| no lower pair | D3 | no |
| BC, BD at level 3.5, no lower pair | induct-pot-nash (n = 3, m = 6) | on 7 instances |
| LP, and BC, BD at level 3.5 (with or without (V3)) | GM4-A (n = 4, m = 7) | yes, on GM4-A |
| LP at level 3.5 (above b) | A131 | yes, on A131 |
| LP, and CD at level 2.5 | A131 | no |
| DE4 + (V3), and CD at level 2.5 | **none** | no |

So the lower pair must stay at b's level, and two-good holdings containing b ({b, c}, {b, d}) make things worse. The
one change that removes every known failure is (V3), with the weaker condition "b held by some agent". Requiring b
to be held alone fails (D3). The two survivors are the subject of `k4/de4.md` §8 and ledger K4.DE4V3.

**Smallest failing configurations.** n = 3, m = 6 for (V3f), the lower pair at 2.5, no lower pair, and BC/BD
(profile D3; `induct-pot-nash`). n = 4, m = 7 for the others (A131; GM4-A).

**Replay.** `python3 k4/de4/refute_ss.py` (brute force from the definitions, no SAT, sharing no code with
`ss_screen.py`): for each failing variant, the stated maximum of its smallest instance is valid, no valid state is
better, and no assignment of the leftover goods is EFX₀ (`results/k4_de4/refute_ss.log`).
