# The faithful LSS algorithm on degree-≤ 4 instances with short cycles

Workstream `proof/k4-girth` (`k4/girth.md` §1–§2). **Approach:** run Algorithms 1–3 of Lianeas–Sgouritsa–Sotiriou
(arXiv 2608.03171, Theorem 1, girth ≥ 4) unchanged on TARGET₄ instances that have 2-cycles (two agents sharing two goods)
or 3-cycles, and see whether the output is still EFX₀.

**Result.** It often is (about 70–80% of runs on the k = 4 screen set and on random strict profiles of the n = 2, 3
cores), but not always, and on some instances no choice of vertex 0 or labeling works (`k4/girth.md` §2). Each failure
is the break of one girth use G1–G6 (`k4/girth.md` §1.4). The implementation records the first step that creates
strong envy, and also the step at which Algorithm 3's line 2 makes its receiver *envied* (not strongly), which Lemma 3.5
excludes with Obs. 2.1 and which later sends that receiver's leftovers to X_0 (`A3L4:G5env`).

**Smallest failing configurations found** (random search, `k4/girth/smallest.py`; vertex 0 = agent 0, default labels;
choices: largest label, smallest good), agent: {good: value}:

| girth use | n, m | instance | what happens |
|---|---|---|---|
| G1 (Alg. 2 line 4) | 3, 5 | {0:2, 3:1}, {0:2, 1:1, 2:1, 4:2}, {1:1, 2:1, 3:3, 4:3} | agent 2 takes U_2 = {1, 2, 4}; agent 1 shares goods 1 and 2 with it and strongly envies |
| G5 (Alg. 3 line 2) | 2, 4 | {0:2, 1:2, 2:1}, {0:1, 1:1, 2:1, 3:2} | the two agents share three goods; line 2 orients a shared good to the non-envied agent, whose bundle the other already values |
| G5, receiver envied | 3, 6 | {0:4, 1:3}, {2:1, 3:4, 4:3, 5:3}, {0:2, 1:2, 2:2, 3:1} | line 2 gives good 2 to agent 1, now envied by agent 2 (goods 2, 3 shared); agent 1's private goods 4, 5 go to X_0 = {1}; agent 1 values {1, 4, 5} at 6 > 5 |
| G6 | 2, 4 | {0:3, 1:1}, {0:2, 1:2, 2:1, 3:1} | vertex 0 and agent 1 share goods 0, 1; agent 1 holds one, X_0 the other |
| G3 | 3, 5 | {0:4}, {0:1, 1:3, 2:2}, {0:2, 1:3, 3:1, 4:2} | agents 1, 2 both share good 0 with vertex 0 and share good 1 with each other |
| G4 | 3, 5 | {1:1, 2:2, 3:1}, {0:3, 2:2}, {0:2, 1:2, 4:1} | a triangle 0–1–2 (linear) |

G2 (a multi-good bundle of a neighbour of 0 envied without strong envy) never appeared as the first cause in these
searches. On linear instances every failure is G4 (`results/k4_girth_faithful.log`).

**Reproduce:** `python3 attempts/k4_girth_attempts.py` (part 1).
