# Referee report: Lemma C13, the RF class (1, 3) at n = 5 (`k4/ttc.md` §14.8, branch `claude/k4-ttc`)

Referee: `proof/k4-referee`, 2026-11-27.
- **Read:** `k4/ttc.md` §14.8 at `699cc115` (PR #125): the data facts, the two-bin trade, Lemma C13 with its proof,
  and the coverage. Also girth's citation of the form (`k4/girth.md` §7, "(1, 3)", on `claude/k4-girth`), and the
  definitions the lemma uses:
  - OC₁ and the improving chain: `k4/sdc.md` §29;
  - (I2): `k4/oc1_hall.md` §1, quoting `k4/sdc.md` §2;
  - "receiver": `k4/ttc.md`, top ("pick holders nobody values above their own pick").
- **Check:** `k4/referee/c13_ref.py` (`c13_ref_runs.sh`), with logs `results/k4_referee/c13_ref_*.log`.
  - The code is my own, with raw EFX₀. Nothing from `k4/ttc/`, `k4/girth/` or `k4/sdc/` is run or imported.
  - The certifier's n = 5 exports (`two_move_starts_n5_partial6.json.gz`, `two_move_starts_n5_sel2.json.gz` on
    `compute/k4-oc1max-cert`) and girth's list (`results/k4_girth_rf_n5_class13.jsonl.gz`) are read as data.

## Verdict: CORRECT WITH FIXES (one missing hypothesis)

The proof is correct, and the n = 5 coverage is confirmed. The statement, however, omits a hypothesis that the proof
uses: **(0) d is a receiver at Y′, i.e. no agent other than d wants Y′_d.** Without (0) the lemma is false, by the
three-agent counterexample below. (0) holds at all 7,733 starts (d is the unique receiver at Y′), so the n = 5
conclusion stands.

## 1. The proof, step by step

The setting is a perfect SD start Y′ with junk J′ and p_i = v_i(Y′_i). The allocation is:
- X_w = H ∪ {x};
- X_d = {Y′_w, Y′_d, y};
- X_i = {Y′_i} for every other agent.

It is complete: the picks plus J′ = H ∪ {x, y}.

- **Own values.** v_w(X_w) ≥ v_w(H) > p_w by (1), and v_d(X_d) ≥ v_d(Y′_w) > p_d by (1). Every other agent has
  v_i(X_i) = p_i. So p_i ≤ v_i(X_i) for all i, with strict inequality for w and d. Correct.
- **Singletons.** X_j ∖ g = ∅ for every other agent j. Correct.
- **X_w, against i ≠ w.** (3) gives v_i(X_w ∖ g) ≤ p_i ≤ v_i(X_i) for every g ∈ X_w, including goods i values at 0.
  - This includes i = d.
  - The "automatic" clause is correct: X_w ⊆ J′, so if i values at most one good h of X_w, then
    v_i(X_w ∖ g) ≤ v_i(h) ≤ p_i by (I2).
- **X_d, against i ≠ d.** By (4), i values at most one good h of X_d, so v_i(X_d ∖ g) ≤ v_i(h) for every g. It
  remains to show that every good of X_d is worth at most p_i to i:
  - **Y′_w:** by (2), for i ≠ w. For i = w, v_w(Y′_w) = p_w. Correct.
  - **y:** by (I2), since y ∈ J′. Correct.
  - **Y′_d:** the proof says "because d is a receiver". Neither the setting nor (1)–(4) states this. It is exactly
    (0). Under (0), each such v_i(h) ≤ p_i ≤ v_i(X_i), and the step is correct.
- **It is an OC₁ move.** Take x₀ = w with H₀ = H ⊆ J′ ∩ R_w and v_w(H) > p_w, and x₁ = d with H₁ = ∅ and
  v_d(Y′_w) > p_d. This is an improving chain of `k4/sdc.md` §29 with t = 1, and the passed base {Y′_w} is nonempty.
  The released Y′_d joins the junk. In the completion, w takes x and d takes {Y′_d, y}, so d is the only agent taking
  two or more junk goods: a one-absorber completion. So OC₁ holds at Y′. Correct.

**The fix.** Add **(0) no agent other than d wants Y′_d (d is a receiver at Y′)** to the setting. Equivalently,
extend (2) to "d is the only agent that wants Y′_w, and nobody but d wants Y′_d". Nothing else changes. In the
"Open" item, (0) comes with the class at n = 5: there U′ = {d}.

## 2. The counterexample without (0) (`c13_ref.py cex`, `c13_ref_cex.log`)

The instance has three agents w = 0, d = 1, i = 2 and goods a = 0, b = 1, c = 2, h₁ = 3, h₂ = 4, x = 5, y = 6. Values
are strict (distinct subset sums for each agent), k = 3, and every good is valued by someone:

| agent | a | b | c | h₁ | h₂ | x | y |
|---|---|---|---|---|---|---|---|
| w | 10 | 0 | 0 | 6 | 5 | 0 | 0 |
| d | 10 | 5 | 0 | 0 | 0 | 0 | 1 |
| i | 0 | 10 | 5 | 0 | 0 | 1 | 0 |

- SD(w, d, i) = (a, b, c), a perfect start with J′ = {h₁, h₂, x, y}, and (I2) holds.
- **(1):** H = {h₁, h₂} ⊆ R_w, worth 11 > 10, and d wants a = Y′_w.
- **(2):** only d wants a.
- **(3):** d values nothing in X_w = {h₁, h₂, x}, and i values only x.
- **(4):** w values only a in X_d = {a, b, y}, and i values only b.
- **(0) fails:** i wants b = Y′_d.
- **The allocation is not EFX₀:** ({h₁, h₂, x}, {a, b, y}, {c}) has v_i(X_d ∖ a) = 10 > 5 = v_i(X_i). The chain is
  official and the completion has one absorber, so it is exactly the lemma's allocation.

The random test (§4) finds the same failure mode: 50 of 737 cases with (0) dropped are not EFX₀, the smallest at
n = 3.

## 3. The n = 5 coverage (`c13_ref.py build`, then `check`; `c13_ref_build.log`, `c13_ref_check.log`)

**Regeneration.** For every exported start (1,285,930 starts, 9 hypergraphs), every listed order o and every receiver
u at Y, I set Y′ = SD(u, o − u) with my own SD. I kept the distinct (sets, vals, Y′) with a perfect Y′ and classified
them by (|U′|, |D_T′|), where:
- U′ is the receivers at Y′;
- D_T′ is the frozen agents with v_i(J′ ∖ h) > p_i for some h ∈ J′.

| distinct perfect RF starts | (1, 0) = DEMOTE-0 | (1, 2) | **(1, 3)** | R2 | U1 | not perfect |
|---|---|---|---|---|---|---|
| 1,526,623 | 113,484 | 140,111 | **7,733** | 1,262,513 | 2,782 | 3,460 |

These are girth's and Hall's numbers exactly. My 7,733 class-(1, 3) starts are **the same set** as girth's list:
7,733 in common, none on one side only.

**The data facts of §14.8**, all confirmed at all 7,733:
- the RF path is u → w → d (length 2), with Y′_w = Y_d;
- U′ = {d}, d values no good of J′, and d wants Y′_w;
- w ∈ D_T′ and u ∉ D_T′;
- |J′| = 4;
- w has exactly one improving junk pair, whether pairs are restricted to R_w or not;
- every EFX₀ split of (J′ ∖ H) ∪ {Y′_d} between w and d gives w exactly one good of J′ ∖ H.

**The lemma** at every start:
- (1), (2), (4) and (3) in value form hold for some (H, x, y) at 7,733 of 7,733;
- (3) holds in its simple form at 7,248, and only in value form at 485;
- **(0) holds at 7,733**;
- the allocation is raw EFX₀ at 7,733;
- the move is an official chain followed by a one-absorber completion at 7,733.

**The 485 value-form cases.** At each one, exactly one agent other than w values two goods of X_w. That agent is in
D_T′, values a good of H, and its two goods sum to less than its pick. In the example, the goods of X_w are worth
0, 2 and 6 to that agent, against p = 10. This matches the note's "2 + 6 < 10".

**One count to correct.** "At 7,248 of the starts, {x, y} is valued exactly by the other two truly dangerous agents"
holds at **all 7,733**. `c13.py` tests it only inside the simple-form branch, so the 485 value-form starts are not
counted. The fact itself holds there too.

## 4. The lemma at any n, random (`c13_ref.py rand`; `c13_ref_rand_*.log`)

Setup:
- random SD starts, n = 3 to 6, m = n + 4, k ∈ {3, 4, 5}, ties allowed in half of them;
- every (w, d, H, x, y) with (1) is collected.

Results:
- **With (0)–(4)** ((3) in value form): no allocation fails raw EFX₀. There are 687 cases at 14,425 perfect starts
  (seed 1), and 7,129 cases at 144,566 perfect starts (seed 2).
- **Mutants:** dropping any one hypothesis produces non-EFX₀ allocations, each time already at n = 3. Seed 2 counts:

  | hypothesis dropped | cases | not EFX₀ |
  |---|---|---|
  | (0) | 7,427 | 298 |
  | (2) | 7,977 | 848 |
  | (3) | 8,920 | 1,515 |
  | (4) | 16,793 | 5,847 |

  So each hypothesis is used, and the checker can find failures.

## 5. What the rest of the campaign uses

Girth's `k4/girth.md` §7 cites C13 for the (1, 3) form at n = 5. That use is covered: (0) holds there. Any later use
of C13 beyond the n = 5 data has to check (0), or derive it, along with (2)–(4).
