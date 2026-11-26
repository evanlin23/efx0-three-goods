# Referee report: Lemmas D, F, S, U, BOTH-TP, Corollary TP (branch `claude/k4-sd-induct`, `k4/sd_induct.md`)

Referee: `proof/k4-referee`, 2026-11-26. Read: `k4/sd_induct.md` at `d244b6a`: §1 (Lemmas D, F), §3 (Lemma S,
Corollary TP, Lemma U), §5 (Lemma BOTH-TP) line by line. Also §7 (Lemma H, Proposition PR-step, Theorem PR-TP),
checked in passing as newer PROVED items, and `k4/sdc.md` §2 ((I1), (I2), Lemma 1).

Checks: `k4/referee/sdind_ref.py`, runs `k4/referee/sdind_ref_runs.sh`, logs `results/k4_referee/sdind_ref.log` and
`results/k4_referee/sdind_prtp.log`. They are written from the text; no code is shared with `k4/sdind/` or `k4/sdc/`.

## Verdicts

| item | verdict |
|---|---|
| Lemma D (deletion is SD-consistent) | CORRECT |
| Lemma F (a first agent is threatened only by the absorber) | CORRECT |
| Lemma S (exact EFX₀ condition for one-absorber completions) | CORRECT |
| Corollary TP | CORRECT. The hypothesis "o is not pick-frozen" is not needed: (S2) only concerns j ≠ o |
| Lemma U | **CORRECT WITH FIXES**: the statement lacks the hypothesis "f is unfrozen" that its title states. Item 3 is false without it (counterexample below). Items 1 and 2 hold as stated |
| Lemma BOTH-TP | CORRECT (it uses Lemma U only for an unfrozen agent) |
| (in passing) Lemma H, Proposition PR-step, Theorem PR-TP | CORRECT, with one wording point: "PR completion" must presuppose EFX₀ |

## 1. Lemmas D, F, S and Corollary TP

- **D.** Re-derived.
  - Agents before u had Y_u available and did not take it.
  - Agents after u never saw it.
  - So every other agent faces the same goods minus a good it did not take.
- **F.** Re-derived. f's singleton is never strongly envied. Removing a good from a non-absorber bundle (at most two
  goods) leaves one good of the instance, worth ≤ v_f(Y_f). So only B_o can threaten f.
- **S.** Re-derived.
  - Removing the junk good from {Y_j, g} gives (S2).
  - Removing Y_j leaves g, worth less than every valuer's pick by (I2), and 0 to pickless agents.
  - (S1) is EFX₀ toward X_o.
  - It is an exact characterization.
- **TP.** Re-derived. Pick-frozen agents are alone, so every two-good holder j ≠ o is unwanted, and
  v_i(Y_j) ≤ v_i(Y_i) ≤ v_i(X_i).

## 2. Lemma U: the missing hypothesis

The title says "an unfrozen first agent", but the statement only says "f first among the agents present". Items 1
and 2 hold as stated.
- Item 1: the case analysis g = b, c, d with c + d ≤ a + b and b + d ≤ a + c, and "at most one non-junk good (Y_o) of
  R_f in X_o".
- Item 2.

**Item 3** ("among the old agents, only o can become threatened") needs that no old agent i ≠ o has
v_i(a) > v_i(X_i), i.e. that f is unfrozen. Otherwise f's new bundle {a, g} threatens such an i.

**Counterexample** (`sdind_ref.py ucex`, first line of the log). Agents f = 0, i = 1, o = 2; goods a = 0, y_i = 1,
y_o = 2, b = 3, c = 4.
- Values: v_f = (10, 0, 0, 6, 5), v_i = (5, 3, 0, 0, 0), v_o = (0, 0, 4, 0, 0).
- Order (0, 1, 2) gives picks (0, 1, 2) and junk {3, 4}.
- X = (i: {1}, o: {2, 3, 4}) is an EFX₀ one-absorber completion of the others, and f is threatened by X_o
  (6 + 5 > 10).
- f takes b = 3. Now agent 1 (old, ≠ o) sees {0, 3} minus 3 = {0}, worth 5 > 3: threatened.

On random instances, item 3 failed in 4,746 of 7,185 cases with f frozen, and in 0 of 23,208 with f unfrozen.

**Fix.** Add "f is unfrozen (v_i(a) ≤ v_i(Y_i) for every other agent i)" to the statement, or weaken item 3 to "only
o and the agents with v_i(a) > v_i(X_i)". Every use I found has an unfrozen f:
- BOTH-TP (a both agent is unwanted);
- PR-step and PR-TP, which state (b) explicitly.

So nothing downstream changes.

## 3. Lemma BOTH-TP

Re-derived.
- The pick-frozen agents are the same with and without u: u holds its top and wants nothing, nobody wants Y_u, and
  the picks are the same by Lemma D.
- By Corollary TP only u's safety is new.
- If u is threatened, u takes its best junk good of X_o (Lemma U items 1 and 2, u unfrozen). The shape stays TP.
- Threats from X_o ∖ g are weaker than from X_o (removing a good is monotone), so (S1) still holds for everyone.

Correct.

## 4. In passing: Lemma H, Proposition PR-step, Theorem PR-TP (§7)

- **Lemma H.** Re-derived. The singletons and two-good bundles are unchanged, and values only rise (o's rises). The
  new absorber bundle X_o ∪ g_f lies inside every inflated set X_o ∪ g_{π₁} ∪ ⋯ ∪ g_{π_{k−1}} (k ≥ 2), whose
  threat-freeness PR already gives. The inflated sets of π° are those of π.
- **PR-step, case 2.** π_k's inflated set is unchanged for k ≥ 2. EFX₀ toward {Y_f, g} is (b). o's loss of g is
  (c) plus the o-part of (b). It is an exact "iff".
- **PR-TP.** Pick-unfrozen f gives (b). TP shape gives (c).
- **Wording point.** The definition reads "a one-absorber completion … is prefix-robust if …", followed by "every PR
  completion is EFX₀ (Lemma S: the other conditions do not involve X_o)".
  - The PR conditions concern only the inflated absorber bundle, so they do not imply Lemma S's (S2).
  - The definition is consistent only if "one-absorber completion" already means an EFX₀ one, as in `k4/sdc.md` §29
    and §1 of this file ("A(U) … one-absorber EFX₀ completions"). Lemma H and PR-step do prove EFX₀ of their outputs.
  - Saying "an EFX₀ one-absorber completion" in the definition would remove the ambiguity.
- **Computation.** Reverse-order insertion with the TP rule: 2,000 random instances, n ≤ 6, 8,000 runs. After every
  step whose agent is unthreatened or pick-unfrozen, EFX₀ and every PR condition were checked. 26,351 steps (2,051
  threatened unfrozen agents), 0 failures. 872 runs stopped at a threatened pick-frozen agent, the only failing step
  the theorem allows.

## 5. Computation for the listed lemmas (evidence)

Random additive instances with ≤ 4 relevant goods per agent and strict values; random orders; every absorber; every
one-absorber completion enumerated. All checks are by the raw EFX₀ definition.

| set | D | S | TP | F | U (f unfrozen): items 1/2/3 | U (f frozen): item 3 fails | BOTH-TP | failures |
|---|---|---|---|---|---|---|---|---|
| n = 3–4, m = 4–8 (5,000) | 17,536 | 382,795 | 195,511 | 163,270 | 12,845 | 2,068 / 3,316 | 117,578 | 0 |
| n = 5, m = 5–9 (1,500) | 7,500 | 557,180 | 168,196 | 270,098 | 7,525 | 2,447 / 3,289 | 172,366 | 0 |
| n = 2–3, m = 3–7 (3,000) | 7,514 | 53,968 | 35,425 | 18,833 | 2,838 | 231 / 580 | 14,135 | 0 |

("Failures" counts the stated lemmas: D, S, TP, F, U with its title's hypothesis, and BOTH-TP.)

## 6. For the coordinator

- Lemmas D, F, S, Corollary TP, Lemma BOTH-TP: CORRECT. They can be recorded as PROVED.
- Lemma U: CORRECT WITH FIXES. Put "f unfrozen" into the statement; the counterexample shows item 3 needs it. Its
  uses are unaffected.
- Lemma H, PR-step, PR-TP: correct as I read them, if "PR completion" is read as EFX₀ + PR. They were not on my list,
  so this is a lighter check.
