# Referee report: PW5, OC and OC₁ fail at k = 5 (branch `claude/k4-ksens`, `k4/ksens.md` §1–§2)

Referee: `proof/k4-referee`, 2026-11-26. Read: `k4/ksens.md` at `ceba5c7` §1–§2 (unchanged at `cebd30a`) (and the status block, Lemma PL's
statement). Definitions: `k4/sdc.md` §29 (improving chain, OC, OC₁). Check: `k4/referee/pw5_ref.py`, log
`results/k4_referee/pw5_ref.log`, written from the instance table alone; no code shared with `k4/ksens/`.

## Verdict: CORRECT (one aside to tighten)

PW5 is an instance with n = 5, m = 9 in which every agent values at most five goods. From the order π = (x₁, x₂, x₃,
w₁, w₂), neither the picks nor any state one improving chain (`k4/sdc.md` §29, t ≥ 1) reaches has a complete EFX₀
completion, even a free one. So OC, and with it OC₁, fails at k = 5. Since PW5 is k-limited for every k ≥ 5, both
fail for every k ≥ 5. I re-derived the case split and found it complete for §29 chains.

## 1. The proof, step by step

- **Step 1** (who gains) is right.
  - An x values only its own p and D. No other base contains its p, so a gaining x needs ≥ 2 goods of D (each is
    worth < 10, any two ≥ 13).
  - A wanter values only the p's and its q, and nothing in D.
  - Every agent's pick base is nonempty, so every chain agent after x₀ receives a nonempty base.
- **Step 2** is right. An off-chain wanter with no p has value 1 and wants every p, so each x still holding its p is
  alone with value 10, and then no bundle of ≥ 3 goods may hold two goods of D.
- **Step 3.** |S| ≤ 2 since |D| = 4. Each case is right, including where the released goods go:
  - |S| = 0: no chain is possible. The four goods of D overfill the two wanters.
  - |S| = 2: the non-head member holds a received base plus a pair.
  - |S| = 1, t ≥ 1: the chain is {x_a, w} in one of two orders.
    - w first: x_a holds {q_w} plus a pair. The junk then contains no p, so w′ holds no p.
    - x_a first: q_w is released, w = {p_a}, and the remaining two goods of D must go to w′.

  In every case the off-chain wanter really holds no p, because no p is ever released into the junk.
- **The t = 0 aside** ("x alone keeps p_x and adds goods of D") covers only additions. A one-agent move may also
  drop p_x for a pair of D, releasing p_a into the junk, and the text does not argue that variant. It is not needed:
  §29's chains have t ≥ 1, and the claim does not depend on it. It is also true: my enumeration includes every
  one-agent replacement H₀ ⊆ J ∪ B_{x₀}, and none of the 78 such states from π extends. Suggested fix: either drop the
  t = 0 sentences, or add "if x drops p_x, then p_a is junk; give it to a wanter and argue as in x_a = x₀, or to
  anyone else and that bundle is threatened".

## 2. Computation (independent; exhaustive)

All 5⁹ complete allocations were enumerated: 186 are EFX₀ (raw definition). For each of the 120 orders, a start
*extends* if some of them contains every base. For the starts that do not, every §29 chain is enumerated, and every
one-agent move (t = 0) as well, and each resulting state is tested.

| result | |
|---|---|
| distinct starts | 19 |
| starts whose picks extend | 12 |
| starts repaired by one chain | 6 |
| starts where OC fails | **1**: π = (0, 1, 2, 3, 4), picks (0, 1, 2, 3, 4) |
| chain states from π (t ≥ 1) / t = 0 moves | 528 / 78; **none extends** |

This agrees with the session's numbers: 19 starts, π the only failing order, 7 starts needing a chain, 6 of them
repaired by one.

## 3. Section 2 (what k ≤ 4 buys)

§2 is an explanation, not a theorem. Its count is correct for PW5's design. One repair consumes two goods of D,
the repaired agent must be the head x₀, and the other |D| − 2 goods need one-good slots. A frozen agent with k
relevant goods has a pool of at most k − 1 junk goods, so k − 3 are left over. Lemma PL, which states this in
general, was not on the referee list and is not refereed here. The k = 4 analogue PW4 holding OC₁ is the session's
computation, not re-run here.

## 4. For the coordinator

- PW5: CORRECT. "OC and OC₁ fail for every k ≥ 5" can be recorded as REFUTED-with-artifact. The artifacts are the
  written proof (§1) and two independent exhaustive checks (the session's and `pw5_ref.py`).
- Optional tightening: the t = 0 aside of the proof (§1 above).
