# Referee report: Lemmas 2, 2\*, Corollary 2.1, Proposition 3, Theorem F1₁ (branch `claude/k4-oc1-hall`, `k4/oc1_hall.md`)

Referee: `proof/k4-referee`, 2026-11-26. Read: `k4/oc1_hall.md` at `5a7a0d6`. §1 (Lemma 1), §4 (Lemma 2), §5
(Proposition 3, Theorem F1₁) and §6 (Corollary 2.1, Lemma 4, Lemma 2\*) line by line; the status block and §16 for
context. Also read the parts of `k4/sdc.md` the proofs call: §2 (I1, I2, Lemma 2), §6 (Theorem DT, (F1)–(F4), moves
(m1), (m2), DT⁺) and §30 (Lemma GDT, Theorem DT₁).

Checks: `k4/referee/oc1hall_ref.py`, runs `k4/referee/oc1hall_ref_runs.sh`, log `results/k4_referee/oc1hall_ref.log`.
They are written from the text; no code is shared with `k4/oc1_hall/` or `k4/sdc/`.

## Verdicts

| item | verdict |
|---|---|
| Lemma 2 (slot count, under (G1), (G2), (G5′), (H3)) | **CORRECT** |
| Lemma 2\* (exact count under (G1), (G2) only) | **CORRECT** |
| Corollary 2.1 ((H2) ⟺ an SDR of admissible holders) | **CORRECT**. One wording point: the gloss "a transversal of the demands" is exact only if read as (H1) |
| Lemma 4 (helpers) | CORRECT |
| Proposition 3 (T2⁺) | CORRECT |
| Theorem F1₁ (f = 1, one wanter, n ≥ 3) | **CORRECT**. Case (B2) rests on Theorem DT₁ and Lemma GDT (`k4/sdc.md` §30), both re-derived here and correct |

The campaign's own status notes that OC₁ itself is refuted at n = 6 (§16). Nothing here depends on OC₁. These are
statements about the completion problem at fixed bases.

## 1. Lemma 2

- **(⇐).** Re-derived.
  - Since |H| − ν(H) ≤ |N₁| − θ(H), the goods of H fit: ν of them to matched exposed holders, the rest to unexposed
    holders.
  - The unmatched exposed holders run DT's moves inside R′_i = {y_i} ∪ (W_o ∩ R_i), taking goods only from L = J ∖ H,
    one good each.
  - y_i is the top of R′_i: junk by (G2), goods of B_o by (G5′). So DT's (F4) applies there.
  - (H3) forces every danger set inside X_o, and the pair {b, c} of move (m2), to meet L: a danger set inside B_o
    would give |B_o ∩ R_i| ≥ 2 with v_i(B_o ∩ R_i) > v_i(B_i).
  - Termination uses DT's lexicographic potential.
  - Safety: matched holders by the choice of h (X_o only shrinks, and "threatened" is monotone in the set); unexposed
    holders since X_o ⊆ W_o ∖ H; Q by (H1). The two-good bundles {y_j, z} threaten nobody (y_j unwanted, z unwanted by
    (G2)), and Q's bundles threaten nobody by (G1).
  - Under (G2) and (G5′) an empty-base holder has R_i ∩ (J ∪ B_o) = ∅, so it is never exposed. This edge case is not
    mentioned but causes no problem.
- **(⇒).** With H the junk given to N₁: X_o = W_o ∖ H exactly, so the Q agents' safety is (H1). Every exposed holder
  needs its own slot good from H ∩ R_i to be safe, so ν(H) = θ(H) and (H2) reads |H| ≤ |N₁|.

## 2. Corollary 2.1, Lemma 4, Lemma 2\*

- **Corollary 2.1.** Unexposed holders are admissible for every good. So a maximum matching of H into N₁ has size
  min(|H|, ν(H) + |N₁| − θ(H)), and a full matching exists iff (H2). Correct.
- **Wording point.** "C(B, o): H is a transversal of the demands: it meets a good of every danger set, inside W_o, of
  every frozen agent and every multi-good holder (H1)". This is (H1) only if "danger set" means a set whose
  presence makes q threatened, i.e. T ⊊ W_o ∖ H, or T = W_o ∖ H with v_q(T) − min_T v_q > v_q(B_q).
  - Read literally ("every T ⊆ W_o ∩ R_q with v_q(T) > v_q(B_q)"), the transversal condition is stricter than (H1).
    Example: X_o = {y_o, b_q} ⊆ R_q with v_q(y_o) + v_q(b_q) > v_q(B_q) but max(…) ≤ v_q(B_q). Then q is not threatened,
    yet a literal transversal must keep b_q out.
  - Lemma 2 and the checks use (H1), so only the gloss needs the qualifier.
- **Lemma 4.** {B_i, h} robust inside B_i ∪ (W_o ∩ R_i) gives v_i(B_i) + v_i(h) ≥ v_i((W_o ∖ H) ∩ R_i), so i_h is
  admissible whether or not it is exposed. Correct.
- **Lemma 2\*.** Dropping (G5′) and (H3), the exposed holders that cannot run DT's moves are exactly the non-movable
  ones: they want a good of B_o (then y_u is not the top of R′_u), or they have a danger set inside B_o (then (m1)
  finds no good of L). Requiring the SDR to cover them, the (⇐) construction of Lemma 2 applies to the remaining
  unmatched exposed holders, which are movable.
  - (⇒) is as for Lemma 2: the slot goods form an SDR covering every exposed holder.
  - Under (G2), an exposed empty-base holder is always non-movable and can never be compensated (R_u ∩ J = ∅). That
    is consistent: no completion exists then.

  Correct.

## 3. Proposition 3, Theorem F1₁ and its dependencies

- **Facts (f1)–(f3).** Re-derived from "exactly one frozen agent".
  - x holds its top: otherwise it would want another pick, making a second frozen agent.
  - Every wanter ranks a first and its pick second.
  - A pickless wanter values only a.
  - No junk good and no pick other than a is wanted.
- **Proposition 3** is Lemma 2 with H = ∅ and Q = {x}. (H1) holds because v_x(W_o) = v_x(D_o) ≤ p_x. Correct.
- **(B2) = Theorem DT₁ + Lemma GDT.**
  - After the swap, x holds a pair worth more than any single good, w holds its top, a is unwanted, and the new junk
    Y_w is unwanted. So F = ∅.
  - (G3) holds for x: R_x ∖ H₀ is a (now w's base) plus at most one more good, since |R_x| ≤ 4.
  - GDT's proof: (F1′) and (F2′) hold; moves (m1) and (m2) inside R′_i find a good of L because at most one good of a
    danger set is y_o; frozen agents are safe by (G4) and pair holders by (G3).
  - Correct; the output has the S\* shape.
- **(B3).** No improving pair forces I(w) = L_x = {b, c, d} with b + c ≤ p_x < b + c + d.
  - Y_w ∈ L_x would make Proposition 3 apply to any o ∉ {x, w}, so L_x ⊆ J.
  - (B3a), nobody crowded: Lemma 2 at the swapped state with owner w and Q = {x}. Checked:
    - (G1): L_x threatens nobody, and w's value rose;
    - (G2), (G5′), (H3);
    - (H1): X_w ∩ R_x = {a}, worth less than L_x.
  - (B3b), i crowded with pair g ≻_i g′: owner o ∉ {x, i}, H = {g}.
    - (H1): X_o ∩ R_x ⊆ L_x ∖ {g}, a pair worth ≤ p_x.
    - {Y_i, g} is robust inside R′_i by (F4), since g′ ∈ R′_i lies below g, so i is admissible for g.
    - (H2) holds in both sub-cases.
  - Correct.

## 4. Computation (evidence)

- **States.** SD picks of random instances with ≤ 4 relevant goods per agent, strict and with ties, n = 3–5; plus
  up to two random improving-chain states from each start.
- **Owner tests.** For every owner, Lemma 2's count (when (G1), (G2), (G5′), (H3) hold), Lemma 2\*'s count (when
  (G1), (G2) hold) and Corollary 2.1's equivalence are each compared with a raw S\* brute force, which enumerates
  every placement and checks EFX₀ from the definition.
- **F1₁.** Every start with exactly one frozen agent, one wanter and n ≥ 3 is run through each claim of the proof
  separately:
  - Proposition 3's owner;
  - (B2): every owner outside {x, w}, after every improving-pair swap;
  - (B3a): owner w, after the swap to L_x;
  - (B3b): every owner outside {x, i}, for every crowded i;
  - the shape claim of (B3), and the theorem's conclusion.

| set | owner tests | Lemma 2 / 2\* / Cor. 2.1 tests | mismatches |
|---|---|---|---|
| random, n = 3–5, strict and ties (21,438 states) | 80,115 | 54,721 / 75,249 / 75,249 | **0 / 0 / 0** |

| F1₁ set | starts with f = 1, one wanter | Prop. 3 owner tests | (B2) owner tests | (B3a) | (B3b) owner tests | failures |
|---|---|---|---|---|---|---|
| random (above) | 4,176 | | 497 swaps | 9 | 4 cases | 0 |
| targeted (shared top), strict / ties | 17,645 / 22,757 | 34,803 / 58,168 | 15,263 / 12,321 | 21 / 162 | 183 / 60 | 0 |
| targeted at (B3), strict / ties | 53,232 / 48,108 | 91,683 / 82,422 | 6,093 / 5,046 | 9,558 / 10,185 | 65,970 / 50,685 | 0 |

**A note on my own first run** (`results/k4_referee/oc1hall_ref_firstrun_5goods.log`, kept for the record). The first version of my
"targeted" generator could give the wanter a fifth relevant good. On those (non-4-limited) instances, (B2) and
(B3b)'s specific owners failed, as they must: F1₁ uses (F4), which needs |R| ≤ 4, and (G3), which needs |R_x| ≤ 4. The
theorem's overall conclusion still held there. After restricting to ≤ 4 goods (with a guard that skips any instance
outside the hypothesis), there are no failures. So the hypothesis k ≤ 4 is used exactly where the proof says.

## 5. For the coordinator

- Lemma 2, Lemma 2\*, Corollary 2.1, Lemma 4, Proposition 3, Theorem F1₁ (with DT₁ and GDT): CORRECT. They can be
  recorded as PROVED.
- One wording fix: Corollary 2.1's gloss "transversal of the demands" should say that a demand is a set whose presence
  threatens (i.e. (H1)), not every set worth more than the base.
