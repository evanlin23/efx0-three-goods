# Referee report: Lemma D1-chain, Proposition 3′, Lemma D1-red, Lemma D1-C₀, Proposition D1-C′, and the §22 counterexamples (`k4/oc1_hall.md` §21–§22, branch `claude/k4-oc1-hall`)

Referee: `proof/k4-referee`, 2026-11-26.
- Read: `k4/oc1_hall.md` at `a14932d`, §21 and §22 in full, plus Lemma 2\* (§6) and Lemma MAX (§19), which they call.
- Check: `k4/referee/hall21_ref.py`, run by `hall21_ref_runs.sh`, log `results/k4_referee/hall21_ref.log`. It is written
  from the text and the raw EFX₀ definition, reusing only my own helpers (`oc1hall_ref.py`, `multi_ref.py`). No code
  from `k4/oc1_hall/` was run or imported.

## Verdict

| item | verdict |
|---|---|
| Lemma D1-chain | **CORRECT** (second part via Lemma MAX (2), refereed CORRECT in `maxsd.md`) |
| Proposition 3′ (K4.OCH.D1POOL) | **CORRECT** |
| Lemma D1-red (K4.OCH.D1RED), Remarks 1–2 | **CORRECT** |
| Lemma D1-C₀ (K4.OCH.D1FAV) (a), (b) | **CORRECT** |
| Proposition D1-C′ (K4.OCH.D1CP) | **CORRECT** |
| §22: cex1, cex2 (n = 4) and the TTC n = 5 instance refute OC₁^max | **CONFIRMED** by my brute force |
| Sub-lemmas D1-H, D1-C, D1-LONG, D1-HJ | not proofs; D1-LONG and D1-H(ii) are recorded as refuted (D1H-X), not re-checked here |

These are lemmas about a fixed state, so §22's refutation of OC₁^max does not touch them, as the note says.

## 1. Re-derivation

**D1-chain.**
- k is frozen, so some x₁ wants Y_k; while x_i is frozen, some x_{i+1} wants Y_{x_i}.
- By (π) each wanter comes later in π, so the agents are distinct and the walk ends at an unfrozen x_t. Only "k
  frozen" is used, so the walk works for any |D|.
- At a maximum-matching start, Lemma MAX (2) says every agent on a want-chain above a dangerous agent holds a pick.

**Proposition 3′.** Lemma 2\* at the picks with owner z and H = ∅:
- (G1): singletons only.
- (G2): (I2), and pickless agents value no junk.
- (H1):
  - a frozen q ≠ k values no junk, by (D). So W_z ∩ R_q ⊆ B_z, a single good worth ≤ p_q since z is unfrozen. Here
    the value bound is stated, so "a single good" is used correctly;
  - k is covered by the assumption v_k(W_z ∩ R_k) ≤ p_k.
- No non-movable holder: B_z is unwanted, and |B_z| ≤ 1.

This gives an S\* completion, contradicting hardness.

**D1-red.** Every step was checked:
1. **(G1), (G2) and the strengthened (G2).** By (I2) and (U); for x_t, p_{x_t} < v(a).
2. **Frozen agents.**
   - An off-path agent unfrozen at the picks stays unfrozen.
   - F ∖ {k} values at most Y_{x_t} in Π, worth ≤ p_q by (U), so it is never threatened.
   - The wanters of a at B′ are off P, by (π) and the gains. So x_t is frozen at B′ iff a has a second wanter off P at
     the picks.
   - k wants no chain pick.
3. **Exposed and non-movable holders.** Exposed holders are x_t or unfrozen off-path agents. Non-movable means crowded,
   using Lemma 2\*'s definition (|B_o ∩ R_u| ≥ 2 and v_u(B_o ∩ R_u) > v_u(B_u)) with B_o = H₀.
4. **The condition.** (H1) becomes (H1′), and HEAD and CROWD are exactly the obstacles at H = ∅.

Remark 2 is also right: a frozen second wanter w continues the walk, and by (π) P_w has ≥ t + 1 steps.

**D1-C₀.**
- (a) u holds a pick. Y_u ∉ Π, so |Π ∩ R_u| ≤ 3. The ≤ 2 goods other than b_u are each worth ≤ v_u(b_u) and
  ≤ p_u (by (I2) and z unfrozen). So any subset of Π ∖ {b_u} is worth ≤ v_u(b_u) + p_u.
- (b) Lemma 2\* at the picks with owner z and H = {b_u}, each b_u matched to its u.
  - Admissibility comes from (a). Here the condition that b_u ∈ J is needed, since Lemma 2\*'s H lies in the junk.
  - k is unthreatened because Π_k ∖ H is worth ≤ p_k.
  - So an S\* completion would exist, contradicting hardness.

**D1-C′.**
- Without HEAD, (H1′) holds for every H, by monotonicity.
- The holders that H₀ ⊆ Π_k can crowd are x_t or off-path unfrozen agents valuing ≥ 2 goods of Π_k, i.e. agents of
  U′. Frozen agents value at most Y_{x_t} in Π.
- The matching:
  - each crowded u ∈ U′ takes its favourite b_u, which is in J′ because H₀ avoids B(U′), and is admissible by
    D1-C₀ (a);
  - a crowded head takes Y_{x_t}, which is in J′ because Y_{x_t} ∉ H₀ by hypothesis. It is admissible because
    (Π ∖ H) ∩ R_{x_t} is ≤ 2 junk goods, worth < 2p_{x_t} < p_{x_t} + v(a).
- The goods are distinct, and D1-red (4) applies.

Correct. It uses |R| ≤ 4 at both counts (|Π ∩ R_u| ≤ 3, two junk goods for the head) and D = {k} through (D). The
note's later remark that D1-C′ needs |D| = 1 (T3) is consistent with this.

## 2. Computation (evidence)

Starts: SD picks of random strict instances (k ≤ 4, n = 2–5; random 4-sets and sparse sets), kept when one-absorber-hard
(raw brute force, every owner) with D = {k}. Perfect and non-perfect starts are both included.

| claim | tests | failures |
|---|---|---|
| D1-chain: a canonical chain from k exists | 17,028 starts | 0 |
| D1-chain: at maximum-matching starts every head holds a pick | 13,969 starts | 0 |
| Proposition 3′ (every unfrozen z) | 18,832 | 0 |
| D1-C₀ (a): \|Π ∩ R_u\| ≤ 3, u holds a pick, every S ⊆ Π ∖ {b_u} safe at p_u + v_u(b_u) | 2,724 agents | 0 |
| D1-C₀ (b): every U″ with distinct favourites in J | 1,818 | 0 |
| D1-red 1, 2 (including "x_t frozen iff a second wanter off P", "k wants no chain pick"), 3 | 42,857 chains (every improving H₀) | 0 |
| D1-red 4: brute-force S\* owned by k ⟺ some H with (H1′) and an SDR covering the crowded exposed holders | 42,857 | 0 mismatches |
| D1-red: no HEAD, no CROWD ⟹ S\* owned by k | 39,503 | 0 |
| D1-C′: a minimal improving H₀ ⊆ Π_k ∖ B(U′) exists | 17,766 chains | 0 |
| D1-C′: every such H₀ (not both crowding the head and containing Y_{x_t}) ⟹ S\* owned by k | 28,938 | 0 |

These come from 1,050,000 instances, 2,147,152 starts and 126,879 hard ones, of which 17,028 have |D| = 1.

**§22, by brute force** (one-absorber completions over every owner, raw EFX₀).

| instance | strict | picks (as printed) | perfect, ν | F / D | hard | one-chain states completing | t = 0 additions completing | first chains with a repairing second chain |
|---|---|---|---|---|---|---|---|---|
| cex1 (n = 4) | yes | (1, 2, 5, 6) ✓ | yes, 4 | {0, 2, 3} / {0, 2, 3} | yes | 0 of 9 | 0 | 4 |
| cex2 (n = 4) | yes | (4, 5, 6, 2) ✓ | yes, 4 | {1, 2, 3} / {1, 2} | yes | 0 of 16 | 0 | 7 |
| TTC n = 5 | yes | (4, 6, 0, 5, 1) ✓ | yes, 5 | {1, 2, 3, 4} / {1, 3, 4} | yes | 0 of 21 | 0 | 16 |

So each instance:
- is a perfect, maximum-matching start;
- has no one-absorber completion at the picks or after any improving chain (`k4/sdc.md` §29: every t ≥ 1, every choice
  of the sets H), nor after a t = 0 addition;
- is repaired by two sequential chains.

OC₁^max is refuted at n = 4, and the "two moves" statement of §22 is confirmed. I did not check the R1-priority remark,
whose order definition is in `k4/sdc.md` §2.

## 3. For the coordinator

- D1-chain, Proposition 3′, D1-red, D1-C₀ and D1-C′: CORRECT. They can be recorded as PROVED.
- §22's cex1 and cex2 (and the TTC n = 5 instance) are confirmed counterexamples to OC₁^max by an independent brute
  force, each repaired by two chains.
