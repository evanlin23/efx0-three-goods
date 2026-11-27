# Referee report: Lemmas 2, 2\*, Corollary 2.1, Proposition 3, Theorem F1₁ (branch `claude/k4-oc1-hall`, `k4/oc1_hall.md`)

Referee: `proof/k4-referee`, 2026-11-26. Read: `k4/oc1_hall.md` at `476207e`; §4–§6 are unchanged at `e2b4701` (22:15 UTC). §1 (Lemma 1), §4 (Lemma 2), §5
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

## 6. Addendum: Lemma MAX (new at `e2b4701`, §19; checked in passing)

Lemma MAX: if the picks form a maximum matching of the relevance graph, no agent reachable from a pickless agent by an
alternating path values a junk good, so no dangerous frozen agent is wanted (through want-chains) by a pickless agent.
- (1): such an agent with a junk good closes an augmenting path.
- (2): want arrows from a pickless agent form an alternating path. Want-chains are acyclic at SD picks.

**CORRECT.** It is a standard augmenting-path argument.

## Addendum: the RF residue proofs at n = 4, Lemmas RF-A1, RF-B, REPAIR-Y and Proposition RF-B4 (`k4/oc1_hall.md` §24.6, §24.8 on `claude/k4-oc1-hall` at `01f986d4`, PR #129; coordinator's priority item, 2026-11-27)

**Verdict: all four CORRECT.** Scripts `rfres_ref.py` and `rfb_rand_ref.py` (own code; nothing from `k4/oc1_hall/` run),
runs `rfres_ref_runs.sh`, log `results/k4_referee/rfres_ref.log`. Data: the certifier's n = 4 export
`two_move_starts_n4.json.gz` (sha256 `6159e38d…`): 112,880 starts and 292,080 failing orders.

**Lemma RF-B (any n).** Re-derived pair by pair.
- Every agent prefers its pick to every junk good. So S never threatens anyone but k, and everyone's value is at least
  its pick value.
- Z is handled as follows:
  - k by (B4): v_k(Z) − min ≤ p_k < v_k(S);
  - agents valuing ≥ 2 goods of Z by (B5);
  - every other agent through its single valued good: junk, Y′_d (unwanted, B3) or Y′_k (wanted only by d, B2).
- The chain (k, d) is official. d's completion takes Y′_d back plus J′ ∖ S, so d is the only absorber.

**Lemma REPAIR-Y (any n).** Re-derived.
- X_u = {Y_k, Y_u} threatens nobody: Y_u is unwanted, Y_k is wanted only by u, and k values Y_k below v_k(S).
- X_{k′} = {Y_{k′}, ℓ} threatens nobody: its wanters are only k and u, bounded by (F-k) and (R3).
- S and ℓ are junk.
- The chain (k, u) is official, and the completion gives u and k′ one good each.
- The contrapositive is sound. Y fails OC₁, and (R1), (R2), (F-k) and the wanter condition hold, so (R3)'s bound must
  fail. That is (U-b), strictly.

**Proposition RF-B4 (n = 4).** The structural remarks are re-derived:
- (B3) is RF-PATH (c);
- (B1) and (B4) follow from R_k = {Y′_k, Y′_{k′}} ∪ S;
- (B5) is void for k′;
- no two agents want each other's picks under SD;
- (B2) holds because the possible wanters of Y′_k are d, k′ and u, k′ does not want it, and u holds its top good;
- with (U-b), v_u(Z) − min ≤ v_u(Y_u) + v_u(Y_k) ≤ v_u(Y_{k′}) < v_u(t), which is (B5).

**Lemma RF-A1 (conditional).** Correct. I re-derived it **directly**, without Lemma 2\*, by checking every pair of the
completion X = (w: W = {Y_d} ∪ (J′ ∖ {h}), d: {g, h}, others their Y′-pick):
- *{g, h}* are junk of Y, by (A1-i) and since d takes junk. u holds Y_w, above Y_u and every junk good. w took Y_d at
  its σ′-turn while g and h were free. Everyone else keeps Y_a.
- *d vs W.* W ∩ R_d = {Y_d}. Since d is truly dangerous with J ∩ R_d = {g, h}, v_d(g) + v_d(h) > v_d(Y_d). A threat
  by a single junk good would contradict SD.
- *u vs W:* (A1-ii).
- *k2 vs W:* W ∩ R_{k2} ⊆ {x}, a junk good of Y′ (below p_{k2} by SD) or Y_d (unwanted, (A1-iii)).
- *Any other frozen q vs W.* Y_d is worthless to q by (A1-iv), and |W| ≥ 2. So the threat is
  v_q(J′ ∖ {h}) ≤ v_q(J′) − min_{J′} v_q ≤ p′_q, because D_T′ = ∅.
- |U′| = 1, so no unfrozen agent other than d remains.

**The n = 4 facts, recomputed with my own code** (receiver, RF order, SD, roles, threats, raw EFX₀):

| item | my count | Hall's |
|---|---|---|
| failing orders; unique receiver = the last picker | 292,080; at all | 292,080 |
| distinct RF starts: R2 / U1 / A / B | 161,520: 67,120 / 16,320 / 34,560 / 43,520 | the same |
| A1 (u → w → d, d takes junk) / A2 | 32,000 / 2,560 | 32,000 / 2,560 |
| A1: (A1-i), (A1-ii), (A1-iii), (A1-iv); the completion raw EFX₀ | 32,000 each; 32,000 | 32,000 |
| B: a unique candidate k (pick wanted by d only); w = d | 43,520; 43,520 | the same |
| B: (B1)–(B5), FULL(k, S) raw EFX₀ | 43,520 each; 43,520 | 43,520 |
| B: fact (a), "only u values two goods of Z", R_u = {t, Y_{k′}, Y_u, Y_k}, (U-b) | 43,520 each | 43,520 |
| REPAIR-Y at Y with \|J ∖ S\| = 1: (R1), (R2), (F-k) and the wanter condition hold; (R3)'s bound fails; the allocation is not EFX₀; (U-b) strict | 38,400; 38,400; 38,400; 38,400 | 38,400 |

**RF-B and REPAIR-Y as general lemmas** (random strict instances, n = 3–6, ≤ 4 goods, 300,000 SD starts):
- 12,365 (d, k, S) meet (B1)–(B5): **0** non-EFX₀;
- 35,369 (u, d, k, k′, S) meet (R1)–(R3): **0** non-EFX₀;
- *mutant* with (B5) dropped and (R3)'s bound dropped: 1,374 and 395 violations. So the hypotheses are needed and
  the test bites.

**For the campaign.**
- At n = 4, residues A1 and B have written proofs from facts that I re-certified independently on the export (single
  implementation before; now two). A2 is closed by enumeration.
- At general n, the open part is why the hypotheses hold: (A1-i)–(A1-iv), and (a) plus (U-b). At n = 5, RF-B covers
  only 61 % of DEMOTE-2 (Hall §24.9, not re-run here).

## Addendum: Lemma RF-B′ (`k4/oc1_hall.md` §24.10 at `7336e31c`; coordinator's queue, 2026-11-27)

**Verdict: CORRECT.** Its new content is (G2) at B′. The exactness is Lemma M^c, refereed CORRECT in
`oc1max_multi.md` §9, whose characterization needs only (G2) and allows multi-good bundles such as B′_k = S.

*(G2), re-derived.*
- The free goods at B′ are J′ ∖ S and Y′_d.
- Junk is below every pick value, and every value at B′ is at least the pick value.
- Y′_d is unwanted by every i ≠ d (the hypothesis), and v_d(Y′_d) = p_d < v_d(Y′_k).

*RF-B as the case o = d, H = F_s = ∅.* B′_k = S raises no τ_i, since each single junk good is below b_i. So "no needy
agent" means "Z threatens nobody", which is (B2), (B4) and (B5). Correct.

*Check* (`rfbp_rft_ref.py rfbp`; 40,000 random SD starts, n = 3–5; every unwanted d, every k whose pick d wants, every
improving S ⊆ J′ of size 1–3):
- 4,369 states, (G2) at all 4,369;
- 17,344 owner tests of my M^c formula (`mc_ref.py`) against the brute-force S^c test: 0 mismatches;
- 16,732 of the tests have an S^c completion.

Log `results/k4_referee/rfbp_rft_ref.log`.
