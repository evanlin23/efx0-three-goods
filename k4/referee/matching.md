# Referee report: Lemma M and Lemma EX (`k4/matching.md` §1, §3, branch `proof/k4-matching`, PR #116)

Referee: `proof/k4-referee`, 2026-11-26.
- Read: `k4/matching.md` at `2c0198e`, all of it (§0–§5); `attempts/k4-matching-deficiency.md` and
  `attempts/k4_matching_attempts.py` (for the instance data); `k4/sdc.md` §29 (definition of an improving chain) on
  `claude/kind-lamport-y8fdme`.
- Check: `k4/referee/matching_ref.py`, run by `k4/referee/matching_ref_runs.sh`, log `results/k4_referee/matching_ref.log`.
  It is written from the text and the raw EFX₀ definition, reusing only my own helpers (`oc1hall_ref.py`). No code from
  `k4/matching/` was run or imported.

## Verdict

| item | verdict |
|---|---|
| Lemma M (K4.MATCH.M), with the deficiency formula | **CORRECT** |
| Lemma EX (K4.MATCH.EX), with its matching form | **CORRECT** (a free strengthening is noted below) |
| §2: "δ ≤ 1 at perfect starts" refuted at k = 4 | **CONFIRMED** on the smallest instances (my brute force) |
| Conjecture CM | evidence only, as stated; not refereed as a proof |

## 1. Lemma M

Setting: a state B with
- (G1): no bundle of a non-holder threatens anybody at base values;
- (G2): no junk good is wanted.

Fix an owner o. Let N₁ be the holders other than o, Q the other agents, and X(H) = (B_o ∪ J) ∖ H.

- **(⇒)** Let H be the junk given to N₁ or to dummies.
  - (H1) holds, because Q receives nothing and the completion is EFX₀.
  - An exposed holder u must receive a good h, since X(H) threatens u at its base value. EFX₀ toward X(H) at the final
    value v_u(B_u) + v_u(h) gives v_u(h) > 0 and admissibility, so (u, h) is an edge.
  - A good given to an unexposed holder is always an edge.
  - These pairs form a matching covering E(H), with |H| − (dummy goods) ≥ |H| − d edges.
- **(⇐)** A matched holder's bundle is {b, h} or {h}, where:
  - b is unwanted because the holder is unfrozen;
  - h is unwanted by (G2).

  Such a bundle threatens i only if v_i(b) or v_i(h) exceeds v_i(X_i) ≥ v_i(B_i), which cannot happen.
  - Non-holders' bundles are unchanged and threaten nobody, by (G1) and since values only rose. Singletons never
    threaten.
  - X(H) is safe for Q by (H1), for exposed holders by the edge condition, and for unexposed holders by definition.
  - o is threatened by none of the above.
- **The formula.** The step needs a matching that both covers E(H) and has maximum size ν(Γ(H)). The Mendelsohn–Dulmage
  theorem gives one, applied to the vertex sets E(H) ⊆ N₁ and the H-side of a maximum matching.
  - Hence the least d for fixed H is |H| − ν(Γ(H)), and minimizing over H gives δ\*(B, o).
  - König–Ore (ν = |H| − max_{S⊆H}(|S| − |N(S)|)) gives the second form.
  - Restricting the min to H with E(H) coverable is right: for other H no d works.

Remark 1, that Lemma 2\* is the movable-holder refinement: consistent with my earlier report `oc1_hall.md` (Lemma 2\*).
Lemma M is the full-witness form, in which every exposed holder is matched.

## 2. Lemma EX

Setting:
- Y is a perfect start: SD picks, every agent with a relevant good picks.
- The chain is official: x_i (i ≥ 1) takes {y_{x_{i−1}}} ∪ H_i, and k takes H₀ ⊆ (J ∖ ∪H_i) ∪ {y_{x_t}}.
- The end: x_t is unfrozen at Y, or y_{x_t} ∈ H₀.
- o is any owner, and N, Ext, s and X are as in §3.

Each step re-derived:
1. **Values only rise.** Chain agents gain strictly; nobody else changes.
2. **N consists of holders of B′.** An agent off P is unfrozen at Y, so no i ≠ j has v_i(y_j) > p_i, and
   v_i(B′_i) ≥ p_i. Its bundle at B′ is still {y_j} or ∅.
3. **Every h ∈ H ⊆ J′ is unwanted at B′.**
   - J′ = (J ∖ (H₀ ∪ ∪H_i)) ∪ ({y_{x_t}} ∖ H₀).
   - For h ∈ J: (I2) of the SD picks gives v_i(h) ≤ p_i ≤ v_i(B′_i) for every non-null i, and null agents value nothing.
   - For h = y_{x_t} ∉ H₀: then x_t is unfrozen at Y, so no i ≠ x_t wants it at Y, hence none at B′. x_t itself has
     v_{x_t}(B′_{x_t}) > p_{x_t} = v_{x_t}(y_{x_t}). The text leaves this last point implicit in "values only rise".
4. **Ext agents hold one unwanted good.** This is the definition of an unfrozen single-good holder at B′.
5. **Bundles of ≤ 2 unwanted goods threaten nobody.**
   - Receivers: N agents hold ≤ 1 good, and Ext agents hold one.
   - Multi-good bases other than o's: by (G1′), at final values ≥ B′ values.
   - So only X can threaten.
6. **Coverage against X.** The case list is exhaustive:
   - F off P, by (1′) at pick value. This includes Ext agents off P, whose final value is ≥ their pick value.
   - P ∖ {o}, by (1′) at B′ value.
   - Exposed N, by their edge. Unexposed N, by definition.
   - Any remaining agent is off P, unfrozen at Y and ≠ o. At Y it holds ≤ 1 good, so it is a holder of Y in N.
   - o is threatened by nobody, by 5.
7. **Shape.** The receivers (N ∪ Ext) are holders of B′ and take ≤ 1 junk good each; everyone else takes nothing. So
   the allocation is S\*-shaped, hence one-absorber.
   - An S\* completion after one official chain is an OC₁ witness (`k4/sdc.md` §29: t ≥ 1, H₀ ⊆ J ∪ B_{x_t},
     H_i ⊆ J). So the implication "CM ⟹ OC₁ at perfect starts" is right.
   - The further steps to OC₁^max (Lemma RED) and TARGET₄ (Lemma MAXSD) are those lemmas' business. I refereed MAXSD
     (`maxsd.md`), not RED.

The **matching form** (d_o ≤ s_o) is the same Mendelsohn–Dulmage step as in Lemma M. The canonical remark also holds:
for o = k and no junk for x₁, …, x_t, B′_k ∪ J′ = J ∪ {y_{x_t}} = W_{x_t}.

**Free strengthening (optional).** Ext may also contain the chain agents unfrozen at Y (x_i with 1 ≤ i < t, and k if
unfrozen at Y) that are unfrozen single-good holders at B′. Steps 4–6 apply to them unchanged: they are covered against
X by (1′) as agents of P. This can only enlarge s. Checked below: 0 failures.

The identification "D = {k}, o = k, H = ∅ is Lemma D1-red" is a remark; I check it with the Hall session's §21–§22
(next item).

## 3. Computation (evidence)

**Lemma M.** States:
- SD picks of random instances: k ≤ 4, n = 2–5, m ≤ 9, a third with a shared pool (the K4.MC2-like design);
- up to three states one improving chain away from them, whenever (G1) and (G2) hold there.

For every owner and d = 0, 1, 2, the raw brute force (every placement of the junk among the owner, the holders ≤ 1 each
and ≤ d dummies; raw EFX₀) was compared with Lemma M's criterion (every H, its exposed set, admissibility, a matching
covering E(H) of size ≥ |H| − d):
- **513,753 tests, 163,221 of them after a chain: 0 mismatches.**

**Lemma EX.** Setup:
- 21,703 perfect starts, every official chain, every improving H₀, every owner, every H ⊆ J′;
- wherever (G1′), (1′) and (2) hold: every matching covering the exposed holders with ≥ |H| − s edges, with the rest of
  H to Ext in a random order;
- each allocation checked with raw EFX₀, exact coverage of the goods, and the S\* shape.

Results:
- **309,568 allocations (182,325 (chain, H₀, owner, H) tuples satisfying the hypothesis): 0 failures.**
- **Mutations**, each hypothesis dropped (3,000 instances each):

| hypothesis removed | failures / allocations |
|---|---|
| (G1′) | 26,969 / 97,150 |
| (1′), the P part | 5,399 / 64,552 |
| (1′), the F part | 1,321 / 62,633 |
| s replaced by s + 1 | 9,806 / 107,814 |

  So every hypothesis is used.
- Strengthened Ext (over F ∪ P): 89,068 allocations, 0 failures.

**§2 refutation.** My brute force reproduces the data for the four cases of `attempts/k4_matching_attempts.py`:

| instance | k | pick vector | SD? | δ, one absorber, per owner | δ\* (S\*) per owner | least δ after one chain | repairing chains |
|---|---|---|---|---|---|---|---|
| gap-ivsetting-n3-m6-n3c23 | 4 | (4, 3, 5) | yes | 2, 2, 2 | 2, 2, 2 | 0 | 13 of 30 |
| r36 | 4 | (4, 3, 5) | yes | 2, 2, 2 | 2, 2, 2 | 0 | 17 of 17 |
| PW5 | 5 | (0, 1, 2, 3, 4) | yes | 2 (all) | 2 (all) | 1 | 0 of 528 |
| RD5 | 5 | (1, 3, 4, 2) | yes | 2, 2, 1, 2 | 2, 2, 1, 2 | 1 | 0 of 28 |

So "δ ≤ 1 at perfect starts" is false at k = 4 (n = 3, m = 6), and RD5 has δ = 1 with no repairing chain, as stated.

## 4. For the coordinator

- Lemma M and Lemma EX: CORRECT; both can be recorded as PROVED.
- The refutation of "δ ≤ 1" (§2) is confirmed by an independent brute force.
- Conjecture CM stays a conjecture (evidence on 2,371 starts, not re-run here).
