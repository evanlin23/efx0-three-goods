# Referee report: twins' RF-minimal-counterexample note (`k4/RFMIN.md`, PR #156, branch `proof/k4-rf-min` at `d32e566d`)

Referee: `proof/k4-referee`, 2026-11-27 (coordinator's queue item 2).
- **Read:** `k4/RFMIN.md` §1–§7 line by line; the four new ledger rows (K4.RF.MINCLASS, K4.RF.TOP, K4.RF.ABS,
  K4.RF.CENSUS); and the statements the proofs cite:
  - LEDGER rows K4.MC0–MC9, K4.R3–K4.R6a, K4.SDC.MAXSD and K4.SDC.RF on main;
  - `k4/sdc.md` §31 (RF and its amendment);
  - `lean/EFX/RF.lean` on main (`ConjRFWith`).
- **Checks:** `k4/referee/rfmin_ref.py` and `k4/referee/norecv_ref.py` (`rfmin_ref_runs.sh`); logs
  `results/k4_referee/rfmin_ref_*.log` and `norecv_ref_*.log`.
  - The code is my own, with raw EFX₀. Nothing from `k4/rfmin/` is run.
  - The certifier's exports (n = 4 complete; n = 5 partial6 and sel2) are read as data.

## Verdicts

| item | verdict |
|---|---|
| Proposition RF-𝒦 | **CORRECT WITH FIXES.** The proof needs a receiver at the OC₁-failing start. RF as amended ("for every receiver u …") no longer asserts one, and the Lean `ConjRF` asserts one together with uniqueness, which K4.SDC.R2.N5 contradicts. A short lemma (REC-∃, below) supplies existence, so the proposition holds with the amended RF. The cited reductions say what is used. |
| Lemma RF-TOP, Corollaries RF-TOP and RF-PRIV | **CORRECT.** |
| Lemma ABS, Corollary ABS | **CORRECT.** k ≤ 4 is used exactly where stated. |
| Census (§4) | **CONFIRMED.** Every count is reproduced. |
| §6 RF-PRIV status, §7 transfer to RKMAX | Correct as stated: the proved and open parts are delimited correctly. |

## 1. Proposition RF-𝒦

**The class.** Each condition is backed by the cited row. I checked each against the ledger statement:
- β ≥ 5: K4.MC7 (TARGET₄ for β ≤ 4), with K4.MC0 (a minimal counterexample is one connected core).
- n ≤ 3(β − 1): K4.MC4.
- n ≥ 6: K4.MC0 gives n ≥ 5 with three 4-good agents if n = 5, and K4.R5c, R5d and R5p settle three, four and five
  4-good agents.
- At least two 4-good agents if n = 6: K4.MC0 gives at least one, and K4.R6a settles exactly one.
- No agent with two private goods: K4.MC2. 𝒦 states only "no PP4", a weaker condition, so 𝒦 is a superset; harmless.
- No P3–P3 degree-2 good: K4.MC3.
- px profiles: K4.MC5. Double edges: K4.MC8. No claw: K4.MC9.

All of these are stated for "a minimal counterexample (fewest agents, then goods)", the same order the proof uses. The
strict-type reduction (K4.MC0) and type invariance of OC₁ and of the set of SD vectors make "RF on 𝒦" (on type
profiles) apply to H.

**The step that needs a fix.** "Otherwise RF gives a receiver-first order with maximum-matching picks at which OC₁
holds." This needs a receiver u of the failing start Y. Two current readings of RF:
- *As amended* (`k4/sdc.md` §31, and ledger K4.SDC.RF: "for every receiver u of a failing start, some order with u
  first gives a maximum matching and every such order satisfies OC₁"). The clause is vacuous at a start with no
  receiver, so RF gives nothing there.
- *In Lean* (`ConjRFWith`): `∃ u, (Receiver u ∧ ∀ u', Receiver u' → u' = u) ∧ …`. This has existence, but also
  uniqueness. At the four n = 5 two-receiver starts of K4.SDC.R2.N5 (OC₁-failing, maximum-matching, strict connected
  cores; coordinator's replay `r2_n5_cex_check.log`, not re-replayed here), uniqueness fails, so **`ConjRF` as
  formalized is false**. The docstring says "only the second and third parts
  of RF are used", but the proof takes u from the first part's existence claim. Only uniqueness is unused.

**Lemma REC-∃ (referee; proof below).** Take any instance, ties allowed, with SD index tie-breaking, and Y = SD(σ) a
maximum matching. If Y has no receiver, then:
- some agent is pickless;
- no agent values a good of J;
- the picks, plus all of J given to one pickless agent, form an EFX₀ one-absorber completion.

So OC₁ holds at Y, and **every OC₁-failing maximum-matching start has a receiver.**

*Proof.*
1. *A pickless agent exists.* Otherwise the last agent ℓ of σ holds a pick, and every other agent i had Y_ℓ free at
   its turn, so v_i(Y_i) ≥ v_i(Y_ℓ). Then ℓ is a receiver.
2. *Wanter chains end at pickless agents.* Let j hold a pick, and let i be a pick holder with v_i(Y_j) > v_i(Y_i). Then
   Y_j was not free at i's turn, so j precedes i in σ. Since Y has no receiver, every pick holder j₀ has a wanter j₁.
   If j₁ holds a pick, it has a wanter j₂, and so on, with strictly increasing positions in σ. The chain ends at a
   pickless agent p that values the last pick.
3. *An alternating path.* p – Y_{j_k} – j_k – Y_{j_{k−1}} – … – j₁ – Y_{j₀} – j₀ is an alternating path from the
   unmatched agent p: each agent values the next good, and each Y_{j_t} is matched to j_t. If j₀ valued a junk good g,
   adding g would give an augmenting path, contradicting maximality. This is Lemma MAX, `k4/oc1_hall.md` §19.
   So no pick holder values junk.
4. *Pickless agents.* They value no junk (SD2: junk was free at their turn).
5. *The completion.* Give J to one pickless agent p₀. Its bundle is worth 0 to everyone, and every other bundle is a
   singleton or empty. So the allocation is EFX₀, with p₀ the only agent holding two or more goods. ∎

With REC-∃, the amended RF suffices for Proposition RF-𝒦 and for "RF ⟹ OC₁^∃max". The Lean frame can then drop
uniqueness, and with REC-∃ formalized, even the existence clause.

*Check* (`norecv_ref.py`; random strict connected instances, every agent valuing 3–4 goods, all orders):

| instances | n | MM starts | without a receiver | … junk valued by someone | … OC₁ fails |
|---|---|---|---|---|---|
| 253,023 | 3–5 | 1,217,682 | 352,478 | 0 | 0 |
| 16,890 | 6 | 239,397 | 68,780 | 0 | 0 |

Every no-receiver start has a pickless agent and completes at the picks. On the certifier's exports, every stored
failing start has exactly one receiver (table in §4).

**Not re-run:** the n = 6 candidate counts (`twins_count.py … --mc9`). They size the hunt list; the proof does not use
them.

## 2. Lemma RF-TOP and its corollaries

**The lemma, re-derived.** σ′ = (u, σ − u), with u holding its top Y_u.
- u takes Y_u first, since its top good is free at the start.
- Induct along σ − u. If u precedes a in σ, a sees the same taken set in both orders.
- Otherwise a's σ′-free set is its σ-free set minus Y_u ≠ Y_a, so a's favourite is unchanged.
- A pickless agent sees fewer free goods, so it stays pickless.

Correct, with no receiver hypothesis.

**The corollaries.**
- *Corollary RF-TOP.* σ′ is then a u-first order with the same maximum-matching picks, which RF's universal clause
  forbids at an OC₁ failure. Correct.
- *Corollary RF-PRIV.* An agent f whose top good p is private takes p: it is free at f's turn, since only f values it.
  And f is a receiver, since nobody else, pickless agents included, values p. Correct.
- *"Certified at n = 4"* follows from the completeness of the n = 4 export together with the data below.

*Check* (`rfmin_ref.py top`): on 100,000 random instances, 301,271 cases of a top-holder moved to the front, picks
unchanged at all of them. The mutant (a non-top holder moved to the front) changes the picks at all 69,334 cases, as it
must: that agent then takes its top.

## 3. Lemma ABS

**Re-derived.** The construction is:
- each receiver r ≠ f, in any order, takes its best free junk good if the free junk is worth more than Y_r to it;
- f takes the rest.

The steps:
- *Facts used.* (SD1) junk ≤ pick for pick holders; (SD2) pickless agents value no junk.
- *{Y_r, g_r} against i ≠ r.* The threat is max(v_i(Y_r), v_i(g_r)) ≤ v_i(Y_i): r is a receiver, and pickless agents
  "prefer" any good they value, so they value Y_r at 0. Correct, including for i = f.
- *X_f against i ≠ f.* Y_f is private, so the minimum over X_f is 0 and the threat is v_i(F).
  - Pickless i: 0.
  - Frozen i: v_i(F) ≤ v_i(J) ≤ p_i by hypothesis.
  - A receiver that took nothing: F ⊆ the free junk at its turn, which was worth at most p_r to it.
  - A receiver that took g_r: **|R_r| ≤ 4** leaves at most two valued junk goods in F, each below both Y_r and g_r. So
    v_r(F) < v_r(Y_r) + v_r(g_r).
  - Correct.
- *One absorber.* Only f gets two or more junk goods. Correct.

**Corollary ABS** is the contrapositive of ABS. Correct.

*Checks* (`rfmin_ref.py abs`; random SD starts, strict values, receivers taken in random order):

| run | full hypotheses | frozen hypothesis dropped | f not private |
|---|---|---|---|
| k ≤ 4, 200,000 starts | **172,923 cases, 0 failures** | 19,972 of 21,999 fail | 314,761 of 603,647 fail |
| k ≤ 5, 100,000 starts | 107 of 56,170 fail | 9,786 of 11,206 fail | 157,379 of 305,124 fail |

At k = 5, **all 107 failures are the predicted mechanism**: a receiver with five goods that took a junk good, against
X_f, valuing three junk goods of X_f. This matches the note's "2 of 1,054".

## 4. Census (`rfmin_ref.py data`)

| | n = 4 (complete) | n = 5 partial6 | n = 5 sel2 |
|---|---|---|---|
| failing starts | 112,880 | 702,250 | 583,680 |
| receivers per start | 1 at all | 1 at all | 1 at all |
| receiver: 4 goods, none private (Q4) / one private (P4) | 110,080 / 2,800 | 611,070 / 91,180 | 468,480 / 115,200 |
| receiver holds its top | 0 | 0 | 0 |
| receiver's pick private | 0 | 23,779 | 115,200 |
| some agent's top good private | 0 | 0 | 0 |
| some agent holds a private good | 0 | 23,779 | 115,200 |
| ABS's two hypotheses together | 0 | 0 | 0 |

Every number in RFMIN §4 and the ABS row is reproduced. In total, 138,979 = 23,779 + 115,200 starts have a
private-good holder, and it is always the receiver. The receiver-first class table was not recomputed here. It ranges
over every u-first order, not only the rotations (u, o − u) of listed orders, so its counts are not comparable with the
RF-start classes of `ttc_c13.md` §3.

## 5. §6 and §7

- **§6.** The proved part of RF-PRIV is exactly Lemma ABS with f the private-top holder. The open part (a frozen agent
  with v_d(J) > p_d) is described correctly. The lift test is evidence and was not re-run.
- **§7.**
  - Proposition RF-𝒦 transfers to RKMAX, with REC-∃ not needed, since RKMAX ⟹ OC₁^∃max by MAXSD (`rkmax.md` §1).
  - ABS transfers, since it is about any SD start.
  - RF-TOP's corollaries do not transfer. The reason given, that RKMAX does not quantify over every receiver-first
    start, is correct.
  - "Top-holding receivers' rotations do not change σ" is correct: the rotation is the identity.
