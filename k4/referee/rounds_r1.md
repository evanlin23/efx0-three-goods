# Referee report: Lemma R1 and the starved-agent certificate (`kgen/rounds.md` §1, with §3's uses, branch `proof/kgen-rounds`, PR #111)

Referee: `proof/k4-referee`, 2026-11-26.
- Read: `kgen/rounds.md` at `a33b135`: the status, §1 (definitions, Lemma RC, Lemma R1, the Corollary), §3 (RD5⁺, C4G,
  the two-type instance) and §6 (proposed ledger rows).
- Check: `k4/referee/rounds_ref.py`, run by `rounds_ref_runs.sh`, log `results/k4_referee/rounds_ref.log`.
  - Rounds are enumerated forward from the definitions, with two enumerators written separately (picks-only and
    general bases). They agree on every named start.
  - Completions are checked against all n^m allocations with the raw definition.
  - No code from `kgen/rounds/` was run or imported.

## Verdict

| item | verdict |
|---|---|
| Lemma R1 (MD and one foreign pick per base after one round) | **CORRECT** |
| Corollary (starved-agent certificate) | **CORRECT** |
| Its use on RD5⁺ (ε = 1 and 99), C4G, the two-type instance: one round fails | **CONFIRMED** (certificate and, independently, forward enumeration of every round) |
| "Two rounds repair" these three | **CONFIRMED**. **Fix needed** in §3.1: the printed two-round repair of RD5⁺ is not valid as written (below), but a one-line correction of it is |
| Lemma RC, RC2, Lemma ID, §4–§5 | not refereed |

## 1. Lemma R1 and the Corollary

**Lemma R1.** After one round from the picks:
- off-chain agents and t = 0 starts keep their pick in their base;
- a receiver x_i gets {y_{x_{i−1}}} ∪ H_i with H_i ⊆ J;
- a start of a chain with t ≥ 1 gets H₀ ⊆ J ∪ {y_{x_t}}, its own chain's end only (the round definition, `k4/ksens.md`
  §6).

So every base holds at most one foreign pick. Chain agents gain strictly over their pick, and bases lie inside the
final bundles. So v_i(X_i) ≥ v_i(base) ≥ v_i(y_i), strictly for every agent that passed its pick, which are exactly
the agents with y_i ∉ X_i. Correct. Only nonnegativity is used, so it holds with zeros too.

**Corollary.** Let X be a completion after one round. By R1, X is EFX and value-dominates the picks, so by hypothesis
some agent a in X is starved.
- y_a ∉ X_a, so a passed its pick and lies on a chain with t ≥ 1.
- Its base is worth more than v_a(y_a) and lies inside {f} ∪ (X_a ∩ J) for its foreign pick f ∈ X_a (if any).
- Values are monotone, so the max in the definition of starved exceeds v_a(y_a). That is a contradiction.

The argument covers free and one-absorber completions alike. Correct.

## 2. The instances of §3 (evidence; my brute force)

| instance | picks | EFX allocations | MD ones | starved agent in every MD one | rounds from the picks (base tuples) | one round completes | first rounds with a completing second round |
|---|---|---|---|---|---|---|---|
| RD5⁺, ε = 1 | (1, 3, 4, 2) | 26 | 6 | agent 0 (holds {3, 4}) | 225 | no | 27 |
| RD5⁺, ε = 99 | (1, 3, 4, 2) | 26 | 6 | agent 0 | 225 | no | 27 |
| C4G | (4, 3, 5, 6) | 18 | 8 | agent 2 (holds {4, 6}) | 255 | no | 20 |
| two types | (2, 3, 6, 4) | 20 | 8 | agent 0 or 1 (holds {4, 6}) | 424 | no | 45 |

- The MD allocations of RD5⁺ are exactly as stated: agent 0 holds {3, 4} (+ 6), agent 3 holds {0, 5} (+ 6), and
  agents 1 and 2 hold the goods 1 and 2.
- "The other 9 distinct starts of RD5⁺ need at most one round": confirmed (5 extend, 4 need one round).
- (Not claimed otherwise in the note, but for the record: C4G has one more failing start, (4, 6, 5, 3), and the
  two-type instance three more.)

**The printed two-round repair of RD5⁺ (§3.1) is wrong as written.**
- The printed repair:
  - Round 1 (valid): the chain 3 → 1 with H₀ = {0, 5}, plus agent 0's t = 0 addition of good 6. Bases
    ({1, 6}, {2}, {4}, {0, 5}).
  - Round 2: "agent 2 takes 1 from agent 0's base {1, 6}".
- That breaks the chain rule (`k4/sdc.md` §29: x_i takes all of B_{x_{i−1}} plus junk), under which agent 2 takes
  {1, 6}. The state reached is ({3, 4}, {2}, {1, 6}, {0, 5}). It uses every good, and it is not EFX.
- The printed final allocation ({3, 4, 6}, {2}, {1}, {0, 5}) does not contain agent 2's base.
- **Fix:** drop the t = 0 addition in round 1. Then round 2's ring hands agent 2 exactly {1}, and agent 0 takes
  {3, 4}, worth 6700 > 5700. The printed final allocation is then a valid completion. Checked by forward enumeration.
- The claim "two rounds suffice" is unaffected: 27 of the 225 first rounds have a completing second round.

**Random positive instances** (n = 3, m ≤ 7; n = 4, m ≤ 6):
- every (round, completion) pair: 398,577 pairs from 8,050 starts, 0 violations of R1;
- no random start satisfied the certificate's hypothesis, consistent with the note ("random sampling found none").

## 3. For the coordinator

- Lemma R1 and the starved-agent certificate: CORRECT. Their part of the proposed KGEN.RC row can be PROVED. RC and RC2
  are not refereed here.
- The ROUND⁺ refutations (RD5⁺, C4G, two types) are confirmed by an independent brute force.
- §3.1's printed two-round repair needs the one-line fix above: no t = 0 addition of 6 in round 1.

## Addendum: the splice sketch, REC-S's two moves as one round (`kgen/rounds.md` §4.10 at `f91c6bc8`; coordinator's queue, 2026-11-27)

**Read.**
- §4.10 in full;
- §4.9 (RND1Z, RNDPZ, RNDOZ) and §1 (Lemma RC) for the definitions.

**Check.** `k4/referee/splice_ref.py`, run by `splice_ref_runs.sh`, log `results/k4_referee/splice_ref.log`.
- It is my own round-witness test, written from Lemma RC and §4.9: choose the passers among the movers, give every
  non-passing mover a predecessor, compute bases and strict gains, and count absorbers.
- It is applied to every REC-S configuration whose final allocation X is EFX₀, with the configurations from my
  `rec_s_ref.py`. Nothing from `kgen/` was run.

**Verdict: GAP.** The sketch's step 2 is false in one case, and its exception list misses that case. In that case the
final allocation X is not a one-round witness under any of the forms, the wide one included.

**Where step 2 fails.** Step 2 says "a path end whose pick was released is an end with a predecessor, because it holds
a received pick". That fails for k when three things happen together:
- P₂'s head is x₁, so B₁[x₁] = Y_k is released by P₂;
- P₂'s start does not take Y_k back (Y_k ∉ H₀′);
- k holds no pick, i.e. Y_z ∉ T.

Then k is a mover with no predecessor, so in any round k must pass Y_k to its final holder. In REC-S, Y_k reaches that
holder in the completion. With Theorem S's h = Y_{z′} it goes to the unfrozen wanter of z′'s good. That agent keeps its
own pick and need not gain from Y_k. If it does not gain, no round has X as a witness.

**Instance** (the first found; re-derived by hand).
- *Instance.* n = 4, m = 8, with values
  - v₀ = {0: 15, 4: 33, 7: 39};
  - v₁ = {0: 28, 1: 37, 3: 19, 6: 39};
  - v₂ = {2: 33, 3: 12, 4: 23, 7: 37};
  - v₃ = {4: 20, 5: 21, 6: 27, 7: 35}.

  The order (1, 2, 0, 3) gives the picks (4, 6, 7, 5). Strict values, a perfect start.
- *The two moves.*
  - E(1) = (1, 3) with T = {0, 1}.
  - In I⁻, Theorem S (relaxed, h = Y_{z′} = 6) uses P₂ = (2, 3) with H₀′ = {2, 3}. The head 3 is frozen after P₂
    (agent 0 wants 7), so h = 6 goes to agent 0.
- *The allocation.* X = ({4, 6}, {0, 1}, {2, 3, 5}, {7}). It is EFX₀ and satisfies (K).
- *Why no round has X as a witness.* Agent 1 holds only junk, so it has no predecessor, and its pick 6 is at agent 0. So
  agent 1 must pass to agent 0. Then agent 0's base is {6} plus its relevant junk in X₀, which is none, and
  v₀(6) = 0 < 33.
- Even the wide form, where an end may retake its own pick 4, gives v₀({4, 6}) = 33, not > 33. So no form of the round
  covers X.

**On the data.**

| data | REC-S configurations | X a witness: RND1Z / RNDOZ / RNDPZ | not a RNDPZ witness | of these, the mechanism above | the start still has some RNDPZ witness |
|---|---|---|---|---|---|
| n = 4 export (112,880 starts) | 627,120 | 0 / 627,120 / 627,120 | **0** | – | – |
| random strict perfect starts (n = 3–5), seeds 1 and 2 | 13,608 | 12,505 / 13,537 / 13,537 | **71** | **71 of 71** | **71 of 71** |

**The sketch's named exception is not the real one.**
- *Its "typical case" (P₂'s head taking Y_{x_t} as junk) cannot happen with REC-S's moves.* Theorem S's P′ is
  canonical, and receivers take no junk.
- *What REC-S's moves can produce instead is the keep-and-add shape:* P₂'s start keeps its own pick and also holds a
  foreign pick. That happens when P₂ starts at z (case A), or when P₂'s head is the start's successor on E(k) (case B).
- *That shape is harmless.* It occurs in 1,579 random configurations (A: 1,437; B: 142), and every one of them is still
  a RNDPZ witness. P₂'s start is then read as untouched, or as an adder, and the foreign pick goes into the completion.
- *The real exception is the mechanism above.* k's own pick is released and lands, in the completion, at an agent
  that keeps its pick.

**Consequences.**
- *The claim on the data stands.* At all 112,880 n = 4 starts the exception never occurs, so the n = 4 statement
  "REC-S's final allocation is a one-round witness" stands.
- *"When P₂ meets E(k), a single OC₁′ chain" is false in general.* All 71 failures have P₂'s head = x₁, an agent of
  E(k).
- *"REC-S existence implies ROUND-P" is not refuted.* At all 71 starts ROUND-P holds through another allocation.
- *What a proof needs.* It must also close this case. Two ways:
  - choose a Theorem S case in which Y_k does not leave the bundles of B₂ (P₂'s start takes Y_k, or P₂'s head is
    not x₁);
  - or show that its final holder gains from it.
