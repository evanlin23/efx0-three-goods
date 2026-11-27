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

## Addendum 2: Lemma SPLICE (`kgen/rounds.md` §4.10 at `7ffbfd2e`, PR #128; coordinator's queue, 2026-11-27)

**Verdict: CORRECT WITH TWO SMALL FIXES** (both wording; the statement the campaign uses, proposed row K4.SPLICE,
is exactly what is proved). I re-derived the proof step by step and tested it with my own code
(`splice_ex_ref.py`, `splice_ex_replay.py`, `splice_n5_ref.py`, `splice_n5_gaps_ref.py`; logs
`results/k4_referee/splice_ex_ref.log`, `splice_ex_replay.log`, `splice_n5_ref.log`). This supersedes the GAP of
Addendum 1: the case found there is the lemma's EX-b, which the lemma now excludes explicitly.

**Re-derivation.**
- *Picks per bundle.* k holds Y_z or nothing. u₀ holds W's picks: B₁[u_s] (one pick, since u_s ≠ k) and Y_z when
  Y_z ∉ T, minus h. w holds one pick, plus h if h is a pick. Every other agent holds one pick.
  - So the four cases (Y_z ∈ T or not; h junk or a pick) give (q, v) = (none, none), (u₀, w), (k, u₀), (k, w).
  - In-degree 0 at q exactly when in-degree 2 at v.
- *Functional graph.* Only one vertex has in-degree 0, so only one component has a tree. That tree is a single path,
  because a branch point would need a second leaf. v is where it meets the cycle. So f is a permutation or a rho plus
  cycles.
- *Round structure.* The Lemma RC structure is forced in one place only:
  - q has no predecessor (it holds no pick), and as a mover it must pass, so q → f(q).
  - In the rho with a = q and f(v) = v, v therefore has predecessor q, its own pick is outside its base, and its gain
    is exactly v_v(X_v ∖ {Y_v}) > p_v.
  - So **the converse also holds**: in (EX), X is not a witness. My data agree in both directions (below).
  - Everywhere else the proof's choices are valid structures for RNDOZ: rings start at an agent valuing its received
    pick; the rho's end pick is at v, a non-end of the same chain; and so on.
- *Gains and one absorber:* re-derived as written. For b = u₀ this needs v_{u₀}(W) ≥ v_{u₀}(H₀′), i.e. H₀′ ⊆ W
  (see F1).
- *The three forms are exhaustive.* Unwinding:
  - q = k (Y_z ∉ T). Follow Y_k from x₁:
    - x₁ ∉ P₂: x₁ keeps Y_k. x₁ keeps its own pick only if t = 1 and h = Y_z goes to z = x₁, and then
      v_z(Y_k) > p_z, so this is not (EX).
    - x₁ = u_i with i < s, or x₁ = u₀: Y_k's holder u_{i+1} wants it, so this is not (EX).
    - x₁ = u_s: Y_k lands in W, with v = u₀ = z (**EX-a**), or it is h (**EX-b**).
  - q = u₀ (Y_z ∈ T, h = B₁[u_s]'s pick). Y_{u₀} reaches an agent that wants it, unless u₀ = x_l and
    u_s = x_{l+1}, where it is h (**EX-c**).
- *EX-a needs Y_z ∈ H₀′.* u₀ = z gains strictly in move 2: v_z(H₀′) > v_z(Y_{x_{t−1}}) > p_z. So Y_z ∉ H₀′ would give
  v_z(W ∖ {Y_z}) > p_z. EX-a was never observed, by me or in the note.

**Fixes.**
- **F1 (setting).** State h ∉ H₀′ (H₀′ ⊆ W) and w ∉ {k, u₀}.
  - The proof uses H₀′ ⊆ W in the rho step and in the gains step (b = u₀). It uses w ≠ u₀ in the count of picks.
  - Both hold for REC-S repairs, because Theorem S takes H₀′ ⊆ W and gives h to z or to a wanter. On my
    configurations: H₀′ ⊆ X_{u₀}, X a partition, and one extra-good agent, at 3,477 of 3,477.
- **F2 (ring start).** The list of agents that value their received pick omits w.
  - It is harmless: in a pure cycle h is junk, because a pick h makes w the in-degree-2 vertex of the rho. So w's
    received pick is B₂[w], which w wants when it is foreign.
  - One sentence should say so.

**Data (my code; (EX) as stated, tested against my RNDOZ witness test).**

| data | REC-S configurations | RNDOZ witnesses | (EX) | (EX) and witness / neither |
|---|---|---|---|---|
| n = 4 export (112,880 starts) | 627,120 | 627,120 | 0 | 0 / 0 |
| random strict perfect starts, n = 3–5, seeds 1–3 (687,331 starts) | 23,682 | 23,560 | 122 (all EX-b) | 0 / 0 |
| the certifier's 280 n = 5 OC₁-failing starts (5_pure) | 4,122 (at 273 starts) | 4,122 | 0 | 0 / 0 |

- At the 280 n = 5 starts, u₀ never keeps its own pick, as the note says.
- **The constructed instance** (n = 4, m = 7, order (2, 0, 3, 1), picks (1, 6, 3, 5)):
  - E(3) = (3, 1), T = {0, 4}, P₂ = (2, 1), h = 5 = Y₃ to agent 0, X = ({1, 5}, {3}, {2, 6}, {0, 4}).
  - X is not a witness (RNDOZ, RNDPZ) and is EX-b.
  - The other 5 REC-S configurations at this start are witnesses.
- **Their printed exceptions.** All 43 that the random logs print (of 49; the 4,7 run prints 20 of its 26) replay:
  - the picks are SD of the stated order, and P₁ is my E(k);
  - X is complete and raw EFX₀, and is one of my REC-S configurations;
  - X is no witness, and my (EX) holds: 42 EX-b and 1 EX-c (random4_8 #646).
  - The totals 49 of 4,616 match the logs' summary lines (26 + 12 + 4 + 7; 2,218 + 1,246 + 669 + 483).

**In passing: K4.MULTI.RECS.EXIST.N5 (REFUTED) is confirmed.**
- With my E(k) form of REC-S, exactly 7 of the 280 starts have no REC-S configuration: #38, #419, #447, #773, #813,
  #963 and #1073, the note's seven.
- #773 and #963: no dangerous agent has an improving pool pair at any order giving the picks.
- The other five: improving pairs exist and SD-E holds at all of them (8, 12, 12, 2 and 12), but I⁻ has no Theorem S
  case.
- Not checked by me: the general canonical-chain form, and the claim that ROUND-P and RNDOZ hold at the 7.

**For the campaign.**
- REC-S ⇒ ROUND-P is proved outside (EX).
- "(EX) never occurs at starts without a one-move repair" remains data: 0 of 627,120 at n = 4 and 0 of 4,122 at the
  n = 5 starts here. It is what a proof of REC-S existence would still need, to give ROUND-P.

## Addendum 3: the pick graph, Lemmas PG, GAIN, RING, RHO, FIX and Theorem ROUND-SIMPLE (`kgen/rounds.md` §4.11 at `d79599ea`, PR #137; coordinator's queue, 2026-11-27)

**Verdict: CORRECT** (all five lemmas and the theorem). Script `roundsimple_ref.py` (own code: my pick-graph
classifier and my RNDOZ witness test `splice_ref.round_witness`), runs `roundsimple_ref_runs.sh`, log
`results/k4_referee/roundsimple_ref.log`.

**Re-derivation.**
- *PG.* A function on a finite set has one cycle per weak component. The in-degree of b is the number of picks in X_b.
  So a component whose in-trees form a single path from a pickless q, entering the cycle at v, has exactly one
  in-degree-2 vertex v. The five named shapes plus "complex" exhaust the cases.
- *GAIN* needs the setting's **distinct subset sums**, which the setting states. With strict good values alone it
  fails: v_b = (a: 3, b: 1, c: 2), Y_b = a, X_b = {b, c} gives v_b(X_b) = p_b.
- *The construction is a valid RNDOZ structure.* The passers are the chain agents other than the end, with s(a) = f(a).
  - In a ring, a_r is the end and its pick lies at the start a₁. Any start works, so the outside count may use the
    best start.
  - In a rho, c_r is the end. Of v's two in-edges only a → v is a chain edge, so s is injective and acyclic. v takes
    Y_{c_r}, its own chain end's pick.
  - In a rho-fix, the end a has a predecessor because the tail has length ≥ 2. The keeper v is off the chains, with
    base {Y_v} plus relevant junk and Y_a outside.
  - Every chain agent's base value equals v_b(X_b), since unvalued goods are worth 0. This is > p_b by GAIN.
  - The outside goods are exactly the theorem's list, so "one absorber" is the round's condition.
- *ka* is excluded correctly. There q → v is forced, and v's gain is v_v(X_v ∖ {Y_v}) > p_v. This is SPLICE's (EX)
  mechanism (Addendum 2).

**Data** (cores with distinct subset sums; every MD raw-EFX₀ allocation by brute force):

| data | starts | MD EFX₀ allocations | simple, one absorber | of these not RNDOZ witnesses | GAIN failures |
|---|---|---|---|---|---|
| random connected cores, n = 4–5, m ≤ 8 / 7, every perfect start | 2,038 | 39,644 | 34,202 | **0** | 0 |
| n = 4 export, 400 random starts with m ≤ 8 | 400 | 2,543 (all one rho) | 2,543 | **0** | 0 |

- Simple allocations with two absorbers: 106, and none is a witness.
- ka allocations: 5,311, of which 921 are witnesses (v gains) and 4,390 are not.
- Complex allocations: 25, and none is a witness.

**On "ROUND-P^max ⟺ SIMPLE-MD".**
- The theorem gives SIMPLE-MD ⟹ RNDOZ.
- The converse is not proved, and it fails allocation by allocation: the 921 ka witnesses above are RNDOZ witnesses
  that are not simple.
- At the start level it holds on my data. Every one of the 2,438 starts has a RNDOZ witness and also a simple
  one-absorber MD allocation (0 exceptions).
- So "⟺" is exact only with a proof of: "a RNDOZ witness at Y ⟹ a simple one-absorber MD allocation at Y".
  - A ka witness is the case to handle.
  - Or the theorem could be widened to admit ka with v_v(X_v ∖ {Y_v}) > p_v, counting Y_v among v's outside goods.
    - Such an X is then a witness by the same construction: q → v with v an end, base {Y_q} plus relevant junk.
    - Every ka witness has this form, since that structure is forced.
    - A converse would then still need to rule out witnesses whose pick graph is complex, for instance an end pick
      completed into another chain. None occurs in my data (25 complex allocations, 0 witnesses), but none is ruled
      out by proof.

## Addendum 4: Lemma UNTANGLE (`kgen/rounds.md` §4.13 at `50c1fc44`, PR #137; coordinator's queue, 2026-11-27)

**Verdict.**
- The proved parts (1)–(5) are **CORRECT**.
- The open parts (O1)–(O3) **cannot be closed by any rule for h**. Each of them alone can block U0 and every U1(h).
- (O2) blocks independently of h, and can also block U1′. So the fallback U2, a move of another kind, is a
  necessary part of the lemma, not a rare extra case.

Script `untangle_ref.py` (own code, brute force over every MD raw-EFX₀ allocation), runs `untangle_ref_runs.sh`, log
`results/k4_referee/untangle_ref.log`.

**Proved parts, re-derived.**
1. *Φ.* q and v end with exactly one pick each, and h is junk. So Φ's first coordinate rises by 2, under U1′ as well.
2. *MD.* X′_q ∋ Y_q, and v keeps Y_v.
3. *q's strict gain.* Junk was available at q's SD turn, so v_q(h) < p_q.
4. *q's EFX₀ conditions.* These follow by monotonicity and EFX₀ of X, exactly as written. Under U1, removing h from
   X_v − Y_q + h leaves X_v − Y_q. Removing any other g changes the value by −v_q(Y_q) + v_q(h) < 0.
5. *Unchanged pairs* are untouched. Under U0 every bundle's view of X_v − Y_q ⊆ X_v is monotone.

My data, counted separately for U0 and for every U1(h): 0 failures of (1)–(5), and every failing pair is of type
(O1), (O2) or (O3) (0 OTHER).

**The open parts: data** (random connected cores with distinct subset sums, every perfect start, every MD EFX₀
allocation, every needy keep-and-add pair):

| | n = 4, m = 7 (800 cores) | n = 5, m = 7 (150 cores) |
|---|---|---|
| needy keep-and-add pairs | 5,491 | 248 |
| U0 is EFX₀ | 2,945 | 95 |
| U0 fails: (O1) only / (O2) only / both | 2,457 / 44 / 45 | 153 / 0 / 0 |
| some U1(h) repairs, U0 failing | 2,363 | 153 |
| no U1(h) repairs; types over all h: (O1) / (O2) / (O3) | 78 / 58 / 47 | 0 |
| of these, some U1′(h, w) repairs | 59 | – |
| **U0, U1 and U1′ all fail: U2 needed** | **124** | 0 |

**Rules for h** (n = 4, among the 2,546 pairs where U0 fails; "some h" works at 2,363):

| rule | succeeds |
|---|---|
| the good of X_q that the U0 (O1)-violators value most (the note's suggestion) | **2,274** (fails at 89 where another h works) |
| largest total value to the other agents | 2,174 |
| v's most valued good of X_q | 2,129 |
| q's least valued good | 2,071 |

**Smallest configurations** (all n = 4, m = 7, found by my code; the first two re-derived by hand).

- *(O2) blocks every move, independently of h.*
  - Values:
    - v₀ = (0: 38, 3: 45, 4: 23, 5: 9);
    - v₁ = (1: 26, 2: 12, 4: 40, 6: 37);
    - v₂ = (0: 21, 1: 12, 3: 34);
    - v₃ = (1: 44, 3: 32, 4: 31, 5: 21).
  - Picks (0, 4, 3, 1), from order (2, 0, 3, 1).
  - X = ({0, 4}, {2, 6}, {3, 5}, {1}) is MD and EFX₀. The pair is q = 1, v = 0: Y₁ = 4 ∈ X₀, and
    v₀(X₀ ∖ {0}) = 23 ≤ 38.
  - After the return, agent 0 holds {0} (38) and envies {3, 5} − 5 = {3} (45).
  - q's junk {2, 6} is worthless to agent 0, so U1 fails for both h.
  - U1′ to agent 2 or 3 leaves agent 0 at 38 against {3} or {3, 5, h}.
  - The obstruction is a pick of an earlier SD agent (Y₂ = 3) that v values above p_v. The SD bound of the note
    ("a good available at v's turn is worth less than p_v") does not cover such picks.
- *(O1) blocks every h.*
  - Values:
    - v₀ = (0: 28, 1: 8, 3: 13, 4: 35);
    - v₁ = (1: 34, 2: 39, 6: 19);
    - v₂ = (2: 4, 4: 1, 5: 56, 6: 2);
    - v₃ = (0: 29, 1: 43, 3: 21, 6: 5).
  - Picks (4, 2, 5, 1). X = ({1, 4}, {2}, {5}, {0, 3, 6}), with q = 3 and v = 0.
  - After the return, agent 1 sees {0, 1, 3, 6} minus a worthless good, worth 34 + 19 = 53 > 39.
  - For h = 0 or 3 the same holds.
  - For h = 6, agent 0 sees {0, 1, 3} − 1 = 41 > v₀({4, 6}) = 35.
- *(O3) blocks every h; U1′ works:* v = [[25,58,0,52,0,55,0], [0,40,59,9,0,0,32], [35,0,0,27,59,0,0],
  [0,0,25,0,0,16,48]], picks (1, 2, 4, 6), X = ({1}, {2, 4, 5}, {0, 3}, {6}), q = 2, v = 1.
- *The note's rule fails while another h works:* v = [[0,51,0,0,22,0,33], [29,34,0,53,42,0,0], [48,0,0,0,54,58,19],
  [0,34,21,7,0,0,0]], picks (1, 3, 5, 2), X = ({1}, {0, 4}, {3, 5, 6}, {2}), q = 1, v = 2.
  - The (O1)-violator's favourite is h = 4, which fails by (O3); h = 0 works.

**For the campaign.**
- UNTANGLE as "U0 or U1, otherwise U1′ or U2" is true on the data only through U2, which is Φ-MAX's local step itself.
- A proof needs a second kind of move for the (O2) configuration: the needy keeper values an earlier agent's pick
  above its own and loses its cushion Y_q.
  - The fallback in the data moves a pick between other agents.
  - A candidate rule: when (O2) holds toward X_j, try handing X_j's offending pick to v's chain. I have not tested it.
- *Follow-up (kgen-rounds, PR #137 head 51cf833d).* kgen-rounds proposes U3: after the return, v takes its favourite
  junk good from a bundle it envies.
  - On my (O2) example this gives ({0, 5}, {2, 4, 6}, {3}, {1}). My code confirms it is raw EFX₀, MD and a RNDOZ
    witness.
  - Their counts with U3 and U13 leave 10 of 5,452 (n = 4) to a three-pick rotation. I have not re-run these counts.
