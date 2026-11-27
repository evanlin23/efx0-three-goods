# OC₁^max as matching theory: the free-slot deficiency, and a chain as an exchange

Workstream `proof/k4-matching` (branch `proof/k4-matching`, draft PR #116) of the TARGET₄ campaign (coordinator's record:
`k4/attack_log.md` on `claude/kind-lamport-y8fdme`). Target: Conjecture OC₁^max (K4.SDC.OC1MAX, `k4/sdc.md` §29–§31),
reduced by Lemma RED (`k4/sdc.md` §31) to perfect starts. Notation as in `k4/sdc.md` §30 and the Hall session's
`k4/oc1_hall.md` (branch `claude/k4-oc1-hall`): Y the picks, p_i = v_i(y_i), J the junk, *wants*, *frozen*, *dangerous* (D),
*holders*, the S\* shape, Lemma 2\*. Code `k4/matching/`, logs `results/k4_matching/`. Every completion test is decided
against the raw EFX₀ definition. Everything called evidence is evidence only (PROMPT.md §5 rule 3).

## Summary

| | statement | status |
|---|---|---|
| Lemma M (§1) | S\* completability with owner o is a bipartite matching condition: for some kept-out set H, Lemma 2\*'s slot graph Γ(H) has a matching covering the exposed holders, and the **free-slot deficiency** δ\*(B, o) (least number of extra one-good slots needed) equals min_H (\|H\| − ν(Γ(H))) = min_H max_{S⊆H} (\|S\| − \|N(S)\|), H over the kept-out sets with (H1) and E(H) coverable | **PROVED** (written proof, §1; refereed CORRECT, `k4/referee/matching.md` on `claude/k4-referee`, commit 19419c5, with 513,753 independent tests; second reader CORRECT, `k4/oc1_hall.md` §23.1). Checked here against a pruning-free brute force: 428,346 completion tests and 46,945 owner tests (deficiencies 0–5), 0 mismatches |
| "δ ≤ 1 at perfect starts", "one chain = one augmenting path" (§2) | **false at k = 4**: 249 of the 2,371 hard perfect starts tested have δ = 2 or 3, and one chain repairs every one of them. Smallest: n = 3, m = 6, δ = 2 for every owner (also in the K4.MC2 class); δ = 3 at n = 3, m = 7 | refuted (brute force; `attempts/k4-matching-deficiency.md`) |
| δ and the k = 5 counterexamples (§2) | PW5: δ = 2, best single move leaves δ = 1 (two chains). RD5: δ = 1, yet no single move repairs. The 41 failing (non-maximum) starts of the k = 4 core counterexamples all have δ = 2 | computed (brute force) |
| Lemma EX (§3) | an improving chain is an *exchange* in the slot graph: if, after the chain, Lemma 2\*'s slot graph **of the picks** with the chain agents' demands deleted or raised has deficiency at most the number s of slots the chain frees, the state completes (S\* shape, any chosen owner). For o = k and a canonical chain: the owner set W_{x_t} of the end, k's demand deleted | **PROVED, as a sufficient condition** (written proof, §3; refereed CORRECT, same report, 309,568 independent allocations, every hypothesis shown necessary to the proof). It is not exact: lb4-n2m5-upgrade (Hall §23.1) completes after a chain only by compensating a threatened head, which (1′) excludes. The exact version is Lemma EX\* (Lemma M after the move). Here the proof's allocation is built and is EFX₀ (raw) on all 49,771 (chain, H₀, owner) triples where the hypothesis holds; 0 violations |
| Conjecture CM (§3) | at every one-absorber-hard perfect start (k ≤ 4), some chain from a dangerous agent, some H₀ and some owner satisfy Lemma EX's hypothesis. CM ⟹ OC₁ at perfect starts ⟹ (RED, MAXSD) TARGET₄ | **refuted with OC₁^max** by the 11 n = 4 cores of compute/k4-oc1max-cert (§5). Before that: 2,371 of 2,371 hard perfect starts (Hall session's 2,071, the 9 of the core counterexamples, 291 of the PW design space) |
| CM ⟺ OC₁ on the data (§3, §5) | one exchange (Lemma EX / EX\*) repairs exactly when one move gives an S\* completion, at every hard perfect start tested: the 2,371 starts, the 30 of the 11 n = 4 instances, the walks near the n = 4 failures. Near those failures, 88 starts satisfy OC₁ only through a non-S\* completion (a compensated frozen slot) | computed |
| Lemma EX\* (§5) | the exchange at any state: Lemma M applied after a move, read in the slot graph before it (ownership moved, chain agents' demands re-evaluated, the chain's new slots added) | written proof (§5), a corollary of Lemma M; 0 violations |
| **Conjecture CM₂** (§5) | from every perfect start, some first move leads to a state where a Lemma EX\* exchange repairs. CM₂ ⟹ OC₂ at perfect starts ⟹ OC₂^max ⟹ TARGET₄ | evidence: all 30 hard maximum-matching starts of the 11 n = 4 failure instances, every start visited by the walks near them (OC₁ failing: 3,179 distinct in this note's long walk; OC₁ only non-S\*: 88 visits), the multi session's 4,955 failing pairs (n = 4, 5; 8,073 distinct failing starts in all), PW5, RD5. Where OC₁ fails, the first moves after which an EX\* exchange repairs are exactly those after which any second move repairs |
| Lemma LIFT-1 (§6) | under LIFT-red's hypotheses and (L3) every other agent values at most one good of h's bundle plus the junk: case (a), if (L1) z is unfrozen after P₂ and (L2′) z values h's new bundle at most its favourite good plus its best junk good, h takes that bundle minus z's best junk good and z takes its favourite good plus that junk good; case (b), if (Lb) z values h's bundle plus all the junk at most its favourite good, h takes everything. Either allocation is EFX₀ | written proof (§6; uses \|R_z\| ≤ 4, and Lemma PL(c) for the second sharer); construction EFX₀ (raw) on all 22,240 pairs meeting (L1), (L2′), (L3) over the two walk datasets (8,073 distinct failing starts, n = 4, 5) |
| **OC2-REC at n = 4** (§6) | the multi session's recursion (settle one sharer by a canonical chain with a shared pool pair T, delete it and T, then one move of the reduced instance repairs and lifts) holds at every n = 4 start with no one-move repair, and the reduced repair is a Lemma EX\* exchange | **CERTIFIED** (K4.MATCH.REC.N4): 112,880 witnesses re-verified by a self-contained raw checker; holds at the n = 5 counterexample to LIFT-SHAPE⁺ too |
| **LIFT-SHAPE⁺ at n = 4** (§6) | every n = 4 start with no one-move repair (all 112,880, every strict profile) has the LIFT shape with case (a) or (b) | **CERTIFIED** (K4.MATCH.LIFT.N4): witnesses re-verified by a self-contained raw checker; the set is compute/k4-oc1max-cert's export |
| Conjecture LIFT-EX (§6) | the second move, in exchange form (OC2-LIFT). At a perfect start with no one-move repair there is exactly one holder z; a chain from a dangerous agent to z absorbs a danger set shared with a second dangerous agent; a second chain ending at z gives z its favourite good, and its head owns (Lemma EX\* holds) | **refuted at n = 5, k = 4** (with LIFT-SHAPE⁺), by compute/k4-oc1max-cert's first n = 5 two-move start: the second chain is disjoint from the first and settles a second danger set (`attempts/k4-matching-lift-shape.md`). It holds at n = 4 (certified, above) and on the 8,073 walk starts. It is false at PW5 (k = 5, two holders). The multi session's recursion (Lemma LIFT, OC2-REC) covers the n = 5 start |
| exchange accounting (§3) | what a repairing chain pays for: in 910 of the 2,071 hard starts, deleting the chain agents' demands alone (s = 0) clears an end-owned deficiency of up to 6 | computed |

**Bottom line.**
1. The one-absorber completion is matching theory (Lemma M), but the matching size is not what a chain changes. A chain
   changes the *demand side*: the head's whole demand goes (two kept-out goods at k = 4 for a danger triangle), middle
   agents' demands shrink, ownership moves, and a few slots appear. So one chain can remove a deficiency of 2 or 3 at
   k = 4, and the static bound "deficiency ≤ 1" is false where OC₁ holds.
2. The right correspondence is the exchange. Lemma EX (sufficient) and Lemma EX\* (Lemma M after the move, exact for
   the S\* shape) say: the chain moves ownership, deletes or raises the chain agents' demands in the slot graph, and adds
   the slots it creates. The repair condition is a Hall condition there.
3. OC₁^max is implied by Conjecture CM, which is a static Hall-type statement about the picks and one chain. On every
   hard perfect start tested, CM holds exactly where a single move gives an S\* completion. That is where OC₁ holds,
   except for 88 starts near the n = 4 failures that need a non-S\* completion. OC₁^max is now refuted at n = 4
   (compute/k4-oc1max-cert, 11 cores), and so is CM.
4. At every known failure of one chain, the best exchange leaves exactly one slot missing:
   - the 11 n = 4 cores, and PW5 and RD5 at k = 5: δ = 1 or 2, best exchange excess 1;
   - in each, a first move followed by a Lemma EX\* exchange repairs (Conjecture CM₂, §5). The same holds at all 8,073
     distinct failing profile–start pairs that value walks find near them (§5, §6, with the multi session's walks).
   CM₂ implies OC₂^max, the campaign's current target.
5. At n = 4 the second move has one uniform shape, LIFT-SHAPE⁺ (§6): where the goods sit, plus three value
   comparisons. Lemmas LIFT-red and LIFT-1 (written proofs) turn it into a completion, and it is certified on every
   n = 4 start with no one-move repair (112,880). At n = 5 it fails (`attempts/k4-matching-lift-shape.md`): the
   second chain can be disjoint from the first, a second augmenting path for a second danger set. The general second
   move is the multi session's recursion: settle one sharer, then OC₁ one size down (OC2-REC).

## 0. Setting

A *state* B gives each agent a base B_i ⊆ R_i; J is the junk. At the picks Y of a perfect start, every agent with a
relevant good holds its pick, so by (I2) of `k4/sdc.md` §2 every junk good is worth at most p_i to every agent i that
values it. A completion keeps every base and hands out J:
- *one-absorber* (`oa`): one owner o takes any set; every other agent takes at most one junk good;
- *S\**: one owner o (any agent); every holder other than o (unfrozen, at most one base good, empty bases included)
  takes at most one junk good; frozen agents and multi-good holders take nothing.

**Free-slot deficiency.** δ(B) (resp. δ\*(B), δ(B, o)) is the least d such that the state, with d extra *dummy slots*
added, has a one-absorber (resp. S\*, resp. owner-o) completion. A dummy slot is a receiver that values nothing and takes
one good. Equivalently, d junk goods are deleted. A singleton bundle is never strongly envied, so this is the same as d
null agents restricted to one good each. δ(B) = 0 iff B completes. δ = ∞ if B does not complete even with all junk
deleted. Implementation: `mlib.M.complete(base, d, shape, owners)`. It prunes with necessary conditions only, decides
existence by bipartite matching when no receiver's bundle can threaten anybody, and checks the witness with raw EFX₀.
`mlib.M.bf_complete` is the pruning-free brute force.

## 1. Lemma M: the matching form of the completion

Let B be a state satisfying Lemma 2\*'s hypotheses:
- (G1) no bundle of a non-holder threatens anybody at base values;
- (G2) no junk good is wanted.

At the picks both hold. Fix an owner o, and let N₁ be the holders other than o, Q the other agents, W_o = B_o ∪ J.
For H ⊆ J let X(H) = W_o ∖ H, and define:
- (H1)(H): no q ∈ Q is threatened by X(H) at v_q(B_q);
- E(H): the *exposed* holders, u ∈ N₁ threatened by X(H) at v_u(B_u);
- Γ(H): the bipartite graph H × N₁ with h ~ u iff u ∉ E(H), or u values h and is not threatened by X(H) at
  v_u(B_u) + v_u(h). This is Lemma 2\*'s admissibility.

**Lemma M (K4.MATCH.M).** For every d ≥ 0, B has an S\* completion with owner o and d dummy slots iff some H ⊆ J
satisfies (H1) and Γ(H) has a matching that covers E(H) and has at least |H| − d edges. Hence
> δ\*(B, o) = min { |H| − ν(Γ(H)) : H ⊆ J, (H1)(H), E(H) coverable in Γ(H) } = min_H max_{S ⊆ H} (|S| − |N_{Γ(H)}(S)|),
> where in the second form H ranges over the same family (H1)(H) with E(H) coverable,

and B completes with owner o iff some admissible H has a system of distinct admissible holders that also covers every
exposed holder.

*Proof.*
(⇒) Let H be the set of junk goods given to N₁ or to dummies. Then X_o = X(H).
- The agents of Q receive nothing and are safe, so (H1) holds.
- An exposed holder must receive a good, since with its base alone X_o threatens it, and that good makes it safe. So
  it is an edge of Γ(H). Any good given to an unexposed holder is an edge.
- These pairs form a matching covering E(H), with |H| minus the dummies' goods ≥ |H| − d edges.

(⇐) Give o the bundle X(H), each matched holder its good, and the unmatched goods of H to dummies (at most d).
- Holders' bundles have at most two goods, a base good nobody wants and a junk good nobody wants (G2). A two-good bundle
  threatens i only if i values one of its goods above its own value, so these threaten nobody.
- Bundles of Q threaten nobody by (G1), since values only rose.
- Dummies hold singletons and value nothing.
- X(H) threatens no agent of Q by (H1). It threatens no exposed holder, by the edge condition. It threatens no
  unexposed holder, since X(H) does not threaten it even at its base value.
- o itself is threatened by nobody, by the same two facts.

*The formula.* By the Mendelsohn–Dulmage theorem, if some matching covers E(H) and some matching has ν(Γ(H)) edges,
then some matching does both. So the least d is |H| − ν(Γ(H)), minimized over the H with (H1) and E(H) coverable. The
König–Ore formula turns ν into the max-deficiency form. ∎

*Remarks.*
1. Lemma 2\* is the refinement in which only *non-movable* exposed holders must be matched. The movable ones serve
   themselves by Theorem DT's moves, which put a good of their own danger set into their own slot. That is a larger H
   in Lemma M. The two conditions are equivalent: Lemma M is the "full witness" form.
2. The one-absorber shape adds frozen slots (Lemma 1's (S1)), where the slot of a frozen agent requires compensation
   of its wanters. That couples slots, and it is not a matching condition. S\* suffices after one chain (Hall session
   §13), so Lemma M uses S\*. δ (one absorber) and δ\* are both computed below.

*Check* (`k4/matching/exact_check.py`; `results/k4_matching/exact_check_*.log`). Data: every distinct start (every
order) of special, screen, suite, logs and 600 + 300 random core profiles with n ≤ 4, and every 7th state one official
move reaches from each.
- (a) `complete` against `bf_complete`, every owner, both shapes, d = 0, 1, 2: **428,346 tests, 0 mismatches**.
- (b) At the states with (G1), (G2), Lemma M's formula (`mlib.M.model_def`, König–Ore asserted) against the raw S\*
  deficiency per owner: **46,945 owner tests, 0 mismatches**. Deficiencies 0–5 occur (33,348 / 8,079 / 3,740 / 1,319 /
  414 / 45).

## 2. The deficiency at the hard starts: "δ ≤ 1" is false at k = 4

`k4/matching/hard_starts.py`, `results/k4_matching/hard_*.log` and `.jsonl` (one JSON row per hard start). The data are
the Hall session's (`ed_check.py` with MAX=1): every order with n ≤ 5, distinct pick vectors, picks forming a maximum
matching.
- The one-absorber-hard ones (no one-absorber completion at the picks, raw) number special 15, screen 182, suite 183,
  logs 1,200, random cores 293 + 182 + 16. That is **2,071, the Hall session's count exactly**, here by brute force
  instead of SAT.
- All are perfect starts (every agent picks).
- Two more sets:
  - `cex`: the maximum-matching orders of PW4, RD4, B<, B> and the 39 core counterexamples (9 hard starts);
  - `pw:7:300`: 300 instances of the PW design space (`k4/matching/pwdesign.py`, generator of `k4/ksens/pw4_search.py`,
    n ≤ 6; 291 hard starts).

| hard perfect starts | δ = 1 | δ = 2 | δ = 3 | OC₁ holds | one move reaches δ = 0 |
|---|---|---|---|---|---|
| Hall session's 2,071 | 1,888 | 175 | 8 | 2,071 | 2,071 |
| cex (9) | 9 | 0 | 0 | 9 | 9 |
| PW design (291) | 225 | 59 | 7 | 291 | 291 |
| **total 2,371** | 2,122 | **234** | **15** | 2,371 | 2,371 |

**So "deficiency ≤ 1 at perfect starts" is false at k = 4, and one chain can remove a deficiency of 3.**
- *Smallest, also in the K4.MC2 class:* gap-ivsetting-n3-m6-n3c23. Sets [[0,3,4,5],[1,3,4,5],[2,3,4,5]] (one private good
  each, a shared pool {3, 4, 5}), values [[1,6,4,8],[2,5,4,8],[3,6,5,7]], order (2, 1, 0).
  - Picks (4, 3, 5), J = {0, 1, 2}. Agents 1 and 2 are frozen and dangerous; agent 0 is the only holder.
  - Every owner has δ(Y, o) = 2.
  - For owner 0: X_0 = {4} plus at most one junk good. A second junk good makes agent 1 or 2 strongly envy it, for
    example {4, 0, 1} gives agent 1 the value 6 > 5. A frozen agent cannot take junk, because agent 0 would need
    compensation worth v_0(3) − 4 = 2 and values its only junk good at 1.
  - One chain repairs: (1, 0). Agent 0 takes 3, which it wants; agent 1 takes {1, 4} (2 + 4 > 5) and owns.
  - Checked by the pruning-free brute force (`attempts/k4_matching_attempts.py`, `results/k4_matching/attempts_check.log`).
- *δ = 3:* red-key-without-t0 (n = 3, m = 7; screen). In the K4.MC2 class: pw19 (n = 4, m = 8).

**The counterexamples** (`k4/matching/cex_deficiency.py`, `results/k4_matching/cex_deficiency.log`; every order, every
distinct pick vector).

| | k | failing start | δ at the picks | least δ after one move |
|---|---|---|---|---|
| PW5 | 5 | (0, 1, 2, 3, 4), maximum | **2** | 1 (two chains needed) |
| RD5 | 5 | (1, 3, 4, 2), maximum | **1** | 1 |
| the 39 core counterexamples, B<, B> | 4 | 41 non-maximum pick vectors | **2** (all 41) | 1 (all 41) |
| PW4, RD4 (the k = 4 versions) | 4 | none | (hard maximum starts: 1) | 0 |

On the core-counterexample instances, 136 non-maximum pick vectors with δ = 2 satisfy OC₁, and all 9 hard maximum ones
have δ = 1.

**Verdict on "δ ≤ 1 exactly where OC₁ holds":** no, in both directions.
- δ ≥ 2 with OC₁ holding: 249 hard perfect starts at k = 4, and 136 non-maximum starts.
- δ = 1 with OC₁ failing: RD5 at k = 5, and at k = 4 all 11 n = 4 OC₁^max failures of compute/k4-oc1max-cert (§5).
  When this section was written, the 41 non-maximum k = 4 failures (all δ = 2) were the only k = 4 failures known.
- PW5 behaves as the naive picture says: δ = 2, two chains.

**Where the augmenting-path picture breaks** (the exchange accounting below makes this precise). An augmenting path
raises the matching by one with the demand side fixed. A chain from a dangerous k does three other things:
1. it moves ownership, from whoever owned before to k or the end;
2. it deletes k's whole demand: k holds its improving set, so it has no danger set left (Lemma PL(b) at k = 4). At
   k = 4 a danger triangle is a demand of two kept-out goods;
3. it raises every middle agent to the pick it wanted, which shrinks or deletes their demands, and it can unfreeze
   other agents.

So the right object is the demand side of the slot graph, not ν. Lemma EX (§3) makes this precise.

## 3. Lemma EX: a chain as an exchange in the slot graph of the picks

**Setting.** Y is a perfect start (null agents allowed), F its frozen agents, J its junk. P = (k = x₀, x₁, …, x_t), t ≥ 1,
is an official chain (`k4/sdc.md` §29):
- x_i (i ≥ 1) takes {y_{x_{i−1}}} ∪ H_i, with H_i ⊆ J pairwise disjoint and v_{x_i} rising;
- k takes H₀ ⊆ (J ∖ ∪H_i) ∪ {y_{x_t}} with v_k(H₀) > p_k;
- x_t is unfrozen at Y, or y_{x_t} ∈ H₀ (its pick goes to k, the ring-like case).

B′ is the state after P, F′ its frozen agents, J′ its junk. Fix any owner o, on P or off it. Let N be the holders of Y
that are off P and other than o. Let Ext be the agents j ≠ o in F ∪ {x_t} that are unfrozen single-good holders at B′.
These are the slots the chain frees; write s = |Ext|. For H ⊆ J′ let X = B′_o ∪ (J′ ∖ H).

**Lemma EX (K4.MATCH.EX).** Suppose:
- (G1′) no multi-good bundle B′_j, j ≠ o, threatens any agent at its B′ value;
- (1′) X threatens no agent of F off P (other than o) at its pick value, and no agent of P other than o at its B′ value;
- (2) in Γ_Y(H), Lemma M's slot graph of the *picks* on the holders N (exposure and admissibility at pick values with
  respect to X), some matching covers the exposed holders and has at least |H| − s edges.

Then B′ has an S\* completion owned by o: o takes X, the matched holders take their goods, the other goods of H go to
the agents of Ext (one each), and every other base is kept.

*Proof.* Four facts are used.
- Values only rise from Y to B′: k and the chain agents gain, and nobody else changes.
- Hence an agent unfrozen at Y and off P is unfrozen at B′. Its pick was wanted by nobody, and nobody's value fell.
  So N consists of holders of B′.
- Every h ∈ H is unwanted at B′. If h ∈ J, (I2) at the perfect start gives v_i(h) ≤ p_i for every i that values it.
  Otherwise h = y_{x_t} ∉ H₀, which happens only when x_t is unfrozen at Y.
- Every agent of Ext holds one good that nobody wants at B′.

The bundles of the final allocation:
- X, held by o;
- {b, h} or {h} for the receivers in N ∪ Ext, with b and h both unwanted at B′;
- the other bases.

A bundle of at most two unwanted goods threatens nobody. Values at the end are at least the B′ values. Singletons
threaten nobody. Multi-good bases other than o's threaten nobody by (G1′). So only X can threaten. Every agent i ≠ o is
covered:
- an agent of F off P (an Ext agent among them included), by (1′);
- an agent of P, by (1′);
- an exposed holder of N, by its matched good (an edge of Γ_Y(H));
- an unexposed holder of N, since X does not threaten it at its pick value;
- every other agent: at Y every agent holds at most one good, so an unfrozen agent off P other than o is a holder of N.

o takes the rest. The receivers are holders of B′ and take one good each. Nobody else takes junk. So the allocation is
S\*-shaped and EFX₀. ∎

*Matching form.* By Mendelsohn–Dulmage, (2) says that E(H) is coverable in Γ_Y(H) and |H| − ν(Γ_Y(H)) ≤ s. So the
**exchange deficiency**
> d_o(P, H₀) = min over H ⊆ J′ with (1′) and E(H) coverable of |H| − ν(Γ_Y(H))

is Lemma M's deficiency of the picks, with the owner set replaced by B′_o ∪ J′, the demands of the chain agents
replaced by their B′ demands (k's deleted when o = k), and the chain's s free slots added. **Lemma EX: d_o ≤ s_o
repairs.**
- For o = k and a canonical chain (no junk for x₁, …, x_t): B′_k ∪ J′ = J ∪ {y_{x_t}} = W_{x_t}. So the chain is
  literally an exchange in the picks' slot graph: ownership moves from the end x_t to k, k's demand is deleted, middle
  demands are raised, and the end becomes a slot if it is unfrozen at B′.
- With D = {k}, o = k and a canonical chain, Lemma EX relates to the Hall session's Lemma D1-red as follows:
  - when no holder is exposed, D1-red is EX with H = ∅;
  - in general, D1-red is EX with H = the goods of Theorem DT's moves, via Lemma M ⟺ Lemma 2\*
    (`k4/oc1_hall.md` §23.1).
  CROWD is the exposure of holders by H₀ ⊆ X. Lemma M's full-witness form handles it by compensation, but that does not
  make the compensation exist.
- **EX is sufficient, not exact** (second reader, `k4/oc1_hall.md` §23.1; `k4/oc1_hall/ex_not_exact.py` on
  `claude/k4-oc1-hall`).
  - Instance: lb4-n2m5-upgrade, sets [[0,2,3,4],[1,2,3,4]], values [[1,4,6,8],[2,4,5,8]], order (0, 1), chain (0, 1),
    H₀ = {2, 3}, owner 0.
  - B′ has the S\* completion [[2,3,0],[4,1]]: the head takes junk good 1 as compensation.
  - (1′) requires every chain agent other than o to be unthreatened outright, so EX misses it.
  - The exact version is Lemma M at B′, in which the chain's single-good holders are compensable slots. That is Lemma
    EX\* of §5.
  - The referee notes a free strengthening that EX\* also contains: Ext may include the chain agents unfrozen at Y that
    are unfrozen single-good holders at B′.

*Check* (`k4/matching/exchange.py`; `results/k4_matching/exchange_all.log` for the 2,071 + 9 starts,
`exchange_pw_7_300.log` for the PW design).
- Enumerated: every official chain from a dangerous agent (`general_chains`; `canonical_chains` for the canonical
  ones), every improving H₀, every owner.
- Wherever the hypothesis d_o ≤ s_o holds, the proof's allocation is built (`md_witness`) and checked with raw EFX₀,
  and the raw S\* test at B′ with owner o is run.
- Result: 38,429 such triples on the 2,080 starts and 11,342 on the 291 PW-design starts, 49,771 in all: 0 witness
  failures, 0 violations.

**Conjecture CM (K4.MATCH.CM).** Let Y be a one-absorber-hard perfect start of an instance with ≤ 4 relevant goods per
agent. Then some official chain P from a dangerous agent, some improving H₀ and some owner o have d_o(P, H₀) ≤ s_o.
- By Lemma EX, CM implies OC₁ at perfect starts. With Lemma RED it implies OC₁^max, and with Lemma MAXSD, TARGET₄.

| hard perfect starts | CM, any owner | owner k or end | owner k | canonical chain, owner k |
|---|---|---|---|---|
| Hall session's 2,071 | **2,071** | 2,071 | 2,070 | 1,988 |
| cex (9) | **9** | 8 | 7 | 7 |
| PW design (291) | **291** | 285 | 284 | 266 |

The exceptions to the narrower forms:
- *Owner k fails, end owns:* log1480 (n = 3, m = 7, picks (3, 6, 1)). This is the strict-dichotomy instance of
  `k4/sdc.md` §29: agent 0's H₀ = {0, 2} is agent 2's danger set, so the end must own (the Theorem B₄ shape). Also RD4.
- *Owner k and end fail, an off-chain agent owns:* PW4 (n = 5, m = 8) and the PW-design instance pw94 (n = 4, m = 7).
  Sets [[0,4,5,6],[1,4,5,6],[0,1,2],[1,0,3]], values [[20,18,12,19],[20,17,15,14],[4,5,1],[3,7,2]], picks (0, 1, 2, 3).
  - In PW4 the frozen agents share the pool. After x₀ takes two pool goods, the third pool good is harmless to the
    other frozen agents (Lemma PL(c)), but H₀ itself is a danger set for them. So x₀ cannot own, and the end, a wanter
    of every frozen pick, cannot either. The other wanter owns.
- *Non-canonical chains are needed* in 83 + 2 + 25 starts (smallest lb4-n2m5-upgrade, n = 2; T3, adaptive-p1, n = 3).
  - In T3 and adaptive-p1 the repairing chain ends at a frozen agent whose pick goes into H₀. These are Finding C's
    configurations.

**The k = 5 counterexamples under CM** (`results/k4_matching/cex_deficiency.log` and the computation in §2). At PW5 and
RD5, the least d_o − s_o over every chain, H₀ and owner is **1**, the same as the least δ after one move.
- At PW5, 696 of the 1,050 triples fail (G1′), 174 have no H satisfying (1′) with the exposed holders coverable, and
  the other 180 leave d − s = 1 or 2. This is the mechanism of Lemma PL(d): after one chain, two pool goods of every
  other frozen agent are still outside its bundle.
- So the exchange deficiency measures exactly what is missing there.

**The exchange accounting** (`k4/matching/ex_profile.py`, `results/k4_matching/ex_profile.log`; the 2,071 starts,
owner k, the triple with the fewest free slots s, then the least d). The table compares δ(Y, x_t) (S\* deficiency with
the end as owner and every demand present) with the exchange (d, s).

| s (free slots used) | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| starts | 910 | 689 | 398 | 72 | 1 |

- With s = 0 the whole deficiency δ(Y, x_t), up to 6, is cleared by deleting and raising the chain agents' demands.
- The chain passes through 1, 2, 3 or 4 dangerous agents in 1,269 / 695 / 102 / 4 of the starts, and has length 1–4.
- Middle or end junk is used in 1,031.
- So the chain's value lies mostly in *demand deletion*. The slot count matters in the rest.

## 4. What a proof now has to do, and where k ≤ 4 enters

OC₁^max is refuted (§5), so the target is OC₂^max. In the language here that is Conjecture CM₂: a first move,
then a Lemma EX\* exchange. Lemma EX\* turns the second step into one Hall-type condition in the slot graph of the
intermediate state. A proof would:
1. take a Hall violator of the picks for a natural owner: a set S of kept-out goods with |N(S)| < |S|. Its goods lie
   in the pools of dangerous agents, since at the picks only frozen agents and exposed holders have demands;
2. choose a dangerous k whose demand meets S, and a chain from k through the other agents whose demands meet S (want
   arcs, plus a junk-assisted step where Finding C needs one);
3. show (1′) and (G1′) after the exchange. This is where k ≤ 4 must enter:
   - Lemma PL(b): k keeps no danger set outside H₀;
   - Lemma PL(c): an agent sharing ≥ 2 goods of H₀ keeps no danger set in J ∖ H₀;
   - but H₀ itself can be a danger set for such an agent when k does not own. That case forces another owner (PW4,
     pw94);
4. count the remaining deficiency against the freed slots. At every known one-chain failure exactly one slot is
   missing after the best exchange (§5). So the proof of the second move must recover one slot.

At k = 5, step 3 fails at PW5 and RD5 with exactly one slot missing, and a second exchange repairs both (§5).

Open items (in order):
- **The second move of CM₂.** At the 11 n = 4 failures, which first moves admit an EX\* exchange, and what they have in
  common. That is the mechanism of the "tree exchange" in `k4/attack_log.md` 23:36, which no single chain performs.
- **CM for |D| = 1** is the Hall session's Finding D1 in the exact form. Both of its obstacles become conditions of
  one matching problem:
  - HEAD is (1′) for x_t, or s = 0 when x_t is frozen at B′;
  - CROWD is the coverability of the crowded exposed holders by compensating goods.

  Sub-lemmas D1-H and D1-C are the two ways this matching condition can fail for one H₀. The exact form does not
  remove them. (D1-C is now proved by proof/k4-d1, PR #113.)
- **CM for a shared pool** (PW4, pw94): owner off the chain, with Lemma PL(c) for the frozen agents sharing two goods of
  H₀.
- "δ = 1 ⟹ OC₁" at k = 4 is false: the 11 n = 4 OC₁^max failures all have δ = 1 (§5).

## 5. The n = 4 OC₁^max failures, Lemma EX\*, and Conjecture CM₂

**The instances.** The ordinal CEGAR of compute/k4-oc1max-cert found 11 strict connected K4.MC2-class cores with n = 4
and m = 7, 8. Each has a perfect start with no one-absorber completion at the picks or after any single move. They
are verified by the coordinator, `k4/sdc/oc1max_cex_verify.py` and `oc2max_cex_check.py`. The copy used here is
`results/k4_matching/data/oc1max_cex_n4.json`, taken from that branch at cfb3c18. Under the matching view
(`k4/matching/n4_cex.py`, `results/k4_matching/n4_cex.log`):

| the 11 failing starts | value |
|---|---|
| free-slot deficiency δ at the picks | **1** in all 11. Three agents are frozen; the one owner with δ = 1 is the lone unfrozen agent (the only holder), the other owners have 2–3 |
| least δ after one move | 1 in all 11 |
| least exchange excess d − s over every chain, H₀ and owner | **1** in all 11 |
| least δ after two moves | 0 in all 11 |

So one missing slot is enough to defeat a single chain at k = 4, and "δ = 1 ⟹ OC₁" is false. The same pattern holds
at k = 5: PW5 and RD5 also have best exchange excess exactly 1. At every known failure of OC₁, one exchange leaves
exactly one slot missing.

**Lemma EX\* (K4.MATCH.EXS).** This is the exchange at an arbitrary state, so that it can be the second step. It is
Lemma M applied after the move, read in the slot graph before it.

*Setting.* Let B be any state with junk J, and P an official chain from B:
- x_i (i ≥ 1) takes B_{x_{i−1}} ∪ H_i, with B_{x_{i−1}} ≠ ∅ and v_{x_i} rising;
- x₀ takes H₀ ⊆ (J ∖ ∪H_i) ∪ B_{x_t}, with v_{x₀} rising.

B′ is the state after P, and J′ = (J ∖ (H₀ ∪ ∪H_i)) ∪ (B_{x_t} ∖ H₀) its junk. Fix an owner o.
- *The slots* are the holders of B′ other than o. They are of two kinds: N, the holders of B off P, whose bases and
  values are unchanged (values rise from B to B′, so they stay unwanted); and Ext, the slots the chain creates (s =
  |Ext|), for example the chain end, and agents that were frozen at B and are unfrozen now.
- For H ⊆ J′ let X = B′_o ∪ (J′ ∖ H).

Suppose:
- (W′) every good of J′ is unwanted at B′;
- (G1′) no multi-good bundle of B′ other than o's threatens anybody at its B′ value;
- (1′) X threatens no non-holder of B′ other than o at its B′ value. For a non-holder off P, that is its B value;
- (2) the exposed slots (threatened by X at their B′ value) can all be matched to compensating goods of H, within a
  matching of all of H into the slots, in Lemma M's slot graph of B′.

*Conclusion.* B′ has an S\* completion owned by o.

*Proof.* (W′) and (G1′) are Lemma M's (G2) and (G1) at B′. (1′) is its (H1), and (2) is its matching condition with
d = 0. Lemma M gives the completion. ∎

*The exchange reading.* The slot graph of B′ is that of B with four changes:
1. ownership moves to o;
2. the chain agents' demands are re-evaluated at their new values (deleted for x₀ when o = x₀);
3. the slots of N keep their exposure and admissibility;
4. the slots of Ext are added, each with its own exposure.

Lemma EX (§3) is the special case at the picks where the Ext slots are required to be unexposed and used as free
slots. That is why its condition reads |H| − ν(Γ_Y(H)) ≤ s.

*Two remarks on the computation.*
- An earlier version of EX\* also treated Ext slots as free, requiring them to be unthreatened. In the walks below this
  missed repairs in which the chain end wants the owner's good and is compensated by a junk good. One example: the
  value neighbourhood of instance 0 with agent 1's values (14, 3, 7, 8). The chain (2, 1) with H₀ = {3, 4} and owner 3
  needs agent 1 to take the released good 2. The version used throughout this section (`exchange.ex_value_general`
  with comp=True) allows compensation.
- At the picks, (W′) is automatic under Lemma EX's end condition, by (I2) and (U), so EX\* contains EX.

**Conjecture CM₂ (K4.MATCH.CM2).** From every perfect start of an instance with ≤ 4 relevant goods per agent, some
official first move leads to a state at which some chain, H₀ and owner satisfy Lemma EX\*'s hypothesis (the first move
may be empty, which is CM).
- By Lemma EX\*, CM₂ implies OC₂ at perfect starts. With RED and MAXSD it implies OC₂^max and TARGET₄.

*Evidence* (`k4/matching/cm2.py`; `results/k4_matching/cm2_n4.log`, `cm2_n4all.log`, `cm2_k5.log`). Every EX\* witness
found is confirmed by the raw S\* test: 0 violations.

| starts | one EX\* exchange (CM) | OC₁ | CM₂ | OC₂ |
|---|---|---|---|---|
| the 11 stored failing starts | 0 | 0 | 11 | 11 |
| all 30 one-absorber-hard maximum-matching starts of the 11 instances | 19 | 19 | **30** | 30 |
| PW5, RD5 (k = 5) | 0 | 0 | 2 | 2 |

- **On these starts EX\* is exact, for one move and for two.** On the 30 starts, one EX\* exchange repairs exactly when
  one move repairs (19 / 19). At the 11 stored starts, PW5 and RD5, the first moves after which an EX\* exchange
  repairs are exactly those after which *any* second move repairs: 4 / 4, 7 / 7, …, 36 / 36 at PW5, 9 / 9 at RD5.
- **Walks in the value neighbourhood of the 11 failures** (`k4/matching/n4_walk.py`, `results/k4_matching/n4_walk_*.log`;
  value mutations ±1..3 that stay strict connected cores; the walk prefers starts where OC₁ fails or EX\* disagrees):
  - runs of 300 steps (seed 1) and 3,000 steps (seed 2) from each of the 11, together 1,250 + 17,883 hard perfect
    starts visited;
  - wherever OC₁ fails (214 + 4,299 visits; 129 and **3,179 distinct failing profile–start pairs** in the two runs,
    which start from the same 11 and may overlap, so OC₁^max failures are plentiful near the 11), CM₂ holds and EX\* is
    exact on the second move;
  - wherever some single move gives an S\* completion, an EX\* exchange exists;
  - but in 14 + 74 visits a start satisfies OC₁ only through a *non-S\** one-absorber completion. A frozen agent takes a compensated junk
    good, which Lemma 1's (S1) allows and S\* does not. No single move gives an S\* completion there, so CM fails
    while OC₁ holds. CM₂ holds on all of them.
  - So EX\* is exact relative to the S\* shape on the data. The S\*-shape gap is real near the failures, and CM₂
    absorbs it with a second move.
- 6,250 hard perfect starts from 3,000 random profiles of each of the 11 hypergraphs (`n4_profiles.py`) contain no
  failure at all. Random profiles miss the failure region.
- Evidence only: the n = 4 failures were found only by an exhaustive ordinal search. Random profiles (11M orders at
  n = 5) and the climbs of `k4/matching/cm_climb.py` missed them (§7).

**Closing the S\*-shape gap: Lemma M^c** (proof/k4-oc1max-multi, `k4/oc1max_multi.md` §9 on its branch, commit
3b69d07). It extends Lemma M in two ways:
- *frozen slots:* a frozen single-good agent may take one junk good when every wanter of its good is compensated;
- *compensated (G1):* a multi-good bundle may threaten an agent that its own junk good compensates.

Its shape S^c lets every agent with at most one base good take one junk good. At single-good states that is exactly
the one-absorber shape. Its matching form enumerates the frozen slots F_s and, for each, runs Lemma M's matching with
per-agent requirements τ_i. Lemma EX\*'s reading carries over verbatim: Lemma M^c at the state after a move.

Checked here with this note's own code (`k4/matching/mc_check.py`, `results/k4_matching/mc_check.log`). Lemma M^c's
formula is written independently as `mlib.M.mc_def`, and S^c is a new shape of `mlib.M.complete` and `bf_complete`.
- The formula against the raw S^c deficiency: **65,201 owner tests, 0 mismatches**. The states are the picks of the
  hard starts and every fifth one-move state, with (G2).
- The pruned S^c search against the pruning-free brute force: 33,200 tests, 0 mismatches.
- S^c equals one absorber at the picks: 21,880 owner tests.
- **Some single move gives an S^c completion exactly when OC₁ holds,** on all 2,371 hard perfect starts of §2 and on
  the 60 distinct walk starts that only a non-S\* completion repairs; S\* repairs none of those 60.

So with S^c in place of S\*, one exchange (Lemma M^c after the move) decides OC₁ exactly on all data, and the S\*-shape
gap is closed. The referee has not read Lemma M^c; the multi session reports its own 2,226,322 tests.

**The mechanism, in exchange terms** (`k4/matching/n4_twomoves.py`, `results/k4_matching/n4_twomoves.log`: every
(first move, EX\* exchange) pair that repairs, 57 over the 11 stored starts).
- *The first move* is always a chain from a dangerous agent whose head takes a junk pair that another dangerous agent
  also values (57 of 57). That is the shared danger pair of Hall §22 and TTC §14. This one exchange removes two
  demands, but one slot is still missing (excess 1).
- *The second exchange.* Its head collects two foreign picks of Y in 35 of the 57, one of them released by the first
  chain, and one foreign pick in 21. The second chain starts at an agent frozen at B₁ in 35, and at the first chain's
  head in only 5.
- Example: instance 0 (coordinator's instance 1). Sets [[0,1,2,5],[1,2,5,6],[3,4,5,6],[3,4,6]], values
  [[2,10,4,7],[10,3,4,8],[3,5,6,7],[3,2,4]], picks (1, 2, 5, 6), junk {0, 3, 4}.
  - Agents 2 and 3 share the danger pair {3, 4} (3 + 5 > 6 and 3 + 2 > 4). Agent 1 is the lone holder.
  - First chain (2, 1): agent 2 takes {3, 4}, and agent 1 takes 5, releasing its pick 2.
  - Second chain (0, 1): agent 1 takes 1, and agent 0 takes {2, 5} (4 + 7 > 10) and owns.
  - Agent 0's only improving sets contain both foreign picks 2 and 5. Its four goods are its pick, one junk good and
    two foreign picks. That is RD5's "two foreign picks" repair (`k4/ksens.md` §6), here at k = 4. One chain can hand
    its head only the end's base, so it cannot collect two picks.

## 6. The second move in exchange form: Conjecture LIFT-EX

This answers the coordinator's request (23:45) to state and prove the second step of CM₂ in the shape found in §5, in
the Hall session's case tree (`k4/oc1_hall.md` §23.2, leaf 5, Sub-lemma OC2-LIFT). The shape is found and is uniform
on all data. Its proof is reduced to one condition below, which is not proved.

> **Update: refuted at n = 5.** LIFT-EX and LIFT-SHAPE⁺ fail at compute/k4-oc1max-cert's first n = 5 two-move start
> (end of this section; `attempts/k4-matching-lift-shape.md`). Both hold at every n = 4 start (certified, below). The
> conjecture and its evidence are kept as stated.

**Conjecture LIFT-EX (K4.MATCH.LIFT).** Let Y be a perfect start of an instance with ≤ 4 relevant goods per agent,
with no one-move repair. Then:
1. Y has exactly one holder z, and every other agent is frozen.
2. Some official chain P₁ from a dangerous agent k ends at z, and its H₀ ⊆ J ∪ {y_z} is also improving for a second
   dangerous agent k′. This is a shared danger set, `k4/oc1_hall.md` §23.3.
3. After P₁, some official chain P₂ ends at z and gives z its favourite good of R_z. With P₂'s head h as owner, Lemma
   EX\* holds at B₁, so the state B₂ after P₂ has an S\* completion owned by h.

In OC2-LIFT's terms: z, holding its favourite good, wants nothing. So every agent that was frozen only because z
wanted its good is unfrozen. On the data every DEMAND agent of P₁ is of this kind.

*Evidence* (`k4/matching/lift_shapes.py`, `results/k4_matching/lift_shapes.log`). The data are every start with no
one-move repair known here:

| starts | 1–3 hold |
|---|---|
| the 3,179 distinct n = 4 failing profile–start pairs of §5's 3,000-step walk (the 11 stored among them) | **3,179** |
| the TTC session's n = 5 strict-core failure (`k4/oc1_hall.md` §22; shared set {junk 2, released pick 4}) | 1 |
| RD5 (k = 5) | 1 |
| PW5 (k = 5) | **0**: it has two holders, so 1 fails |

So LIFT-EX is consistent with being a k ≤ 4 statement; PW5 is its k = 5 obstruction.

**The shape on the n = 4 data** (`k4/matching/lift_oblig.py`, `results/k4_matching/lift_oblig.log`). Over the LIFT
pairs of each of the 3,179 starts:
- *Jointly on all 3,179*, some LIFT pair satisfies Lemma LIFT-red's hypotheses below:
  - z is unfrozen after P₁;
  - P₁'s H₀ is a pair, the shared pair;
  - P₂ is canonical;
  - P₂'s head h is not P₁'s head.
- *Each of the following holds for some LIFT pair on all 3,179*:
  - h is inert at Y: its junk is worth at most its pick (in cex1, agent 0);
  - P₂'s H₀ is a pair containing z's good after P₁, a = B₁_z;
  - the only other multi-good bundle of B₂ is P₁'s pair.
- *Together with Lemma LIFT-red's hypotheses*, h can take **all** the junk on 2,987 of the 3,179. Then B₂ with J₂ given
  to h is EFX₀ (raw), and Lemma M's witness at B₂ has H = ∅. On the other 192 the LIFT pairs need H ≠ ∅: some junk goes
  to a holder of B₂.
- All of the features hold at once for one pair on 2,774 of the starts.

**Lemma LIFT-red (K4.MATCH.LIFTRED; written proof).** Assume:
- Y is a perfect start and z is a holder of Y;
- P₁ is an official chain ending at z, with |H₀¹| = 2 and H₀¹ ⊆ J ∪ {y_z}, in which the agents after the head take no
  junk;
- z is a holder of B₁ (unfrozen after P₁);
- P₂ is a canonical chain at B₁ (each agent after the head takes its predecessor's bundle alone) ending at z, and z's
  new bundle is a single good;
- P₂'s head h is not P₁'s head, and B₂_h = H₀² is h's improving set.

Then no bundle of B₂ other than h's threatens anybody, and every junk good of B₂ is unwanted. So Lemma M applies at B₂
with owner h. In particular, giving h the set X = H₀² ∪ J₂ and keeping every other base is EFX₀ iff X threatens no
agent i ≠ h at v_i(B₂_i).

*Proof.* We show that no bundle other than X threatens anybody.
1. Values only rise along both chains.
2. Every good of J₁ ∪ J₂ and of H₀¹ is unwanted at B₂:
   - goods of J: by (I2) at the perfect start;
   - y_z: it is unwanted at Y because z is a holder of Y, and values only rose;
   - a = B₁_z, released or taken by h: it is unwanted at B₁ because z is a holder of B₁, and values only rose.
3. The bundles other than X are:
   - single goods: z holds its favourite good, and the other agents of P₁ and P₂ (they take no junk) and everybody else
     hold one good;
   - P₁'s head's pair H₀¹. It may have moved one step along P₂, if P₂ passes through P₁'s head.

   A single good threatens nobody. A pair of goods that are both unwanted at B₂ threatens nobody: removing one good
   leaves one unwanted good.
4. So only X can threaten. ∎

The one remaining obligation is therefore Lemma M's condition at B₂ for owner h:

> **(LIFT-1)** Some H ⊆ J₂ has X = H₀² ∪ (J₂ ∖ H) threatening no non-holder of B₂ (other than h) at its value in B₂,
> and the exposed holders of B₂ compensated by distinct goods of H, within a matching of all of H into the holders
> of B₂.

On 2,987 of the 3,179 starts H = ∅ works, and then (LIFT-1) just says that X = H₀² ∪ J₂ threatens nobody.

**Who threatens X** (`k4/matching/lift1_threats.py`, `results/k4_matching/lift1_threats.log`; the best LIFT-red pair of
each start). At n = 4 the agents are h, z, P₁'s head k and the second sharer k′.
- k values exactly one good of X, on all 3,179.
- k′ values at most one, on all 3,179.
- z values two or three goods of X. It is the only agent X ever threatens, on 192 starts, and one junk good given to
  z fixes every one of them.

**Lemma LIFT-1 (K4.MATCH.LIFT1; written proof, k ≤ 4).** Assume Lemma LIFT-red's hypotheses. Let t be z's good at B₂
(its favourite good of R_z), X = H₀² ∪ J₂, and assume:
- **(L1)** z is unfrozen at B₂: nobody wants t;
- **(L2′)** v_z(H₀² ∩ R_z) ≤ v_z(t) + v_z(g), where g is z's most valuable good of J₂ (v_z(g) = 0 if z values none).
  This is automatic when z values at most one good of H₀². The stronger (L2), without the term v_z(g), was the first
  version; it fails on 32 of the multi session's n = 4 starts, where h takes both of z's released picks;
- **(L3)** every agent other than h and z values at most one good of X.

Let g be z's most valuable good of J₂, if z values any. Give h the set X ∖ {g}, give z {t, g}, and keep every other
base. This allocation is EFX₀ and S\*-shaped with owner h.

*Proof.*
1. *Every good of X is unwanted at B₂.* The goods of J₂ are unwanted by Lemma LIFT-red's step 2. H₀² ⊆ J₁ ∪ {a},
   and each of these goods is unwanted at B₁ (junk, y_z, and a, since z is a holder at B₁); values only rose.
2. *Bundles other than h's threaten nobody.*
   - Single goods threaten nobody.
   - The pair H₀¹ consists of unwanted goods.
   - z's {t, g}: t is unwanted by (L1), and g is unwanted by 1.
   - A bundle of at most two unwanted goods threatens nobody.
3. *X ∖ {g} threatens no agent i ∉ {h, z}.* By (L3), i values at most one good of it, and that good is unwanted
   (by 1). Removing it leaves nothing i values.
4. *X ∖ {g} does not threaten z.* A threat needs v_z((X ∖ g) ∩ R_z) > v_z(B_z), where B_z is z's final bundle. Let
   A = H₀² ∩ R_z and G = J₂ ∩ R_z. Since t ∉ X and |R_z| ≤ 4, we have |A| + |G| ≤ 3.
   - G = ∅: z gets nothing extra, and v_z(A) ≤ v_z(t) by (L2′).
   - G ≠ ∅: z holds {t, g}, with g the most valuable good of G. Then v_z(A) + v_z(G ∖ g) ≤ v_z(t) + v_z(g),
     case by case:
     - |A| = 0: G ∖ g has at most two goods. One is worth ≤ v_z(t), since t is z's favourite good, and the other
       ≤ v_z(g).
     - |A| = 1: the good of A is worth ≤ v_z(t), and G ∖ g has at most one good, worth ≤ v_z(g).
     - |A| = 2: G = {g}, and v_z(A) ≤ v_z(t) + v_z(g) by (L2′).
   - In the case G = ∅, (L2′) reads v_z(A) ≤ v_z(t).
5. *h is threatened by nobody,* by 2. Its value only rose.
6. *Shape.* z is a holder at B₂ (by (L1), it holds one good) and takes one junk good. Nobody else but h takes junk. ∎

**Case (b) of Lemma LIFT-1** (needed: the exhaustive n = 4 data have starts where z stays frozen after P₂, so (L1)
fails). Assume LIFT-red's hypotheses and (L3), and instead of (L1), (L2′):
- **(Lb)** v_z(X ∩ R_z) ≤ v_z(t), with X = H₀² ∪ J₂.

Then giving h all of X and keeping every other base (z keeps {t}) is EFX₀.

*Proof.* Steps 1–3 and 5 above do not use (L1) or (L2′). z's bundle {t} is a singleton, so it threatens nobody even
if t is wanted. X threatens z only if v_z(X ∩ R_z) > v_z(t), which (Lb) excludes. ∎

*Where k ≤ 4 is used:*
- in step 4, through |R_z ∖ {t}| ≤ 3;
- in (L3) for the second sharer k′ when k′ is off both chains. k′ values both goods of H₀¹: each single good of
  J ∪ {y_z} is worth at most its pick, and H₀¹ is improving for it. So k′ values at most one further good (Lemma
  PL(c), `k4/ksens.md`), and (L3) holds for k′ automatically.

*Check* (`k4/matching/lift1_check.py`, `results/k4_matching/lift1_check.log`; `k4/matching/multi_check.py`,
`results/k4_matching/multi_check.log`).
- On all 3,179 n = 4 failing starts of §5's walk, some LIFT-red pair meets (L1), (L2′), (L3). (L2) alone also
  suffices there: `lift1_check_L2strict.log`.
- **The multi session's walks** (proof/k4-oc1max-multi; copy at `results/k4_matching/data/multi_oc1_fail_walk.jsonl.gz`):
  4,955 failing profile–start pairs, 4,378 with n = 4 and **577 with n = 5** near the TTC session's core. Every row is
  re-verified here with this note's own code: SD picks of the stored order, perfect, no one-absorber completion at
  the picks or after any move. On all 4,955:
  - some LIFT-red pair meets (L1), (L2′), (L3);
  - the construction is raw EFX₀ on all 13,324 such pairs;
  - CM₂ holds, and EX\* is exact on the second move.
- Together that is **8,073 distinct failing starts** (7,496 at n = 4, 577 at n = 5), all satisfying LIFT-SHAPE⁺.
- The lemma's allocation, built for every one of the 8,916 pairs meeting them, is EFX₀ (raw) every time.
- These counts are with P₁'s junk-free condition. An earlier version of the lemma omitted that condition; the proof
  needs it, because middle agents taking junk would hold multi-good bundles.
- No sharer violates (L3).

**So the second move is a pure shape statement.** By Lemmas LIFT-red and LIFT-1, OC₂ at a start with no one-move
repair follows from:

> **LIFT-SHAPE⁺** (with (L2′)). There is exactly one holder z. Some official chain P₁ from a dangerous agent k ends at z, with no
> junk for its agents after the head, |H₀¹| = 2, H₀¹ ⊆ J ∪ {y_z} improving a second dangerous agent, and z unfrozen
> after P₁. Some canonical chain P₂ at
> B₁, with a head h ≠ k, ends at z and gives z its favourite good as a single good. (L3) holds, and either (L1) and
> (L2′) hold (case (a)) or (Lb) holds (case (b)).

No completion search is left in it, only which goods sit where, and the value comparisons (L1)–(L3) or (Lb):
- (L3) is automatic for the sharer off both chains;
- for P₁'s head k off P₂, (L3) fails only if P₁ = (k, z), so that a = y_k ∈ H₀², and k's fourth good is also in X
  (k values both goods of H₀¹ and its pick, so at most one further good).

It holds on all 8,073 distinct walk starts (n = 4 and n = 5; `lift1_check.py`, `multi_check.py`; case (b) was added
after the exhaustive run below) and on all 112,880 n = 4 failures (exhaustive, below).

**Every n = 4 failure (exhaustive).** compute/k4-oc1max-cert exported every n = 4 start with no one-move repair, over
every strict profile of every core hypergraph: 112,880 starts on 11 hypergraphs. The copy is
`results/k4_matching/data/two_move_starts_n4.json.gz`, from `results/k4_oc1max/two_move_starts_n4.json.gz` of PR #114.
Its completeness is that session's certificate (ordinal CEGAR, independently checked there), and its values are
integer representatives of the strict order types. Every condition of LIFT-SHAPE⁺ compares disjoint sets of goods, so
the representatives decide it for every profile of that type.
- `k4/matching/n4_exhaustive.py` (`results/k4_matching/n4_exhaustive.log`):
  - every one of the 112,880 is hard (raw) and has exactly one holder (item 1);
  - **LIFT-SHAPE⁺ holds on all 112,880**: 109,680 through case (a), 3,200 through case (b);
  - Lemma LIFT-1's allocation is raw EFX₀ on all;
  - CM₂ holds on all;
  - EX\* is exact on the second move on every 20th start (5,644).
- The witnesses are in `results/k4_matching/lift_n4_witnesses.json.gz`: P₁, H₀¹, P₂, H₀², owner, case and final
  allocation per start.
- They are re-checked by `k4/matching/check_lift_n4.py` (`results/k4_matching/check_lift_n4.log`), a self-contained
  checker that imports no code of this workstream or of k4/sdc. From the raw definitions it checks the SD picks, the
  single holder, both chains (official, improving, shape), the stated case's conditions, and that the allocation is
  the prescribed one, keeps the bases, partitions the goods and is EFX₀. **All 112,880 verified.**

So at n = 4, OC₂ at every start with no one-move repair is certified with the explicit two-move shape of LIFT-SHAPE⁺
(ledger K4.MATCH.LIFT.N4). The single holder, the shared pair, z's lift to its favourite good and the owner condition
all hold without exception. This is the shape a proof for general n has to produce.

*Another route to the same move* (multi session, `k4/oc1max_multi.md` §8 on its branch; not refereed here). Lemma
LIFT (recursion): delete P₁'s head k and its pair T; the reduced state is a perfect SD start of I − k − T, and its
one-move repairs lift back. Sub-lemma OC2-REC (evidence on all 4,955) says such a repair exists. Its
"no truly dangerous agent" observation may give (L1)–(L3) a structural proof. It is open in general, and so is item 1 (one holder), which fails at k = 5
(PW5).

**LIFT-SHAPE⁺ fails at n = 5** (`attempts/k4-matching-lift-shape.md`, `attempts/k4_matching_lift_n5.py`,
`results/k4_matching/lift_n5_cex.log`; ledger K4.MATCH.LIFT REFUTED). The first n = 5 two-move start found by
compute/k4-oc1max-cert (list 5_pure, idx 164) has n = 5, m = 8, k = 4 and a strict profile.
- Picks (7, 2, 3, 5, 4), junk {0, 1, 6}. The single holder is z = 3, with favourite good 4.
- No assignment of the junk completes, at the picks or after any one move.
- Items (1) and (2) of LIFT-EX hold: 75 first chains end at z with a shared pair inside J ∪ {y_z}.
- After none of them does a second chain end at z with z's favourite good in z's bundle. So (3) fails, and with it
  LIFT-SHAPE⁺.
- 120 pairs of chains from dangerous agents repair it (raw, any completion). 45 of them are vertex-disjoint, e.g.
  (2, 3), where 2 takes {5, 6}, then (1, 0), where 1 takes {1, 7}: two augmenting paths for two danger sets, the
  coordinator's original "deficiency = number of chains" picture. The other 75 overlap, but none of them has its
  second chain end at z with z's favourite good.
- CM₂ holds there. So does the multi session's recursion: after (2, 3), deleting agent 2 and {5, 6} leaves an SD
  start of the n = 4 instance that one move repairs.

What survives:
- Lemmas LIFT-red and LIFT-1 (conditional) and the n = 4 certificate;
- CM₂ as the general conjecture;
- OC2-REC as the general explicit form of the second move.

At n = 5 the reduced instance has four agents, and its one-move repair need not touch z.

**The recursion at every n = 4 failure** (`k4/matching/n5_census.py`, `results/k4_matching/n5_census_n4export.log`;
ledger K4.MATCH.REC.N4). This is an independent implementation of the multi session's Sub-lemma OC2-REC with Lemma
LIFT's hypothesis:
- P₁ is a canonical chain from a dangerous agent k;
- T = H₀¹, with |T| = 2 and T ⊆ J ∪ {y_end}, is improving for a second dangerous agent;
- after P₁, every agent other than k values each good of T below its holding;
- deleting k and T leaves a perfect SD outcome of the reduced instance I⁻;
- that state, at once or after one official move of I⁻, has a one-absorber completion that lifts: k keeps T and
  receives nothing, the owner is not k, and the allocation is raw EFX₀ in I. The search is a brute force over every
  owner and every one-absorber assignment.

On all 112,880 n = 4 starts with no one-move repair:
- **OC2-REC holds at every start.** The reduced start never completes without a move. It cannot: a lifting
  completion right after P₁ would be a one-move repair. In the witness found, P₁ ends
  at the holder z.
- **The reduced repair is a Lemma EX\* exchange of I⁻ at every start.** So at n = 4 the second move is a Hall
  condition (Lemma M) in the reduced instance after one sharer is settled.
- 99,840 starts also have a vertex-disjoint repairing pair of chains. The other 13,040 have none. Every start has a
  repairing pair whose second chain ends at z, as LIFT-SHAPE⁺ requires.
- CM₂ and LIFT-SHAPE⁺ hold at every start, and EX\* is exact on the second move at every 20th start (5,644).
- The witnesses (`results/k4_matching/rec_n4_witnesses.json.gz`) are re-checked by `k4/matching/check_rec.py`
  (`results/k4_matching/check_rec_n4.log`). It is self-contained and imports nothing from this workstream or from
  k4/sdc. It checks each condition from the raw definitions and enumerates the official moves of I⁻ itself (junk
  grabs, chains, rings): **112,880 / 112,880 verified.**

So at n = 4 both forms of the second move are certified: the explicit LIFT shape, and the recursion. Only the
recursion survives at n = 5.

**n = 5 walks near 5_pure #164** (`k4/matching/fail_walk.py`; evidence only). The walks keep the hypergraph fixed and
change one value by ±1..3 per step, keeping a strict connected core. Every distinct start with no one-move repair is
collected, and the walk climbs towards OC2-REC failures.
- Runs: 3,000 steps with seeds 1–4, and 20,000 steps with seeds 11–14. Logs: `n5_walk164.log`, `n5_walk164_long.log`.
  Dumps: `n5_walk164.jsonl`, `n5_walk164_long.jsonl.gz`.
- **23,924 distinct n = 5 starts** with no one-move repair (1,498 + 22,445, 19 shared). The census
  (`n5_census_walk164.log`, `n5_census_walk164_long.log`) finds, at every one of them:
  - exactly one holder;
  - LIFT-SHAPE⁺ fails;
  - some repairing pair is vertex-disjoint, so every start is of the integrator's type 4a;
  - OC2-REC holds, its reduced repair is a Lemma EX\* exchange of I⁻, and B₁⁻ never completes without a move (it
    cannot, as at n = 4);
  - CM₂ holds, and EX\* is exact on the second move (tested at every start).
- The OC2-REC witnesses are re-checked by `check_rec.py`: 1,498 / 1,498 and 22,445 / 22,445 (`check_rec_n5walk.log`,
  `check_rec_n5walklong.log`).
- The walks never leave #164's hypergraph, so this is narrow evidence. The certifier's 5_pure chunks (128
  hypergraphs with two-move starts) are the broader test.
- The same census on the multi session's 4,955 walk starts (`n5_census_multiwalk.log`; witnesses re-checked,
  `check_rec_multiwalk.log`): OC2-REC, its EX\* form, CM₂ and LIFT-SHAPE⁺ hold at every start.
  - 1,951 are type 4a, with a vertex-disjoint repairing pair. This includes all 577 at n = 5 near the TTC core.
  - 3,004 are type 4b, with no such pair, all at n = 4.
- *Cross-check with the multi session's own code.* `k4/oc1max_multi/reduce_s.py` (proof/k4-oc1max-multi at 4179bcc,
  Theorem REC-S, which gives (b) by its Theorems U and S in I⁻) was run unmodified on the n = 4 export and on both n = 5
  walk dumps (`reduce_s_n4export.log`, `reduce_s_n5walks.log`). It covers all 112,880 and all 1,498 + 22,445 starts,
  in its general form and in its start-checkable earliest-wanter form E(k). There are 0 violations of Theorems U/S,
  Lemma LIFT or Lemma SD-E.
- The smallest 4b-type start at n = 4 has (n, m, Σ|R_i|) = (4, 7, 15) and was sent to the integrator:
  - sets [[0,4,5,6],[1,2,3,5],[1,3,5,6],[2,4,6]], values [[2,3,10,6],[2,8,3,4],[3,5,7,6],[4,2,3]];
  - picks (4,5,6,2), order (3,1,2,0);
  - the head of every second move, agent 3, becomes dangerous only after the first move.

**Iterated reduction (RSD; the coordinator's question)** (`k4/matching/rsd.py`). This tests whether settling
sharers one at a time, with no other kind of move, repairs every start with no one-move repair.

A *reduction step* at a perfect SD start B of the current instance I′:
- a canonical chain P from an agent k that is dangerous in I′ takes a set T ⊆ (J′ ∪ B_end) ∩ R_k with
  v_k(T) > v_k(B_k);
- (L\*) T threatens no other agent of I′ at its value after P. For a pair this is Lemma LIFT's hypothesis;
- deleting k and T leaves a perfect SD outcome of I′ − k − T (checked over all orders).
  - MODE=E: P is instead the earliest-wanter chain E(k) of a tracked order, and the new order is the old one minus k
    (the multi session's Lemma SD-E).

RSD(d) holds when at most d steps reach a state whose one-absorber completion lifts. Lifting means: every deleted
agent keeps its T and receives nothing, the owner is a present agent, and the allocation is raw EFX₀ in I.

> **Lemma LIFT\*** (iterated lift; written proof, uses nothing about k). Let I₀ = I and I_j = I_{j−1} − k_j − T_j for
> reduction steps j = 1..r, each with (L\*). Let X be an EFX₀ allocation of I_r extending the last state. Suppose
> (Φ) no bundle of X, and no T_j with j > i, threatens k_i at v_{k_i}(T_i). Then X together with all the T_j is EFX₀
> in I.

*Proof.* Every agent's value is non-decreasing along the process: a step changes only its chain agents, which gain,
and k_j, which gains; the completion only adds goods. EFX₀ for agent a is monotone in v_a(A_a). Take agents a ≠ b.
- If both are present in I_r, X is EFX₀ in I_r, and their bundles hold only goods of I_r.
- If a = k_i:
  - a bundle of X, or T_j with j > i, is covered by (Φ);
  - T_j with j < i: a was present at step j, so by (L\*) T_j did not threaten a then, nor later.
- If a is present at step j and b = k_j, the same argument gives that T_j does not threaten a. ∎

> **Lemma PHANTOM** (written proof; |R_k| ≤ 4). Let k hold T ⊆ R_k with v_k(T) > v_k(y), where y ∉ T is its former
> pick, and let X be a bundle disjoint from T.
> 1. If |T| = 3, X never threatens k.
> 2. If |T| = 2 and R_k = T ∪ {y, ℓ}, X threatens k exactly when (P1) or (P2) holds:
>    - (P1) ℓ ∈ X, |X| ≥ 2, and v_k(ℓ) > v_k(T);
>    - (P2) {y, ℓ} ⊆ X, |X| ≥ 3, and v_k(y) + v_k(ℓ) > v_k(T).

*Proof.* X ∩ R_k ⊆ R_k ∖ T. If |T| = 3 this is ⊆ {y}, and v_k(X) − min ≤ v_k(y) < v_k(T). If |T| = 2:
- X a singleton, or X ∩ R_k = ∅: the threat is 0.
- X ∩ R_k = {y}: at most v_k(y) < v_k(T).
- X ∩ R_k = {ℓ}, |X| ≥ 2: some good of X is worth 0 to k, so the threat is v_k(ℓ).
- X = {y, ℓ}: the threat is max(v_k(y), v_k(ℓ)), which exceeds v_k(T) iff v_k(ℓ) > v_k(T).
- X ⊋ {y, ℓ}: the threat is v_k(y) + v_k(ℓ). ∎

So the **phantom constraint** the coordinator asked about is exact and small. An induction on n through reduction
steps must carry, for each deleted agent with |T| = 2, at most two constraints on the rest of the allocation, and
none for |T| = 3:
- "ℓ is alone in its bundle", when v_k(ℓ) > v_k(T);
- "y and ℓ are not together in a bundle of three or more goods", when v_k(y) + v_k(ℓ) > v_k(T).

Together with (L\*) at each step, these are exactly what Lemma LIFT\* needs.

*On the data* (logs `results/k4_matching/rsd_*.log`):

| start set | RSD with any T (canonical chains / E(k)) | RSD with pairs only | RSD⁺(1) (OC2-REC without "shared") | dead end reachable |
|---|---|---|---|---|
| n = 4, all 112,880 (exhaustive) | **d = 2 at all 112,880**, both forms; T sizes (2, 2) at 103,600, (2, 3) at 9,280; witnesses re-verified by `check_rsd.py` | d = 2 at 105,200; **fails at 7,680** | 112,880 | from 16,240 starts |
| n = 5 walks near #164, 23,924 | **d = 2 at all**, both forms; sizes (2, 2) | (not run) | 23,924 | none |

The answers to the coordinator's questions:
- **Does some RSD sequence repair every hard start?** Yes on all data: two reduction steps, then a completion, with no
  other move, at every n = 4 start and every n = 5 walk start.
- In the 112,880 n = 4 witnesses (`rsd_n4_witnesses.json.gz`):
  - the first step always takes a shared pair;
  - the second step's T is never shared;
  - at the second level there are 1 dangerous agent (80,560 starts) or 2 (32,320);
  - the second step's head was not dangerous at the picks at 27,760 starts.
- T must be allowed three goods. With pairs only, 7,680 n = 4 starts have no RSD repair. In the example examined, the
  second head needs a triple of two junk goods and the end's good. A triple carries no phantom constraint (Lemma
  PHANTOM, case 1).
- **Greedy RSD fails.** From 16,240 n = 4 starts some sequence of steps reaches a dead end: a state with no lifting
  completion and no reduction step. So an induction must choose the step, and the inductive hypothesis must carry
  the phantom constraints of the earlier steps. An example dead end, after one step: the only dangerous agent's
  improving triple threatens another agent.
- At n = 4 every RSD repair is short. The reduced instance after two steps has two agents.

What an induction on n would need, in this form, is the open statement:
> **RSD-IND (conjecture).** Let I′ (≤ 4 relevant goods per agent) be at a perfect SD start, with a family Φ of
> phantom constraints of Lemma PHANTOM's two kinds. Suppose Φ comes from earlier reduction steps with (L\*). If the
> start has no completion respecting Φ, then some reduction step with (L\*) respects Φ (both its T and the rest),
> and the reduced instance with Φ updated satisfies the hypothesis again.

Lemma LIFT\* turns RSD-IND into EFX₀ existence, with no bound on the number of moves. The dead ends show that RSD-IND
must be existential, not "every step works".

**RSD-IND is false at n = 5** (`attempts/k4-matching-rsd-lstar.md`, `attempts/k4_matching_rsd_n5.py`,
`results/k4_matching/rsd_n5_cex.log`; ledger K4.MATCH.RSDIND REFUTED). Two of the certifier's sampled n = 5 starts,
5_pure m = 10 idx 419 and m = 11 idx 447, have no RSD sequence of any depth. This is confirmed by two independent
brute forces, one with arbitrary final assignments.
- Each start has two sharers whose sets threaten an agent that only the other sharer's chain improves. So (L\*) fails
  for whichever is settled first.
- With (L\*) deferred to the final EFX₀ test, two vertex-disjoint steps repair both. That is one round of two
  simultaneous moves, the coordinator's ROUND form.
- What an induction must then carry, besides Lemma PHANTOM's phantom constraints, is **demands**. A present agent i
  threatened by a deleted T must finish with value at least v_i(T) − min_{g∈T} v_i(g). In the slot graph of Lemma M
  this is an exposed slot that must be compensated.

> **Conjecture RSD-D (K4.MATCH.RSDD).** The deferred form. At a perfect SD start (≤ 4 relevant goods per agent)
> carrying phantom constraints and demands from earlier steps, either a completion meets them all, or some reduction
> step (without (L\*)) leads to a reduced instance that satisfies the hypothesis again, with its new demands.

Lemma LIFT\* holds for RSD-D with (L\*) read at the final values. Its proof only uses that no T threatens an agent at
that agent's final value. Evidence: all n = 4 starts, the 23,924 n = 5 walk starts, and all 280 sampled 5_pure starts
(below).

**ROUND-RSD** (`k4/matching/round_rsd.py`; the coordinator's proposal). A step is a *round*: up to RMAX = 2
settlements at once, with vertex-disjoint canonical chains and disjoint T's. (L\*) is read at the round's end, so the
other settled agents of the round count at v(T_b). All of them are deleted, the reduced start must be a perfect SD
outcome, and the search recurses. RMAX = 1 is RSD.

Lemma LIFT\* holds for rounds with the same proof:
- within a round, (L\*) at the round's end covers every pair of agents present at its start, including two
  settled agents;
- monotonicity covers later rounds;
- (Φ) covers earlier deleted agents.

The witnesses are re-checked by `check_rsd.py`, which now also verifies rounds.
- **n = 4, all 112,880:** repaired at every start, always as two rounds of one settlement each. At n = 4 a single round
  of two never works. `round_rsd_n4.log`, `check_round_rsd_n4.log`: 112,880 / 112,880.
- **n = 5, the 280 sampled 5_pure starts:** repaired at every start. 150 take one round of two settlements and 130
  take two rounds of one. **5_pure m = 10 #419 and m = 11 #447 are repaired by one round of two**, where RSD fails.
  `round_rsd_5pure_s5o0.log`, `check_round_rsd_5pure_s5o0.log`: 280 / 280.
- **n = 5 walks, 23,924:** one round of two at every start, 23,924 / 23,924.

*The coordinator's threat-graph rule* (`round_rsd.py` with ROUNDS=scc / scc2 / minimal, EXPLORE=1; logs
`round_rsd_explore_*`). Draw an arc s → s′ between candidate settlements when s's T threatens an agent that lies on s′'s
chain. The conjecture was: one strongly connected component per round avoids every RSD dead end.
- Taken literally (a whole component as the round), it fails at #419 and #447. There the component also contains
  alternative settlements of the same agents, so it is never a compatible round.
- Taking only the 2-cycles of the graph as rounds (scc2), or only the pairs neither of whose members passes (L\*)
  alone (minimal), repairs every start: all 112,880 at n = 4, and all 280 5_pure (24 in one round, 256 in two).
- **But dead ends stay reachable** under every round rule. A dead end is a state with no lifting completion and no
  admissible round. They are reachable from the same 16,240 n = 4 starts as for RSD, and from 123 of the 280 5_pure
  starts, whether rounds are scc2, minimal, or any compatible pair. The n = 4 dead ends do not come from threats; one
  example examined is a state whose only dangerous agent's improving set is a triple that threatens a holder.
- So the choice of rounds must be existential, as for RSD. The rounds fix the RSD-X starts; they do not make the
  process greedy.

> **Conjecture ROUND-IND (K4.MATCH.ROUNDRSD).** At a perfect SD start (≤ 4 relevant goods per agent) carrying
> phantom constraints from earlier rounds, either a completion respecting them exists, or some round of simultaneous
> settlements, with (L\*) at its end, respects them and leads to a reduced instance that satisfies the hypothesis
> again. With Lemma LIFT\* (rounds) it gives EFX₀ existence by induction on n. Its base case is not pure (below).

**The certifier's partial n = 5 export** (compute/k4-oc1max-cert commit cd476cf7,
`results/k4_oc1max/n5/two_move_starts_n5_partial6.json.gz`). It holds 702,250 two-move starts on six 5_pure
hypergraphs (idx 374, 379, 464, 808, 778, 164), every list cut by a CEGAR time cap. A subsample of every 50th start
per hypergraph, 14,047 starts, is `results/k4_matching/data/two_move_starts_n5_partial6_s50.jsonl.gz`. Evidence
only. Results:
- every start is hard (raw) with one holder;
- ROUND-RSD repairs all 14,047. 7,358 take one round of two and 6,689 take two rounds of one; `check_rsd.py`
  verifies all of them;
- RSD (all in two steps), OC2-REC (with its EX\* form) and CM₂ also hold at all 14,047;
- LIFT-SHAPE⁺ holds at 3,448;
- 4a / 4b: 13,336 / 711;
- EX\* is inexact on the second move at 1,608.

Logs: `round_rsd_n5partial_s50.log`, `check_round_rsd_n5partial_s50.log`, `rsd_n5partial_s50.log`,
`n5_census_n5partial_s50.log`.

**The base case** (the coordinator's question; `attempts/k4-matching-rsd-base.md`; ledger K4.MATCH.RSD.BASE). The
data are all 10,109 distinct one-absorber-hard starts with a one-move repair: multi's 8,081, Hall's 1,737, and 291
PW starts. On them, pure reduction with a completion at once gives:

| form | multi (8,081) | Hall (1,737) | PW (291) |
|---|---|---|---|
| RSD, (L\*) at the step | 8,046 | 1,705 | 291 |
| ROUND-RSD (rounds of ≤ 2) | 8,046 | 1,705 | 291 |
| RSD, (L\*) deferred, deleted agents may receive junk | 8,075 | 1,731 | 291 |

- 35 distinct starts fail the first form, all with #D ≥ 2; the smallest is T3 (n = 3, m = 6).
- The T3-type failures need the settled head to absorb a junk good it does not value at the end.
- 6 starts fail every form; the smallest is ls-alt-rule-n4m7 (n = 4, m = 7). Their one-move repair has a chain agent
  after the head that also takes junk, which a reduction step cannot express. This is confirmed by the independent
  brute force `attempts/k4_matching_rsd_base.py`.

So the answer is (b): an induction through reductions keeps OC₁ in its base case (Part 1 of the Hall session's plan),
under phantom constraints.

**The certifier's first n = 5 chunk** (5_pure_s5o0, commit 259289f9 of compute/k4-oc1max-cert; OC₂^max certified
there on all 935 hypergraphs).
- Data: its summary samples up to 3 two-move starts on each of the 137 hypergraphs with one, 280 starts in all. The
  copy is `results/k4_matching/data/n5_5pure_s5o0_two_move_starts.json.gz` (and `.jsonl.gz`), with the SD orders added
  here. This is a sample, not an enumeration.
- Every start was re-verified as hard (raw) and has exactly one holder.

| mechanism (code) | starts repaired, of 280 |
|---|---|
| CM₂, first move + Lemma EX\* exchange (`n5_census.py`) | **280** |
| ROUND-P, one round of ≤ 2 disjoint OC₁′ moves (coordinator's `roundp_check.py`) | **280** (1 move: 234, 2: 46) |
| RSD-D, reductions with (L\*) deferred (`rsd.py`, LSTAR=defer) | **280** (2 steps) |
| RSD, reductions with (L\*) at the step (`rsd.py`; `check_rsd.py` verifies 278 witnesses) | 278 |
| OC2-REC, this note's implementation (`n5_census.py`; `check_rec.py` verifies 274 witnesses) | 274 |
| OC2-REC, multi's `reduce_check.py` ("SD and lifts with k keeping T") | 276 |
| REC-S, multi's `reduce_s.py` / `recs_witness.py` + `check_recs.py` | 273 |
| LIFT-SHAPE⁺ (refuted form) | 132 |

The logs are `n5_census_5pure_s5o0.log`, `check_rec_5pure_s5o0.log`, `rsd_5pure_s5o0_*.log`,
`check_rsd_5pure_s5o0.log`, `multi_tools_5pure_s5o0.log` (the multi session's code at 8924c6b3, unmodified) and
`roundp_5pure_s5o0.log` (the coordinator's code at 6faed757, unmodified).
- 4a / 4b: 240 starts have a vertex-disjoint repairing pair and 40 do not.
- The mechanisms fail together on few starts:
  - the 2 RSD failures (idx 419, 447 above) also fail OC2-REC and REC-S, and both are 4a;
  - 4b start m = 9, idx 38 fails only REC-S;
  - every other failure of OC2-REC or REC-S is 4a and is repaired by RSD.
- EX\* is no longer exact on the second move. At 60 starts, 91 first moves have a repairing second move but no EX\*
  exchange.
  - At 90 of them some repairing second move has an S\* completion. At 83 of those, a junk good is wanted after it,
    so Lemma M's hypothesis (G2)/(W′) fails there.
  - One needs a non-S\* completion.
  - CM₂ still holds at every start, through another first move.

## 7. Climbs and reproduction

**Climbs against CM** (`k4/matching/cm_climb.py`; `results/k4_matching/cm_climb_*.log`). The climbs maximize hard
starts with few CM witnesses (CAP = 10), seeded from the hard rows of §2:
- 32 runs × 3,000 steps on any instance (LOOSE);
- 32 × 2,000 on strict cores;
- 32 × 2,000 in the K4.MC2 class.

No start without a witness was found, although the 11 n = 4 failures exist. So these climbs are weak evidence, as
AGENTS.md warns. The exhaustive ordinal search is what found the failures.

**CM at n = 6, 7, sampled orders** (`k4/matching/cm_big.py`; `results/k4_matching/cm_big_*.log`; evidence only):
- 2,000 random strict profiles of the n = 6 cores with one 4-good agent, 40 random orders each: 8,325 perfect starts,
  61 hard, CM holds on all 61 (owner k on 59, the end on 2);
- 800 random K4.MC2-class cores with n = 6, 7 (`oc1_mc2_rand.gen`), 30 orders each: 4,248 perfect starts, 16 hard, CM
  holds on all 16.

**The TTC session's 84 non-core counterexamples** (`FILE=results/k4_matching/data/ttc84_oc1_counterexamples.json
python3 k4/matching/cex_deficiency.py`, `results/k4_matching/cex_deficiency_ttc84.log`).
- All 84 failing (non-maximum) starts have δ = 2, and the best single move leaves δ = 1.
- Their maximum-matching starts all satisfy OC₁, with δ = 1 on 240 and δ = 2 on 15.

```
python3 k4/matching/exact_check.py screen                    # Lemma M vs brute force (also special, suite, logs, cores:...)
python3 k4/matching/hard_starts.py screen                     # deficiency at the hard maximum-matching starts
python3 k4/matching/hard_starts.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 3000 91   # (and the other sources of §2)
NMAX=6 python3 k4/matching/hard_starts.py cex; NMAX=6 python3 k4/matching/hard_starts.py pw:7:300
python3 k4/matching/exchange.py results/k4_matching/hard_*.jsonl   # Lemma EX and Conjecture CM
python3 k4/matching/ex_profile.py results/k4_matching/hard_{special,screen,suite,logs,cores_*}.jsonl
python3 k4/matching/cex_deficiency.py                         # PW5, PW4, RD5, RD4, B<, B>, the 39 cores
python3 k4/matching/explain.py 'SETS' 'VALS' 'PICKS'          # every repairing move of one start, with EX values
python3 attempts/k4_matching_attempts.py                      # the refuted deficiency bound, by pruning-free brute force
python3 k4/matching/n4_cex.py; python3 k4/matching/cm2.py n4all; python3 k4/matching/cm2.py k5   # §5
python3 k4/matching/n4_twomoves.py                            # the two-move repairs of the n = 4 failures
python3 k4/matching/n4_walk.py 3000 2; python3 k4/matching/n4_profiles.py 3000 7   # walks / random profiles near them
DUMP=results/k4_matching/n4_failing_walk.jsonl python3 k4/matching/n4_walk.py 3000 2  # dumps the failing pairs (§6)
python3 k4/matching/lift_shapes.py; python3 k4/matching/lift_oblig.py               # Conjecture LIFT-EX and its shape
python3 k4/matching/lift1_threats.py; python3 k4/matching/lift1_check.py             # Lemma LIFT-1 and (L1)-(L3)
python3 k4/matching/multi_check.py                            # the multi session's 4,955 failing pairs (§6)
python3 k4/matching/n4_exhaustive.py; python3 k4/matching/check_lift_n4.py   # LIFT-SHAPE+ on all 112,880 n = 4 failures (§6)
python3 attempts/k4_matching_lift_n5.py                       # LIFT-SHAPE+ and LIFT-EX fail at n = 5 (§6)
cd k4/matching; EXACT_STRIDE=20 REC_WIT=../../results/k4_matching/rec_n4_witnesses.json.gz python3 n5_census.py n4export
python3 check_rec.py ../../results/k4_matching/data/two_move_starts_n4.json.gz ../../results/k4_matching/rec_n4_witnesses.json.gz
                                                              # OC2-REC on all n = 4 failures, and its checker (§6)
EXPLORE=1 TSIZE=any python3 rsd.py n4export; MODE=E TSIZE=any python3 rsd.py n4export; TSIZE=2 python3 rsd.py n4export
TSIZE=any RSD_WIT=../../results/k4_matching/rsd_n4_witnesses.json.gz python3 rsd.py n4export
python3 check_rsd.py ../../results/k4_matching/data/two_move_starts_n4.json.gz ../../results/k4_matching/rsd_n4_witnesses.json.gz
                                                              # iterated reduction (RSD) and its checker (§6)
DUMP=../../results/k4_matching/n5_walk164.jsonl python3 fail_walk.py cex5 3000 1 2 3 4   # n = 5 walks (§6)
DUMP2=results/k4_matching/n4_nonsstar_walk.jsonl python3 k4/matching/n4_walk.py 3000 2; python3 k4/matching/mc_check.py   # Lemma M^c (§5)
python3 k4/matching/cm_big.py cores6 2000 40 31               # CM at n = 6 (sampled orders)
CAP=10 SEEDFILES=... python3 k4/matching/cm_climb.py 32 2000 22 3 6 [MC2]    # climbs (LOOSE=1 for any instance)
```
Each command takes seconds to two minutes on 4 CPUs.
