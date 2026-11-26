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
| **Conjecture CM₂** (§5) | from every perfect start, some first move leads to a state where a Lemma EX\* exchange repairs. CM₂ ⟹ OC₂ at perfect starts ⟹ OC₂^max ⟹ TARGET₄ | evidence: all 30 hard maximum-matching starts of the 11 n = 4 failure instances, every start visited by the walks near them (OC₁ failing: 4,513 visits, 3,308 distinct; OC₁ only non-S\*: 88), PW5, RD5. Where OC₁ fails, the first moves after which an EX\* exchange repairs are exactly those after which any second move repairs |
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
   - in each, a first move followed by a Lemma EX\* exchange repairs (Conjecture CM₂, §5). The same holds at all 3,308
     distinct failing profile–start pairs that value walks find near the 11.
   CM₂ implies OC₂^max, the campaign's current target.

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
  - wherever OC₁ fails (214 + 4,299 visits; 129 + **3,179 distinct failing profile–start pairs**, so OC₁^max failures
    are plentiful near the 11), CM₂ holds and EX\* is exact on the second move;
  - wherever some single move gives an S\* completion, an EX\* exchange exists;
  - but 14 + 74 visited starts satisfy OC₁ only through a *non-S\** one-absorber completion. A frozen agent takes a compensated junk
    good, which Lemma 1's (S1) allows and S\* does not. No single move gives an S\* completion there, so CM fails
    while OC₁ holds. CM₂ holds on all of them.
  - So EX\* is exact relative to the S\* shape on the data. The S\*-shape gap is real near the failures, and CM₂
    absorbs it with a second move.
- 6,250 hard perfect starts from 3,000 random profiles of each of the 11 hypergraphs (`n4_profiles.py`) contain no
  failure at all. Random profiles miss the failure region.
- Evidence only: the n = 4 failures were found only by an exhaustive ordinal search. Random profiles (11M orders at
  n = 5) and the climbs of `k4/matching/cm_climb.py` missed them (§6).

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

## 6. Climbs and reproduction

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
python3 k4/matching/cm_big.py cores6 2000 40 31               # CM at n = 6 (sampled orders)
CAP=10 SEEDFILES=... python3 k4/matching/cm_climb.py 32 2000 22 3 6 [MC2]    # climbs (LOOSE=1 for any instance)
```
Each command takes seconds to a minute on 4 CPUs.
