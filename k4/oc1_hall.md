# A Hall-type count for OC₁ (workstream `proof/k4-oc1-hall`)

Target: Conjecture OC₁ (K4.SDC.OC1, `k4/sdc.md` §29), which implies TARGET₄. For every serial-dictatorship order, the
picks have a one-absorber completion, or after one improving chain the bases have one. Notation is that of
`k4/sdc.md` §30. Y = SD(π), J = junk (unpicked goods), p_i = v_i(Y_i). Agent i *wants* g ∉ B_i if
v_i(g) > v_i(B_i). F = frozen agents (single-good holders whose good someone wants). D ⊆ F = dangerous agents (frozen
agents that value a junk good). W_x = the agents that want x's good.

**Conjecture OC₁-ED\* (agreed with k4/ttc.md; K4.OCH.ED).** For every serial-dictatorship order of every instance
in which every agent values at most four goods:
- **(a)** the picks have a one-absorber completion; or
- **(b)** some *ED chain* leaves an S\* completion owned by x₀ or x_t.

An ED chain is an improving chain x₀, x₁, …, x_t in which:
- x₀ is dangerous (frozen, and values a junk good), and takes H₀ ⊆ J ∪ B_{x_t};
- every middle agent x_i (0 < i < t) takes exactly its predecessor's base B_{x_{i−1}}, which it wants;
- only the head x_t may add junk: it takes B_{x_{t−1}} ∪ H_t.

An S\* completion gives at most one junk good to each single-good holder that nobody wants, nothing to frozen agents
and multi-good holders, and the rest to the owner.

**REFUTED as stated (§16), also on strict cores.** The TTC session found OC₁ counterexamples at n = 6, m = 10
(`claude/k4-ttc`); they are verified here independently.
- Instance 36 of their list is rejected by `k4/c4_verify_H/hcore.py`'s `is_core4` only because agent 2's values tie.
- Its two strict perturbations B< and B> pass `is_core4`, so they are strict connected k = 4 cores. OC₁ fails on both
  for 24 of 720 orders.
- In them, agents 1 and 3 each have two private goods (allowed, since p + q < s + t). K4.MC2 (CERTIFIED) excludes such
  agents from minimal counterexamples to TARGET₄.

**UPDATE (§22): OC₁^max, OC₁-ED\*^max and the R1-priority forms are REFUTED at n = 4** (the certifier
`compute/k4-oc1max-cert`, verified by the coordinator). Both starts have |D| ≥ 2, with two dangerous agents sharing a
junk danger pair, and two sequential moves repair them. §21 (|D| = 1) is unaffected.

**FORMER CENTRAL CONJECTURE (§19): OC₁-ED\*^max.** For every serial-dictatorship order whose picks form a *maximum
matching* of the agent–good graph, (a) or (b) above holds.
- Such orders always exist, so OC₁-ED\*^max implies TARGET₄ on cores.
- Lemma MAX (§19, proved) removes the pickless-agent pigeonhole behind every known counterexample.
- Evidence:
  - all 2,071 one-absorber-hard maximum-matching starts of this note's data (n ≤ 5, every order);
  - all 1,950 maximum-matching orders of the 39 known core counterexamples complete *at the picks* (coordinator,
    `results/k4_sdc/oc1_max_orders_ttc_cores.log` on `claude/kind-lamport-y8fdme`).
- Alternative with the same evidence: OC₁-ED\* for R1-priority orders (1,855 of 1,855 hard starts, §18). The two order
  classes are incomparable on the data (§19).

**UPDATE (§18): OC₁ and OC "for every order" also fail inside the K4.MC2 class.** The TTC session's
n = 5, m = 9 core (verified here) has picks with no completion at all, one-absorber or free, after any one move.
Every R1-priority order still works. The surviving targets are therefore the R1-priority forms (OC₁ and OC₁-ED\* for
R1-priority orders, on the K4.MC2 class), together with MD and SD-C.

**Agreed targets before §18 (with the TTC session, `attempts/k4-ttc-oc1-counterexample.md` on `claude/k4-ttc`).**

*Primary.* OC₁, unchanged, on strict connected k = 4 cores in which no agent has two private goods (the K4.MC2
class). It is open, and it implies TARGET₄. The same holds for its ED form, OC₁-ED\*.

*Safety net.* The forms with empty bases treated as free, in case a counterexample in the K4.MC2 class appears:
- *One-absorber completion relative to empty bases:* at most one agent with a nonempty base receives two or more junk
  goods. Agents with an empty base may receive any number.
- *S\*ᵖ:* S\* plus agents with an empty base taking any number of junk goods.
- *OC₁ᵖ:* for every order, the picks, or the bases after one improving move (an addition, chain or ring of `de_free`),
  have such a completion.
- *OC₁-ED\*ᵖ:* for every order, the picks have an S\*ᵖ completion, or some ED chain leaves one owned by x₀ or x_t.

**The form that is still open and still implies TARGET₄** (via K4.MC0, K4.MC2 and the n = 5, 6 certificates):
OC₁-ED\* for *strict connected k = 4 cores with n ≥ 6 in which no agent has two private goods*. A weaker variant is
OC₁ᵖ-ED\*, where agents without a pick take any number of junk goods.

OC₁-ED\* would imply OC₁, hence MD and TARGET₄. Lemma 2\* (§6) is the exact invariant for (b). Evidence: §14, all 2,308
one-absorber-hard starts with n ≤ 5, every order. The TTC session's data are in `k4/ttc.md` §8–§10.

Code: `k4/oc1_hall/` (`ohlib.py` is shared). Logs: `results/k4_oc1_hall/`. Every check uses the raw EFX₀ definition
(`ohlib.efx0`), and its own enumeration rather than SAT unless stated. Data sets are those of `k4/sdc`:
- special: T3, Q2, r4253, r3943;
- screen: 168 instances;
- suite: 158 instances;
- logs: the 1,534 hard profiles printed in `results/k4_sdc/*.log`, n ≤ 4;
- random strict core profiles: 3,000 with n ≤ 3 (seed 91), 1,500 with n = 4 (seed 92), 150 with n = 5 (seed 93).

Every order is tried, n ≤ 5. Everything called *evidence* is evidence only (PROMPT.md §5 rule 3).

## Status (end of burst 8)

| | statement | status |
|---|---|---|
| Lemma 1 | slot form of the one-absorber completion at SD picks: conditions (S1), (S2) | written proof; agrees with SAT on all 14,461 distinct starts, and with raw brute force on special and screen |
| Lemma 2 | slot count: under (G1), (G2), (G5′), (H3), an S\* completion with owner o exists iff some kept-out set H satisfies (H1) and \|H\| + θ(H) − ν(H) ≤ \|N₁\| | written proof (§4). Check (`lemma2_true_check.log`): H ranges over transversals of the demands only, at the picks and at every post-chain state (n ≤ 4). The count agrees with the raw S\* enumeration on all 248,341 owner tests. The (⇐) construction, with DT's moves actually used in 73,410 cases, is EFX₀ every time |
| Lemma 2\* | the same with (G5′), (H3) dropped: exposed holders that are not movable (they want a good of B_o, or have a danger set inside B_o) must be compensated, i.e. matched to a good of H | written proof (§6); `lemma2star_true_check.log`: 330,992 owner tests (frozen and multi-good owners included), 0 mismatches, DT's moves used in 76,395 |
| Prop. 5 (small ω) | at the picks, if some unfrozen o has ω_o = \|J\| − \|N₁(o)\| ≤ 1, the picks have an S\* completion with owner o; so every hard start has ω_o ≥ 2 for every unfrozen o | written proof (§9); 14,756 owner tests with ω ≤ 1, 0 failures |
| Cor. 2.1, Lemma 4 | (H2) is Hall's condition for a system of distinct admissible holders of H, so C(B, o) = a transversal of the demands with an SDR into the slots; robust helpers always suffice | written proofs (§6) |
| Prop. 3 (T2⁺) | f = 1: if some o ≠ x has v_x((J ∪ {Y_o}) ∩ R_x) ≤ p_x, the picks have an S\* completion with owner o | written proof (§5) |
| **Theorem F1₁** | f = 1, exactly one wanter, n ≥ 3: the picks or one swap x → w have an S\* completion. This covers the open sub-case "x improves only with three goods" of `k4/sdc.md` §30 | written proof (§5); the proof run literally succeeds on all 3,329 such starts |
| Finding S\* (**refuted at n = 6**, §16) | OC₁ holds with the narrower completion S\*: one owner (any agent); one junk good each for single-good holders that are not frozen; nothing for frozen agents and multi-good holders | evidence: 0 failures on 14,461 distinct starts with n ≤ 5 (every order), and on 48,123 distinct starts with n = 6–10 (sampled orders, SAT, §7) |
| Finding B | at every hard start (no S\* completion), some repairing chain starts at a dangerous frozen agent k, and after it k owns: all but 1 of the 2,676 hard starts with n ≤ 5. In that one start (§29's dichotomy instance) the chain end owns. At n = 6–10, every one of the 1,300 hard starts is repaired by a chain after which a dangerous agent that gave its pick away owns. 80 adversarial climbs (§10) never broke the "k or end owns" form; 77 reached a start with exactly one such repair | evidence |
| Finding F1 | f = 1: at every hard start, some swap x → w with an *inclusion-minimal* improving set H₀ ⊆ J ∪ {Y_w} repairs with x as owner, also when \|W_x\| = 2 | evidence: all 100 f = 1 hard starts |
| Finding F1W | f = 1, several wanters: hard starts occur only at n = 3 in the data (n − 2 = 1 slot). For n ≥ 4, the picks have an S\* completion with a wanter as owner on 219 of 220 starts | evidence (§5) |
| Conjecture F1W (K4.OCH.F1W) | f = 1, several wanters, n ≥ 4: if some owner o ≠ x needs at most one of x's junk goods kept out (τ(o) ≤ 1), the picks have an S\* completion. With n ≥ 3, τ(o) ≥ 2 for every o only if x's three lower goods are junk and every pair of them beats a, and then a swap is needed (red-b1) | evidence (§11): 0 failures in 1,243 starts with τ ≤ 1 at n = 4–8, 319 of them with τ = 1 (τ = 0 is Proposition 3) |
| Finding M (§12) | the coordinator's matroid-partition form (a transversal matroid of slots, one matroid per frozen agent, Rado's condition) is a valid sufficient condition, and Rado's condition equals the model when the D_i are disjoint and all matroids. It is **not exact**, because of (i) overlapping D_i (19% of owner tests), (ii) non-matroid {xy, xz} agents, and (iii) even with disjoint matroids, the strictness clause (150 tests) and exposure that depends on H (25 tests). Lemma 2's count, which has both, is exact | evidence: 20,648 owner tests |
| "Frozen slots are not needed" (§13) | **refuted at n = 4**: five one-move repairs, none of S\* shape (`attempts/k4-oc1-hall-frozen-slots.md`) | `frozen_slot_cex.log` |
| Finding C (§13) | outside canonical chains, only 20 configurations are left. Every hard start of every data set (n ≤ 5) has a canonical repair from a dangerous agent with owner k or end, except 20 distinct configurations (n = 3–5, smallest T3), listed in `no_canonical.json`. Each of those has a repair from D with owner k or end and exactly one non-canonical step: one middle agent takes its predecessor's good together with junk (17), or k just adds junk to its base (3) | evidence |
| **Conjecture OC₁-ED\*** (§14; agreed with the TTC session's OC₁-ED); **refuted as stated** by the TTC session's n = 6 instances (§16) | for every order: the picks have a one-absorber completion, or some ED chain (x₀ dangerous; middle agents take exactly their predecessor's pick, which they want; only the head x_t may add junk) leaves an S\* completion owned by x₀ or x_t | evidence: all 2,308 one-absorber-hard starts (n ≤ 5). With "S\*" also in the first alternative it fails only on lb4-owner-needs-from-base-n4m8 (2 starts), which complete at the picks with a compensated frozen slot |
| Finding D1 (§15) | one dangerous agent k: on all 197 one-absorber-hard starts with \|D\| = 1, some ED chain from k with an *inclusion-minimal* improving H₀ leaves an S\* completion owned by k (rule ED-MIN). The swap (t = 1) is enough whenever f = 1, but fails on 19 configurations with f ≥ 2, listed in `d1_swapmin_fails.json` | evidence |
| **Lemma D1-red, Prop. 3′, Lemma D1-chain** (§21) | D = {k}, hard start. k has a canonical chain (heads hold picks at maximum-matching starts), and every chain end's pool J ∪ B_{x_t} is improving for k (Prop. 3′, Prop. 3 carried to \|D\| = 1). After any canonical chain with an improving H₀, owner k: (G1), (G2) hold; the only agent that can be threatened by the pool is the head x_t, and only if x_{t−1}'s pick has a second wanter (HEAD); the only non-movable holders are those crowded by H₀ (CROWD). With neither, k owns an S\* completion | written proofs (§21); P1–P5 checked at all 197 starts, 0 violations; all 282 chains free of HEAD and CROWD repair |
| **Lemma D1-C₀, Prop. D1-C′** (§21) | favourites duality: a holder off the chain is admissible for its favourite pool good, so hardness forces an improving set of k avoiding any set of distinct favourites in J. Hence every canonical chain without HEAD repairs with owner k, except in the residual cases C-a (shared favourite), C-b (every such H₀ crowds the head and contains Y_{x_t}) and C-c (a favourite is Y_{x_t}) | written proofs; `d1_crowd.log`: 224 of 227 chains without HEAD covered, 0 violations; the 3 others are C-b, all copies of lb4-n2m5-upgrade (n = 2) |
| Sub-lemma D1-H(ii) (§21; K4.OCH.D1H): **REFUTED in canonical form** (D1H-X); replaced by D1-HJ of `proof/k4-d1` (the head may add at most one junk good) | a longest canonical chain with HEAD (all second wanters are then unfrozen at the picks): the chain itself, or the one through a second wanter, repairs with owner k. With the rows above, this implies Finding D1 outside C-a to C-c | **open**; evidence 14/14 paths; smallest lil-noncore-n3 and log557 (n = 3) |
| Conjecture D1-LONG (§21): **REFUTED in canonical form** (D1H-X, n = 3, m = 8; `attempts/k4-oc1-hall-d1-long.md`); the ED-MIN form of §15, which allows head junk, survives | some *longest* canonical chain from k, with some minimal H₀, repairs with owner k. A longest chain is never in HEAD's case H-i (proved), so only H-ii (a second wanter unfrozen at the picks) and CROWD remain | evidence: 197/197 starts with n ≤ 5, every order (every longest chain: 196; exception log557); 309/309 sampled hard starts at n = 6–8 (SAT); adversarial climbs at n = 4, 5 bottom out at one repairing pair |
| **OC₁^max, OC₁-ED\*^max, R1-priority forms** (§22) | **refuted at n = 4** (certifier, 11 cores; TTC, an n = 5 core). Every known failure has \|D\| ≥ 2 with a pool danger set shared by two dangerous agents. Two moves repair. OC₂^max is certified for n ≤ 4 (`compute/k4-oc1max-cert`) | analysed here: `oc1max_cex_analysis.log`, `oc2_cases.log` |
| Lemmas M, EX of `proof/k4-matching` (§23.1) | second reading: M is correct; EX is correct as a sufficient condition but not exact (it cannot compensate the head: lb4-n2m5-upgrade) | read here; `ex_not_exact.log` |
| **Sub-lemma OC2-LIFT** (§23.3; K4.OCH.LIFT) | with no one-move repair, a canonical first chain from D is followed by a move that removes every DEMAND agent (starts at it or unfreezes it) and completes. The coordinator's literal form, a chain from the DEMAND agent, holds on only 6 of 12 | **open**; evidence 12/12 known failures; smallest 4_n4_3#58 (n = 4, m = 7) |
| Case tree for OC₂^max (§23.2) | 15 leaves with status and owner session; open: 3b (all-HEAD, k4-d1), 4d SLOT and 4e RING (k4-oc1max-multi), 4f (unverified), 5 OC2-LIFT, 6 (three moves, certifier) | plan |
| **Lemma MAX** (§19) | if the picks form a maximum matching, no agent reachable from a pickless agent by an alternating path values a junk good. So no pickless agent wants a dangerous frozen agent, or any agent on a want-chain above one, and the pickless-bin pigeonhole of §16/§18 cannot form | written proof (§19); checked at every maximum-matching start of special, screen and the K4.MC2 core |
| refuted | the GDT shape (frozen agents take nothing, owner unfrozen) is too narrow for OC₁: 9 distinct screen starts have no repair in it | `attempts/k4-oc1-hall-gdt-shape.md` |
| refuted | canonical chains only (each middle agent wants its predecessor's pick, no middle junk): 15 of 234 screen hard starts have no canonical repair (e.g. adaptive-p1, where the middle agent gains only with a junk good) | `attempts/k4-oc1-hall-canonical-chains.md` |
| refuted | a single culprit (LB⁺'s bad case: some owner fails only because of one frozen agent): false at about 30% of the hard starts | `attempts/k4-oc1-hall-single-culprit.md` |
| refuted | a rule from the order for the chain's first agent (every k ∈ D; first or last of D in π; most wanters) | `attempts/k4-oc1-hall-order-rule-k.md` |

**Scope remark.** By K4.MC0 (CERTIFIED), a minimal counterexample to TARGET₄ is a connected k = 4 core with strict
types and n ≥ 5, with at least three 4-good agents if n = 5. K4.R5, K4.R5c, K4.R5d and K4.R5p certify every such core
with n = 5, and K4.R6a every one with n = 6 and one 4-good agent. So OC₁ for connected strict k = 4 cores with n ≥ 6
already implies TARGET₄. The exceptions at n = 2, 3, where only a frozen owner works (§5), do not matter for TARGET₄.
The data of this note, however, have n ≤ 10, and those with every order tried have n ≤ 5.

**The statement that remains** (evidence for it: Findings S\* and B, in the language of Corollary 2.1):

> **Conjecture OC₁ᴴ (K4.OCH.OC1H).** For every serial-dictatorship order, either:
> - some agent o has, at the picks, a transversal of the demands with a system of distinct admissible holders
>   (Lemma 2\*); or
> - some improving chain starting at a dangerous frozen agent k reaches a state where k, or the chain's end, has one.

By Lemma 2\* this implies OC₁ (with the S\* shape), hence MD and TARGET₄.

The invariant is Lemma 2\* (S\* with any owner). Compensated frozen slots are not needed on this note's data (§13), but they are
needed at an n = 4 start (`attempts/k4-oc1-hall-frozen-slots.md`). By Finding C, the chain
lemma may be restricted to canonical chains from D plus at most one junk-assisted middle step.

Next (after the refutation of §16, everything restricted to the K4.MC2 class of strict connected cores in which no
agent has two private goods):
0. **Finding D1** (§21; D1-H(ii) and C-a to C-c are now worked on in `proof/k4-d1`, and |D| ≥ 2 in
   `proof/k4-oc1max-multi`). Left: Sub-lemma D1-H(ii), for a longest chain whose head is frozen by a second wanter that
   is unfrozen at the picks (smallest lil-noncore-n3, log557), and the residual cases C-a to C-c of Proposition D1-C′,
   which are absent from the data at n ≥ 3. Then |D| ≥ 2: disjoint danger sets (one chain per dangerous agent, Lemma
   PL's "≤ 1 pool good left" for the others) and shared ones (PWk(a) as the model).
1. f = 1 with several wanters, n ≥ 4: the picks with a wanter as owner (Corollary 2.1, with helpers). One n = 4 start
   (red-b1-blocked-improvement) needs the swap, because x needs two goods kept out and only one admissible holder
   exists.
2. f = 2 (§8): the chain removes both demands, by passing through the other frozen agent or by unfreezing it. A count
   for "after the chain" needs Lemma Ωʳ's unfreezing term inside Corollary 2.1.
3. The chain lemma in general. Proposition 5 shows the chain must beat a junk excess ω ≥ 2, up to 8 on the data.
4. Not a route: with one dangerous agent k but other, non-dangerous frozen agents present, Proposition 3's analogue
   is Lemma GDT's (G4). DT₁'s swap then breaks, because the released pick Y_w can make another frozen agent dangerous.

## 1. Lemma 1: the slot form at serial-dictatorship picks

Recall from `k4/sdc.md` §2:
- (I1) every good that i prefers to Y_i was picked earlier;
- (I2) every junk good g ∈ R_i ranks below Y_i for i (if Y_i is none, then R_i has no junk good).

A one-absorber completion gives at most one agent o (the absorber or owner) two or more junk goods, and every other
agent at most one. Write z_j for the junk good of j ≠ o (or none), X_j = {Y_j, z_j}, and
X_o = {Y_o} ∪ (J ∖ {z_j}). Let t_i = v_i(X_i).

**Lemma 1 (K4.OCH.SLOT).** These are EFX₀ exactly when:
- **(S1)** for every j ≠ o holding a pick and a junk good z_j, every agent i that wants Y_j has t_i ≥ v_i(Y_j); and
- **(S2)** X_o threatens nobody: no T ⊊ X_o with T ⊆ R_i and v_i(T) > t_i, for i ≠ o.

*Proof.*
1. Bundles with at most one good are never strongly envied.
2. Take a bundle X_j = {Y_j, z_j} with j ≠ o, and an agent i ≠ j. Removing one good leaves {Y_j} or {z_j}.
   - By (I2), v_i(z_j) ≤ p_i ≤ t_i.
   - If Y_i is none, then z_j ∉ R_i.
   - So the only possible violation is v_i(Y_j) > t_i ≥ p_i, which means that i wants Y_j and (S1) fails for i.
3. A bundle X_j with Y_j none and one junk good is a singleton.
4. That leaves X_o, which is condition (S2) by `k4/sdc.md` Lemma 2(b). ∎

*Check* (`k4/oc1_hall/slot_check.py`, `slot_check.log`; `slot_check_brute.log` with `BRUTE=1`). On every distinct
start of every data set, "some o satisfies (S1)–(S2)" agrees with `k4/sdc/oc_absorb.extends_A`, the SAT test:
- special 28, screen 775, suite 726, logs 4,328;
- random: 4,583 (n ≤ 3), 3,449 (n = 4), 572 (n = 5).

On special and screen, the set of working absorbers also agrees with the raw brute force `ohlib.absorb_brute`, which
enumerates every one-absorber placement and checks EFX₀ from the definition.

**Frozen slots are used.** Lemma 1 lets a frozen agent j take a junk good when every wanter of Y_j is compensated.
The wanter is either the owner or holds its own junk good. GDT's shape forbids this: frozen agents take nothing and
the owner is not frozen. That shape misses 77 of the 581 completable screen starts (71 of 530 on the suite). In each
of these, some unfrozen owner works once frozen agents may take compensated slots, except 7 logged and 25 random
starts where only a frozen owner works.

## 2. The completion shape S\* suffices for OC₁ (evidence)

**Shape S\*.** At a state B (bases B_i ⊆ R_i, junk J):
- one owner o, which can be any agent: frozen, or holding several goods;
- the *holders*: agents with at most one base good that nobody else wants. Each holder other than o takes at most
  one junk good;
- all other agents (frozen agents, and holders of two or more goods) take nothing;
- the completion must be EFX₀ (raw check).

**Finding S\*** (`k4/oc1_hall/oc1_gdt.py` with `OWNERS=any`, `oc1_sstar.log`). For every order, the picks have an S\*
completion, or after one improving chain (`k4/sdc/de_free.py` chain moves) the bases have one. Failures: 0 on every
data set (14,461 distinct starts; 121,556 orders).

Variants on the screen set (`oc1_shapes_screen.log`):

| owner | holders | distinct starts not repaired |
|---|---|---|
| unfrozen single-good holder | unfrozen single-good holders (GDT's shape) | **9** (A131, B131, GM4, gap-ivmax-n5-m9) |
| unfrozen single-good holder | every single-good holder | 9 |
| any agent | unfrozen single-good holders (**S\***) | 0 |
| any agent | every single-good holder | 0 |
| unfrozen single-good holder | every agent | 0 |

So, after the chain, what matters is who owns, not who else takes junk. The owner is usually the chain's first agent,
which now holds two or three goods (§3).

## 3. Which chain repairs (evidence)

`k4/oc1_hall/chain_shapes.py`, `chain_shapes.log`. A *hard start* is a start with no S\* completion. For each one, the
script lists every repairing chain (all descriptions) with every owner that works afterwards. A chain is
*canonical* when:
- each x_i (i ≥ 1) wants B_{x_{i−1}} and takes no junk;
- the end is unwanted, or its pick goes to x₀ (inside H₀).

| hard starts | x₀ ∈ D, owner x₀ | x₀ ∈ D, owner x_t | canonical from D, owner x₀ |
|---|---|---|---|
| special 17 | 17 | 17 | 15 |
| screen 234 | 234 | 219 | 217 |
| suite 233 | 233 | 226 | 216 |
| logs 1,470 | 1,469 | 1,456 | 1,449 |
| random n ≤ 3: 436 | 436 | 431 | 436 |
| random n = 4: 255 | 255 | 255 | 254 |
| random n = 5: 31 | 31 | 31 | 31 |

- *The only start without an owner-x₀ repair* is the strict-dichotomy instance of `k4/sdc.md` §29 (log1462: n = 3,
  picks (3, 6, 1)). There agent 0 takes its danger set {0, 2}, which is also agent 2's danger set, so the owner must be
  the chain end 1. This is the Theorem B₄ shape.
- So the k = 4 analogue of LB⁺'s Theorem B is: the chain starts at a dangerous frozen k. It passes k's pick along
  wanters. k takes an improving set H₀ (often its own danger set) from J ∪ B_{x_t}. Afterwards k owns (LB⁺'s
  Theorem B), or the end owns (Theorem B₄).
- 17 screen hard starts have no canonical repair with owner x₀, and 15 have none with owner x₀ or the end (§6). There
  a middle agent must take junk, or must gain without wanting its predecessor's good alone.

**f = 1** (`k4/oc1_hall/f1_study.py`, `f1_study.log`). Exactly one frozen agent x. Its wanters W hold their second
goods, and every other agent holds its top. On every f = 1 hard start:
- 13 + 2 screen, 13 + 2 suite, 17 + 3 logs, 46 + 2 random n ≤ 3, 2 random n = 4 (|W| = 1 + |W| = 2), 100 in all;
  none among the special instances or the random n = 5 profiles;
- some swap x → w (w takes Y_x; x takes an inclusion-minimal set H₀ ⊆ (J ∪ {Y_w}) ∩ R_x with v_x(H₀) > p_x; Y_w ∖ H₀
  becomes junk) has an S\* completion with owner x;
- "every minimal H₀, owner x" fails on 5 of them (2 logs, 2 random n ≤ 3, 1 random n = 4).

So the data cover both open sub-cases of `k4/sdc.md` §30 (several wanters, three-good improvements). §5 proves the
three-good one when there is a single wanter.

## 4. Lemma 2: the slot count

**Setting.** A state B, an owner o, and N₁ the holders other than o: single-good or empty holders whose good nobody
else wants. Q = N ∖ (N₁ ∪ {o}) are the others. W_o = B_o ∪ J. Write threatened(i, S, t) for "some h ∈ S has
v_i(S ∖ h) > t". Hypotheses:
- **(G1)** no bundle B_q, q ∈ Q, threatens anybody at the base values;
- **(G2)** no junk good is wanted;
- **(G5′)** no agent of N₁ wants a good of B_o;
- **(H3)** every i ∈ N₁ has |B_o ∩ R_i| ≤ 1 or v_i(B_o ∩ R_i) ≤ v_i(B_i).

For H ⊆ J, define:
- E(H): the agents i ∈ N₁ with threatened(i, W_o ∖ H, v_i(B_i)), the *exposed* holders;
- θ(H) = |E(H)|;
- ν(H): the largest number of exposed holders that can be given distinct goods h ∈ H ∩ R_i with
  not threatened(i, W_o ∖ H, v_i(B_i) + v_i(h)). This is a bipartite matching.

**Lemma 2 (K4.OCH.COUNT).** An S\* completion with owner o (junk only to o and, one good each, to N₁) exists iff some
H ⊆ J satisfies both of the following:
- **(H1)** no q ∈ Q has threatened(q, W_o ∖ H, v_q(B_q));
- **(H2)** |H| + θ(H) − ν(H) ≤ |N₁|.

*Proof.*
(⇐) Fix H. Match ν(H) exposed holders to goods of H as in the definition of ν. Place the other goods of H in the slots
of unexposed holders. That is possible because |H| − ν(H) ≤ |N₁| − θ(H), which is (H2). The θ(H) − ν(H) unmatched
exposed holders keep their slots free. Let L = J ∖ H and run Theorem DT's moves (m1), (m2) (`k4/sdc.md` §6) for the
unmatched exposed holders, inside the relevant sets R′_i = {y_i} ∪ (W_o ∩ R_i), taking goods only from L.
- In R′_i, y_i is the top: junk ranks below y_i by (G2), and goods of B_o do too by (G5′). So DT's (F1) and (F4) hold
  inside R′_i.
- (m1): a danger set T ⊆ X_o ∩ R_i has at least two goods. If it lay inside B_o, then |B_o ∩ R_i| ≥ 2 and
  v_i(B_o ∩ R_i) ≥ v_i(T) > v_i(B_i), against (H3). So T meets L, and i takes a good of T ∩ L.
- (m2) is the same with T = {b_i, c_i}.
- DT's potential (robust matched agents, matched agents) rises at every move, so the moves stop. Then every
  unmatched exposed holder is robust inside R′_i or has no danger set inside X_o.

Now check EFX₀.
- Matched exposed holders are safe by the choice of their goods: X_o only shrinks, and threatened is monotone.
- Unexposed holders are safe, since X_o ⊆ W_o ∖ H.
- Agents of Q are safe by (H1).
- Two-good bundles {y_j, z} (j ∈ N₁) threaten nobody: y_j is unwanted and z is unwanted by (G2), as in Lemma 1.
- Bundles of Q threaten nobody by (G1): values only rise.
- So only X_o could threaten, and it threatens nobody.

(⇒) Let H be the set of junk goods given to N₁.
- The agents of Q are safe, so (H1) holds.
- Every exposed holder is safe in the completion, so it must hold a good of H that makes it safe, and ν(H) = θ(H).
- So (H2) reads |H| ≤ |N₁|, which holds because each holder takes at most one good. ∎

*Remarks.*
1. Lemma GDT (`k4/sdc.md` §30) is the case H = ∅, with (G4) giving (H1) for the frozen agents and (G3) giving (H1)
   for the pair holders.
2. The whole difficulty sits in (H1)–(H2). The frozen agents and the multi-good holders impose *demands* (goods of
   their danger sets to keep out of X_o). The holders have |N₁| slots. A holder serves itself only when it is exposed
   and no kept-out good serves it, and then it uses its own slot. This is the count `k4/sdc.md` §30 asks for: Lemma
   K's service count (`k4/rulef.md` §2) with frozen agents protected by other agents' slots.
3. *Checks.*
   - **A real test of Lemma 2** (`k4/oc1_hall/lemma2_true_check.py`, `lemma2_true_check.log`). At the picks and at
     every state one improving chain reaches, for every owner satisfying the hypotheses, the script lets H range over
     the sets meeting (H1) only. It computes θ(H) and ν(H) (a maximum matching) and compares "some H has
     |H| + θ − ν ≤ |N₁|" with the raw S\* enumeration `ohlib.shaped_completion`.
     - Result: 248,341 owner tests, 0 mismatches.
     - For the least such H, `ohlib.lemma2_build` runs the (⇐) construction. The unmatched exposed holders do DT's
       moves, which happens in 73,410 cases. The output is always EFX₀ (raw check) and of S\* shape.
   - *An implementation cross-check, not a test of the lemma* (`deficit_check.py`, `deficit_check.log`). The
     *deficit* of o is the least |H| − |N₁| over slot sets H (self-service goods included) for which the needy holders
     can be matched inside H (`ohlib.deficit`). This is the definition of an S\* completion written as a search, so its
     agreement with `ohlib.shaped_completion` (31,459 tests, 0 mismatches) only confirms the two implementations.
     `lemma2_check.py` builds from such full witnesses, so it never runs DT's moves (312,502 constructions, all EFX₀).
     It is kept for its hypotheses test.
   - At the starts with no unfrozen owner (271 screen), the least deficit is 1 on 235, 2 on 35 and 3 on 1.
   - The logs give 1,435 / 138 / 12, and the random profiles 883 / 190 / 9.
   - A deficit of 3 occurs, for example, when n = 3 and two agents are frozen, so that no holder is left.
   - So one chain must sometimes recover three slots. It does so by unfreezing: in red-key-without-t0 (screen), the
     chain 1 → 2 gives agent 2 its top, and agent 2 then stops wanting agent 0's pick.

## 5. One frozen agent (f = 1)

**Setting.** Y = SD(π) has exactly one frozen agent x. Let a = Y_x, L_x = R_x ∖ {a} (at most three goods), W the
wanters of a, and for o ≠ x let D_o = (J ∪ {Y_o}) ∩ R_x, the goods of x that X_o would contain if no junk were kept
out. Facts used throughout:
- (f1) x holds its top a. Every w ∈ W ranks a first and Y_w second. Every other agent i ∉ W ∪ {x} holds its top.
  - A good i prefers to Y_i would be a pick wanted by i, and only a is wanted.
  - By (I2), junk ranks below the pick.
  - A wanter with no pick values only a.
- (f2) Every agent other than x is unfrozen, so every agent other than x and the owner is a holder (N₁ = N ∖ {x, o}).
- (f3) No junk good and no pick other than a is wanted. So (G2) holds, and (G5′) holds for every owner o ≠ x.

**Proposition 3 (T2⁺, K4.OCH.T2).** If v_x(D_o) ≤ p_x for some o ≠ x, then the picks have an S\*
completion with owner o.

*Proof.* Lemma 2 with H = ∅ and Q = {x}.
- (G1): x is a singleton.
- (G2), (G5′): by (f3).
- (H3): B_o is a single good.
- (H1): X_o ∩ R_x ⊆ D_o is worth at most p_x, so x is not threatened.
- (H2): θ(∅) ≤ |N₁|. ∎

When x values no junk at all, Proposition 3 applies to any wanter w (D_w ⊆ {Y_w}, worth less than a), so it contains
DT⁺ for f = 1. Write I(w) = D_w = (J ∪ {Y_w}) ∩ R_x. An *improving set* is H₀ ⊆ I(w) with v_x(H₀) > p_x. The
*swap* (w, H₀) gives a to w and H₀ to x, and makes Y_w ∖ H₀ junk.

**Theorem F1₁ (K4.OCH.F1W1).** Let Y have exactly one frozen agent x, exactly one wanter w, and n ≥ 3. Then the picks
have an S\* completion, or the swap (w, H₀) has one for some improving set H₀ ⊆ I(w).

*Proof.* If Proposition 3 applies, we are done. Otherwise v_x(D_o) > p_x for every o ≠ x, so x has an improving set
inside I(w).

**(B2) Some improving pair H₀ ⊆ I(w).** This is Theorem DT₁ (`k4/sdc.md` §30): after the swap nobody is frozen, and
Lemma GDT applies with any owner o ∉ {x, w}. That completion has the S\* shape.

**(B3) No improving pair.** Then every pair inside I(w) is worth at most p_x, while I(w) is worth more. So
I(w) = L_x = {b, c, d} with v_x(b) + v_x(c) ≤ p_x < v_x(b) + v_x(c) + v_x(d).
- Y_w ∉ L_x. Otherwise pick o ∉ {x, w} (n ≥ 3). Then D_o = L_x ∖ {Y_w}: Y_o ∉ R_x, because R_x = {a} ∪ L_x and
  L_x ⊆ J ∪ {Y_w}. That pair is worth at most p_x, and Proposition 3 would apply.
- So L_x ⊆ J. Call agent i ≠ x *crowded* if the bundle L_x threatens i at p_i: v_i(L_x ∖ h) > p_i for some h ∈ L_x.
  Then L_x ∖ h holds exactly two goods of R_i, since each junk good is worth less than p_i to i by (I2). Call them i's
  *danger pair* in L_x.

*(B3a) No agent is crowded.* Take the swap (w, L_x) with owner w: w holds a, x holds L_x, and Y_w becomes junk. Apply
Lemma 2 with H = ∅ and Q = {x}.
- (G1): the bundle L_x threatens nobody at the base values. Nobody is crowded, and w's value only rose.
- (G2): Y_w is unwanted by (f3), and x now holds L_x, worth more than a > Y_w.
- (G5′): a is wanted by nobody else (one wanter), and x is not in N₁.
- (H3): B_w = {a} is one good.
- (H1): X_w ∩ R_x = {a}, and v_x(a) < v_x(L_x).
- (H2): θ ≤ |N₁|.

*(B3b) Some agent i is crowded,* with danger pair {g, g′} ⊆ L_x, where g is the one i ranks higher. Keep the picks.
Choose an owner o ∉ {x, i} (n ≥ 3; o is unfrozen by (f2)). Apply Lemma 2 with H = {g} and Q = {x}.
- (H1): X_o ∩ R_x ⊆ D_o ∖ {g} = L_x ∖ {g}, a pair worth at most p_x, so x is safe.
- i with g is robust inside R′_i = {Y_i} ∪ (W_o ∩ R_i):
  - Y_i is the top of R′_i: junk by (I2), and Y_o by (f3).
  - |R′_i| ≤ 4, and g is not the lowest good of R′_i, since i ranks g above g′ ∈ R′_i.
  - So {Y_i, g} is robust by DT's (F4). Hence i is not threatened by W_o ∖ {g} at p_i + v_i(g).
- (H2):
  - If i is exposed, ν({g}) = 1 and θ ≤ |N₁|, so 1 + θ − 1 ≤ |N₁|.
  - If not, θ ≤ |N₁| − 1, since i ∈ N₁ is unexposed, and 1 + θ ≤ |N₁|. Lemma 2 then puts g in an unexposed slot.
- The other hypotheses hold as in Proposition 3. ∎

*Remarks.*
1. **The duality in (B3).** The agent that blocks the swap (crowded by x's three goods) is the agent that unblocks
   the picks: its own slot keeps one of x's goods out of the owner's bundle.
2. **n = 2** is excluded: there N₁ = ∅ at the picks, and the only possible owners after the swap are x and w. The data
   have n = 2 starts where only a frozen owner works (lb4-n2m5-upgrade, picks (3, 4): x owns at the picks). For
   TARGET₄ this case is not needed (scope remark).

*Check* (`k4/oc1_hall/f1w1_check.py`, `f1w1_check.log`). The proof's case split runs literally. Each case ends in
Lemma 2's construction (`ohlib.lemma2_build`: matched goods, the rest of H, then DT's moves), and the result is checked
with the raw EFX₀ definition and the S\* shape. Over all 3,329 starts with f = 1, one wanter and n ≥ 3 (every data
set): case A 2,098, B2 1,157, B3a 58, B3b 16, and 0 failures.

**Several wanters** (`k4/oc1_hall/f1_mech.py`, `f1_mech.log`; evidence).
- Mechanisms that cover every f = 1 start with n ≥ 4: Proposition 3, Lemma 2 at the picks with an unfrozen owner, or a
  swap with owner x or an owner outside {x, w}.
- The only f = 1 starts these miss:
  - n = 2: lb4-n2m5-upgrade and its logged copy;
  - n = 3 with two wanters: c4-owner-last-n3m8, c4x-n3m6-ef-bases and their logged copies. There n − 2 = 1 slot, and
    only a frozen owner works: x at the picks, or w after the swap.
- With several wanters and n ≥ 4 (220 starts), the picks have an S\* completion with an unfrozen owner on all but 1,
  and a wanter can own whenever an unfrozen owner can.

In Theorem F1₁'s check, cases A, B2 and B3a use H = ∅, so every exposed holder does DT's moves. The check therefore
exercises Lemma 2's (⇐) construction, not only its count.

## 6. The count in transversal form, and what the chain must do

**Corollary 2.1 (Hall form of (H2), K4.OCH.HALL).** In the setting of Lemma 2, fix H ⊆ J. Call a holder u ∈ N₁
*admissible* for h ∈ H if either
- u is unexposed (not threatened by W_o ∖ H at its base value), or
- u is exposed, values h, and is not threatened by W_o ∖ H at v_u(B_u) + v_u(h).

Then (H2) holds iff H has a system of distinct admissible representatives in N₁. By Hall's theorem, that holds iff
every S ⊆ H has at least |S| holders admissible for some good of S. So Lemma 2 reads:

> **C(B, o):** some H ⊆ J is (i) a *transversal of the demands*: it meets a good of every danger set, inside W_o, of
> every frozen agent and every multi-good holder (H1); and (ii) it has an SDR into the slots of the holders.

*Proof.* Every good of H is adjacent to every unexposed holder. So a full matching of H uses at most ν(H) exposed
holders, and it exists iff |H| − ν(H) ≤ #unexposed = |N₁| − θ(H), which is (H2). ∎

**Lemma 4 (helpers, K4.OCH.HELP).** In the setting of Lemma 2, let H satisfy (H1), and suppose every h ∈ H has a
*helper* i_h ∈ N₁, distinct for distinct h, such that:
- i_h values h, and
- {B_{i_h}, h} is robust inside R′ = B_{i_h} ∪ (W_o ∩ R_{i_h}).

Then C(B, o) holds.

*Proof.* A robust holder is never threatened, so i_h is admissible for h in both cases (exposed or not). Corollary 2.1
applies. ∎

By DT's (F4), {Y_i, h} is robust whenever h is not the lowest good of a four-good R′. So a helper is any holder that
values the kept good and values some other good of W_o below it. Case (B3b) of Theorem F1₁ is Lemma 4 with H = {g}.

**Lemma 2\* (the general exact count; compensation included; K4.OCH.COUNT\*).** Lemma 2 assumed (G5′) and (H3) so that
every exposed holder could serve itself by DT's moves. Drop both. Call an exposed holder *non-movable* if:
- it wants a good of B_o, or
- it has a danger set inside B_o (|B_o ∩ R_u| ≥ 2 and v_u(B_o ∩ R_u) > v_u(B_u)).

Then, under (G1), (G2) only, an S\* completion with owner o exists iff some H with (H1) has an SDR of admissible
holders, as in Corollary 2.1, that contains every non-movable exposed holder. A non-movable exposed holder u must
receive a good h ∈ H ∩ R_u that makes it safe, i.e. that compensates it.

*Proof.* As for Lemma 2. Unmatched exposed holders are movable, so they satisfy (F1) inside R′_u (y_u is the top), and
each of their danger sets meets L, so DT's moves apply to them. A completion matches every exposed holder to its slot
good. ∎

*Check* (`lemma2_true_check.py` with `STAR=1`, `lemma2star_true_check.log`). Only (G1), (G2) are assumed. H ranges over
demand transversals, and the matching is forced to cover the non-movable exposed holders.
- Result: 330,992 owner tests (picks and post-chain states, every owner), 0 mismatches with the raw S\* enumeration.
- The construction (DT's moves used in 76,395 cases) is always EFX₀.
- (G1) fails in 35–46% of the post-chain owner tests: a middle agent's pair contains a pick that someone wants, or the
  owner wants a good of a pair. `lemma2star_check.py` handles those states by checking every agent, owner
  included, against the fixed bundles. That is again a search over full slot sets, so it confirms only the
  implementation (212,695 owner tests, 0 mismatches).

This is the form the post-chain states need. When the chain's first agent k takes the end's pick and owns, the
wanters of that pick are non-movable and must be compensated by their own junk good (adaptive-p1, `k4/sdc.md` §29,
and the dump in `chain_shapes.log`).

**What the chain must do: refuted simplifications** (evidence, all on the hard starts):
1. *One culprit* (LB⁺'s bad case): false for about 30% of the hard starts, and about half at n = 5.
   `attempts/k4-oc1-hall-single-culprit.md`, `culprit.log`.
2. *Canonical chains* (each middle agent wants its predecessor's pick and takes no junk; any improving H₀; owner k or
   end) repair 219 of 234 screen hard starts, 1,452 of 1,470 logs and 255 of 255 random n = 4
   (`k4/oc1_hall/greedy_rules.py`, `greedy_rules.log`). In adaptive-p1, picks (5, 3, 4), the only repairs pass agent
   0's pick to 1, 1's pick to 2 *with junk good 2* (2 prefers 7 + 2 to its pick 8), and give 2's pick 4 plus junk 1
   to agent 0.
   - Taking H₀ as everything k values in J ∪ B_{x_t} does as well as any H₀ on 216 of 217 screen starts with a
     canonical owner-k repair.
   - Taking junk only (never the end's pick) drops to 145.
3. *A rule for k from the order* (`k4/oc1_hall/which_k.py`, `which_k.log`):

   | rule for k | screen | logs |
   |---|---|---|
   | every k ∈ D works | 123 / 234 | 694 / 1,470 |
   | the first agent of D in π | 553 / 773 (start, order) pairs | 3,232 / 4,849 |
   | the last agent of D in π | 578 / 773 | 3,162 / 4,849 |
   | the agent of D with the most wanters | 195 / 234 | 1,142 / 1,470 |

   So k must be chosen by the count (Corollary 2.1), as Lemma K chooses the owner.

**Consequence for a proof.** The chain lemma has to show: when no owner has a transversal with an SDR, some chain from
some dangerous k produces a state where k (or the end) has one. The chain may do any of the following:
- absorb k's demand (k owns its danger set);
- remove several demands at once: chain agents get what they want, and off-chain frozen agents whose wanters
  improved are unfrozen;
- create new demands, which then need helpers:
  - the end's released pick is valued by the end, if it is still frozen;
  - goods of H₀ crowd other agents.

The f = 1 analysis (§5) is the case with one demand. Case (B3)'s duality ("the agent that blocks the swap is the
helper at the picks") is the pattern to generalize.

## 7. Larger n (evidence)

`k4/oc1_hall/big_sstar.py`, logs `big_sstar_*.log`.
- *Method.*
  - S\* completions by SAT: sdclib's EFX₀ encoding, with at most one agent receiving two or more junk goods, and
    non-holders receiving junk only as the owner.
  - Cross-checked against the brute force `ohlib.gdt_shape(..., 'any')`: 8,234 states and 29,897 owner tests on
    special and screen, 0 mismatches.
  - Orders are sampled.
  - For hard starts, chains come from `de_free.iter_chains` (junk sets of at most 4 goods, any length). First the
    script asks for a completion owned by a dangerous agent that gave its pick away in the chain; failing that, any
    owner.
- *Instances.*
  - random strict profiles of the n = 6 cores with one 4-good agent (`results/k4_certs_6_n4_1.json.gz`);
  - random hypergraphs with 3 or 4 goods per agent and m between n + 2 and 2n ("big", balanced types).

| data | instances | distinct starts | hard starts | repaired, a dangerous agent owns | not repaired |
|---|---|---|---|---|---|
| n = 6 cores | 3,000 | 20,950 | 387 | 387 | 0 |
| random n = 6 | 2,000 | 10,503 | 614 | 614 | 0 |
| random n = 7 | 1,000 | 7,503 | 214 | 214 | 0 |
| random n = 8 | 600 | 6,354 | 76 | 76 | 0 |
| random n = 10 | 200 | 2,813 | 9 | 9 | 0 |

The share of hard starts falls with n (1.8% at n = 6 cores, 0.3% at n = 10), as the slot count predicts: more holders
are unexposed. Sampled orders and random profiles are evidence only. Failures elsewhere in this project occurred in 1
of 23,000 profiles.

## 8. Two frozen agents (evidence)

`k4/oc1_hall/f2_study.py`, `f2_study.log`. The hard starts with exactly two frozen agents x, y:
- 93 screen, 524 logs, 388 random n ≤ 3, 49 random n = 4;
- none in the 150 random n = 5 profiles.

| | screen | logs | random n ≤ 3 | random n = 4 |
|---|---|---|---|---|
| hard f = 2 starts | 93 | 524 | 388 | 49 |
| x, y independent / one wants the other's pick | 58 / 35 | 287 / 237 | 202 / 186 | 38 / 11 |
| both dangerous (\|D\| = 2) | 85 | 478 | 358 | 46 |
| some unfrozen owner has a single culprit | 3 | 12 | 0 | 19 |
| some owner-k repair passes through the other frozen agent | 53 | 311 | 262 | 38 |
| some owner-k repair unfreezes the other off the chain | 23 | 261 | 237 | 34 |
| some owner-k repair leaves the other frozen | 54 | 173 | 212 | 33 |
| some canonical owner-k repair | 79 | 507 | 388 | 48 |

- With n = 3 and two frozen agents there is no holder, so the deficit is the whole demand. A single culprit then
  means that one frozen agent has no demand at all, which almost never happens at a hard start. Every repair must
  remove both demands at once.
- The three mechanisms are about equally common. The chain absorbs k's demand (k owns). The other frozen agent's
  demand is then:
  - removed by the chain (it is on the chain and now holds what it wanted), or
  - removed by unfreezing (its wanter is on the chain and improved), or
  - met by the slots, which the chain may have freed (Lemma Ωʳ's f-term).
- So a count for the chain lemma at f = 2 must combine Corollary 2.1 with the unfreezing term of Lemma Ωʳ
  (`k4/sdc.md` §26): u = the number of agents off the chain that were frozen before and are not after.

## 9. Small excess: Proposition 5

**Proposition 5 (K4.OCH.OMEGA).** Let Y = SD(π), o an unfrozen agent, N₁(o) the unfrozen agents other than o, and
ω_o = |J| − |N₁(o)|. If ω_o ≤ 1, the picks have an S\* completion with owner o.

*Proof.* Give every junk good but at most one to distinct agents of N₁(o), one each, and the rest to o. Then
X_o = {Y_o} or {Y_o, g} with g ∈ J.
- A bundle of at most two goods threatens i only if i values one of its goods above t_i ≥ p_i (Lemma 1).
- Y_o is unwanted (o is unfrozen), and junk is unwanted by (I2).
- The same holds for the holders' bundles {Y_j, z}.
- Frozen agents take nothing and are singletons. ∎

This is the S\* form of LB₄ʳ's `EFX.LB4R.output_none_of_omega`. Two consequences:
- **Hard starts are dense.** At a hard start every unfrozen owner has ω_o ≥ 2. With f frozen agents and every agent
  holding a pick, that reads |J| ≥ n − f + 1, i.e. m ≥ 2n − f + 1.
  - In a core, Σ_i |R_i| ≥ 2m − π, with π the number of private goods, and Σ_i |R_i| = 4n − n₃, with n₃ the number of
    3-good agents. So n₃ ≤ 2f − 2 + π at a hard start where every agent picks.
  - In the data, the least ω over unfrozen owners at the hard starts runs from 2 to 8 (`omega_sstar.log`; e.g. screen
    2: 30, 3: 112, 4: 57, 5: 27, 6: 6, 7: 2).
- **The chain must beat a large excess.** Unlike LB⁺ at k = 3, where the bad case has excess one, one chain here
  must overcome ω up to 8. It does so by moving junk into the chain agents' new bases, H₀ and the H_i, and into k's
  owned bundle, which Lemma 2's count then accepts.

*Check* (`k4/oc1_hall/omega_sstar.py`, `omega_sstar.log`). On every distinct start of every data set, every
unfrozen owner with ω_o ≤ 1 passes the raw S\* enumeration: 14,756 owner tests, 0 failures.

## 10. Adversarial climbs against Finding B (evidence)

`k4/oc1_hall/climb_b.py`, logs `climb_b_n3_s11.log`, `climb_b_n3_s12.log`, `climb_b_n4_s13.log`, `climb_b_n4_s14.log`.
- *Objective.* Over every order whose picks have no S\* completion: the least number of pairs (chain description,
  owner) in which the chain starts at a dangerous frozen agent k, and k or the chain end owns afterwards in S\* shape.
  Ties are broken by the number of hard starts, more being better. 0 would be a counterexample.
- *Climb.* Seeds are logged profiles with a hard start. Mutations are those of `k4/sdc/sdc_climb.py`.
- *Runs:* 2 × 25 rounds of 400 steps at n = 3 and 2 × 15 rounds of 250 steps at n = 4.

| best objective | (1, ·) | (2, ·) | (10, ·) |
|---|---|---|---|
| rounds | 77 | 2 | 1 |

- No round reached 0.
- 77 of the 80 reached a profile with a hard start that has *exactly one* repairing pair (chain from D, owner k or
  end). So the statement is tight but survived.
- As everywhere in this note, this is evidence only.

## 11. Several wanters: where the one-wanter proof stops (conjecture)

Setting of §5 with |W| ≥ 2. For an owner o ≠ x, let τ(o) be the fewest of x's junk goods that must be kept out of
W_o = {Y_o} ∪ J for x to be safe.

**Fact (written proof).** If n ≥ 3, then τ(o) ≤ 1 for some o unless L_x ⊆ J, |L_x| = 3, and every pair of L_x is
worth more than a to x.

*Proof.* Let J_x = L_x ∩ J.
- If |J_x| ≤ 1, each danger set inside D_o has at most two goods, one of them junk, so one kept good suffices.
- If |J_x| = 2, choose o with Y_o ∉ R_x. Such an o exists: L_x has at most one pick, so at most one agent's pick is
  valued by x, and n − 1 ≥ 2. Then D_o = J_x, and one good of the pair suffices.
- If |J_x| = 3, then L_x = J_x and D_o = L_x for every o. Two kept goods are needed only if every pair is a danger
  set. ∎

**Conjecture F1W.** If n ≥ 4 and τ(o) ≤ 1 for some unfrozen o ≠ x, the picks have an S\* completion.
- τ(o) = 0 is Proposition 3.
- For τ(o) = 1, with g the kept good, Corollary 2.1 asks for one admissible holder for g among the n − 2 ≥ 2
  holders. A counterexample would need, for every such owner and every such g:
  - every holder exposed by its own junk, and
  - no holder valuing g except as the lowest good of its R′.

  The proof of Theorem F1₁ never meets this situation, because with one wanter the swap removes every demand.
- When τ(o) = 2 for every o, the picks can fail. On red-b1-blocked-improvement (n = 4), x's three junk goods are
  pairwise dangerous and only one admissible holder exists. The swap (any pair of L_x, owner x) repairs.

*Evidence* (`k4/oc1_hall/f1w_tau.py`, `f1w_tau.log`, SAT S\* test, sampled orders; and the n = 4, 5 data of §5):

| data | starts with f = 1, several wanters | τ_min = 0 | τ_min = 1 (picks complete) | τ_min = 2 (picks complete) |
|---|---|---|---|---|
| n = 4, 5 (screen, suite, logs, random) | 228 | 168 | 53 (53) | 7 (5) |
| n = 6 cores, one 4-good agent | 312 | 264 | 48 (48) | 0 |
| n = 5 pure cores | 162 | 97 | 60 (60) | 5 (5) |
| random n = 6 | 399 | 293 | 104 (104) | 2 (2) |
| random n = 8 | 158 | 102 | 54 (54) | 2 (2) |

The two τ = 2 failures at n = 4 are red-b1-blocked-improvement, counted once in screen and once in suite.

## 12. The matroid-partition form (coordinator's proposal), tested

**Proposal** (coordinator, from the literature survey; `research_notes/.../cross_field_techniques.md` §Q5 on branch
`claude/kind-lamport-y8fdme`, not read here). Fix the start and an unfrozen owner o.
- The holders' slots form a transversal matroid M_T on J.
- Each frozen agent i gives a family I_i of sets of its junk goods D_i = J ∩ R_i that the absorber may hold. I_i is a
  matroid except in one k = 4 configuration: the danger sets inside D_i are exactly {xy, xz}.
- With the D_i pairwise disjoint and every I_i a matroid, Edmonds' matroid partition theorem gives: a completion
  exists iff every S ⊆ J has Σ_i (|S ∩ D_i| − r_i(S ∩ D_i)) ≤ r_T(S) (**RADO**).

**Implementation** (`k4/oc1_hall/matroid_check.py`, `matroid_check.log`).
- In the graph of M_T, h ~ u when holder u is unexposed at W_o, or values h and {Y_u, h} is robust. That is the
  H-independent part of Corollary 2.1's admissibility.
- I_i = {A ⊆ D_i : v_i(P_i ∪ A) ≤ p_i}, with P_i = {Y_o} ∩ R_i. This is conservative: the strictness clause is ignored.
- MODEL is the brute-force condition: some H independent in M_T, with D_i ∖ H ∈ I_i for all i.
- Two variants: MODEL_S computes the frozen agents' threat exactly; MODEL_HS also recomputes admissibility for each H.
  MODEL_HS is Lemma 2's count.

**Results** (20,648 owner tests: special, screen, suite, logs, random n ≤ 5; every order; unfrozen owners). Totals over
the data sets in `matroid_check.log`:

| class of owner test | tests | RADO ≠ MODEL | MODEL ≠ EXACT |
|---|---|---|---|
| D_i pairwise disjoint, every I_i a matroid | 16,532 | **0** | 175 |
| D_i overlapping | 3,929 | 347 | 100 |
| disjoint, but some I_i not a matroid ({xy, xz}) | 187 | 8 | 3 |

- MODEL ⇒ EXACT always (no `BUG` line), so the matroid form is a valid sufficient condition.
- RADO = MODEL on every disjoint all-matroid test: Edmonds' theorem as predicted.
- Even there MODEL is not exact. Of the 175 misses:
  - 150 come from the **strictness clause**: when the absorber's bundle lies inside R_i, its least good is discounted
    (MODEL_S leaves 25);
  - the rest come from **exposure that depends on H**: kept-out goods unexpose holders, which then become admissible.
  - With both, MODEL_HS = EXACT on all 20,648 tests. This is Lemma 2, whose admissibility is not a fixed matroid.
- Non-matroid {xy, xz} agents occur in 331 owner tests; with disjoint D_i, RADO then differs from MODEL in 8.
- Overlapping D_i occur in 19% of owner tests. RADO differs from MODEL in 347 of them and from EXACT in 447, once in
  the permissive direction.
- At the level of starts:
  - 230 starts have an unfrozen-owner S\* completion that RADO misses;
  - 627 complete only with a frozen slot or a frozen owner (SAT yes), which the proposal's model excludes by design.

**Assessment.** The k = 4 difficulty is not localized to "overlapping D_i" and "{xy, xz} agents". The fixed-matroid model
loses exactness also through the strictness clause and through the H-dependence of exposure. Both are local, and both
only *help* completions. The exact condition is Lemma 2 / Corollary 2.1: for some H, a transversal condition whose
admissibility depends on H.

Uses of the matroid form:
- *A polynomial sufficient test* when the D_i are disjoint matroids (matroid partition), for runs at large n.
- *A clean sub-statement for a proof*: if RADO holds for some owner, the picks complete. Then the chain lemma only
  has to handle starts where every owner has a Rado violator S. On the data these are 230 + 627 + 2,015 starts.

## 13. Frozen slots are not needed (REFUTED at n = 4, see below); the configurations beyond canonical chains

**Refuted** (`attempts/k4-oc1-hall-frozen-slots.md`, `k4/oc1_hall/frozen_slot_cex.py`). At an n = 4 start found by
`proof/k4-matching`, five one-move states have a one-absorber completion and none has an S\* completion: the
completing allocations give a frozen agent a compensated junk good, as in Lemma 1's (S1). The evidence below covers
only this note's n ≤ 5 data. Two S\*-shaped moves still repair (matching session). The exact count that includes
compensated frozen slots is Lemma M^c (`proof/k4-oc1max-multi`, §23.2 leaf 1).

These are the coordinator's steps 1 and 3 (`k4/oc1_hall/frozen_slots.py`, `frozen_slots.log`;
`k4/oc1_hall/no_canonical_list.py`, `no_canonical_list.log`, `no_canonical.json`).

**Frozen slots.** Lemma 2\* already allows a frozen owner. What S\* excludes is a frozen agent taking a (compensated)
junk good.
- Starts whose picks have a one-absorber completion (SAT) but no S\* completion: 368 (special 1, screen 40, suite 37,
  logs 106, random 143 + 40 + 1).
- On every one of them, one chain restores S\*, and a chain of Finding B's form does: x₀ dangerous, owner k or end.

So extending the invariant to compensated frozen slots is not needed for OC₁. These starts are simply hard starts for
S\*, and the chain lemma covers them. Keeping S\* keeps the invariant exactly Lemma 2\*.

**The configurations beyond canonical chains (Finding C).** Over every data set (n ≤ 5, every order), deduplicated:
- every hard start has a canonical repair from a dangerous agent with owner k or end (`greedy_rules.py`: middle
  agents want their predecessor's pick and take no junk; any improving H₀), except **20 configurations**;
- by size: 9 with n = 3, 9 with n = 4, 2 with n = 5;
- they are all known adversarial instances: T3, Q2, adaptive-p1/p3, nsw-strict-n4m8/m9, lb4-owner-needs-from-base,
  c4one-one-rotation-m8/m9, and others;
- each has a repair from D with owner x₀ or end and **exactly one non-canonical step**:
  - in 17, one middle agent takes its predecessor's good *together with* junk, without wanting the good alone;
  - in 3, a t = 0 repair also exists: k keeps its pick, adds junk and owns.
- The smallest is T3: n = 3, m = 6, picks (0, 4, 1), frozen {0, 1}, both dangerous. Every repair passes through both
  frozen agents with a junk-assisted middle step.

So a proof of the chain lemma can restrict to canonical chains from D, plus one junk-assisted middle step. The
canonical part is what Theorem F1₁ handles at f = 1.

## 14. Agreement with the TTC session: Conjecture OC₁-ED\*

The TTC session (`claude/k4-ttc`, `k4/ttc.md` §8–§10) states **OC₁-ED**:
- the absorber is an endpoint of the chain, x₀ or the head x_t;
- x₀ is dangerous;
- middle agents take exactly their predecessor's pick, and want it;
- only the head may add junk.

That statement uses one-absorber completions. Finding C says: canonical chains from D, plus at most one junk-assisted
middle step. `k4/oc1_hall/ed_check.py` (`ed_check.log`, `ed_check_list.log`) compares the two on every hard start:

| hard starts (n ≤ 5, every order) | ED chain, S\* completion owned by x₀ or x_t | ED chain, one-absorber completion with absorber x₀ or x_t | head takes junk needed (no fully canonical repair) |
|---|---|---|---|
| one-absorber-hard: 2,308 (16 special, 194 screen, 196 suite, 1,364 logs, 538 random) | **2,308** | 2,308 | 2,308 − 2,266 = 42 |
| S\*-hard but one-absorber-complete at the picks: 368 | 362 | 362 | |

- *The two statements agree.* On every hard start in the one-absorber sense, an ED chain repairs, even with the
  stricter S\* completion. Finding C's junk-assisted step sits at the head of the chain in 18 of the 20 configurations
  of `no_canonical.json`.
- The other 2 are both orders of lb4-owner-needs-from-base-n4m8, picks (4, 6, 7, 5) and (6, 5, 4, 7), each counted in
  screen, suite and logs. Their picks complete with a compensated frozen slot, so they are not hard for OC₁. In S\*
  they need junk at a non-head middle agent, or an owner off the chain.

**Agreed statement (Conjecture OC₁-ED\*, K4.OCH.ED).** For every serial-dictatorship order:
- the picks have a one-absorber completion; or
- some ED chain leaves an S\* completion owned by x₀ or x_t. Here x₀ is dangerous, x₀ takes H₀ ⊆ J ∪ B_{x_t},
  every middle agent takes exactly its predecessor's pick (which it wants), and the head may add junk.

Evidence: all 2,308 one-absorber-hard starts with n ≤ 5. The TTC session adds 264 at k = 3, 103 at n = 6–9 and two
OC₁-H instances at n = 6, m = 10 (not re-run here). OC₁-ED\* implies OC₁, hence TARGET₄. Its second alternative has
Lemma 2\* as its exact invariant.

## 15. One dangerous agent: a fixed rule (proof plan, step 1)

`k4/oc1_hall/d1_rules.py`, `d1_rules.log`, `d1_swapmin_fails.json`. The one-absorber-hard starts with exactly one
dangerous agent k:
- 197 in all: 5 special, 14 screen, 14 suite, 112 logs, 41 random n ≤ 3, 11 random n = 4, 0 random n = 5;
- by (|F|, |W_k|): (1, 1) 36, (1, 2) 9, (2, 1) 67, (2, 2) 22, (3, 1) 32, (3, 2) 11, (3, 3) 2, (4, 1) 16, (4, 2) 2.

| rule (the ED chain starts at k; owner k unless stated) | starts repaired (of 197) |
|---|---|
| SWAP-ALL: t = 1, k takes everything it values in J ∪ {Y_w} | 171 |
| SWAP-MIN: t = 1, an inclusion-minimal improving H₀ | 177 |
| ED-ALL: any ED chain, k takes everything it values in J ∪ B_{x_t} | 195 |
| **ED-MIN: any ED chain, an inclusion-minimal improving H₀** | **197** |
| ED-ANY (Conjecture OC₁-ED\* (b): any H₀, owner k or x_t) | 197 |

- **Finding D1.** With one dangerous agent k, OC₁-ED\* (b) holds in the narrower form ED-MIN. The owner is k itself,
  and H₀ is inclusion-minimal among the improving sets inside J ∪ B_{x_t}. So the step-1 target is: *if D = {k} and
  the picks have no one-absorber completion, then some ED chain from k with a minimal improving H₀ has an S\*
  completion owned by k.*
- *Where the shortest rule fails.* With f = 1 (45 starts) the swap with a minimal H₀ always works. This is Finding F1,
  proved for one wanter in Theorem F1₁. With f ≥ 2 the swap fails on 19 distinct configurations (n = 3–5; smallest
  log584, n = 3, m = 5), all repaired by a longer ED chain. They are listed with their orders in
  `d1_swapmin_fails.json`. This is the list a proof of step 1 must justify: a passing chain is needed when a second,
  non-dangerous frozen agent sits between k and an unwanted end.
- ED-ALL fails only on r1179 (= log558; f = 1, one wanter). There the improving set of three goods crowds another agent,
  and a minimal pair works: case (B2) of Theorem F1₁.

*Why minimal H₀ and owner k fit Lemma 2\*.*
- With k as owner, k's own demand disappears.
- A minimal H₀ crowds as few agents as possible (fewest goods inside X_k).
- With |D| = 1, the other frozen agents value no junk at the picks. Their demands after the chain can come only from
  the released end pick and from H₀.
- By the k ≤ 4 count, each such agent has at most one good of its own left in the pool. That is the lever named in the
  coordinator's note, and in the proof of Theorem F1₁ it appears as "x's leftover lower good is a single good".

## 16. OC₁ is false at n = 6 (TTC session), checked here; what survives

**The counterexample** (TTC session, `claude/k4-ttc`, commit 5e99d73, `attempts/k4-ttc-oc1-counterexample.md`,
`results/k4_ttc/oc1_counterexamples.json`, 84 instances).
- Instance A: sets [[0,2,3,1],[1,4,5,9],[1,2,0,8],[1,6,7,8],[3,6,9],[1,3,6,9]], values
  [[2,7,8,3],[3,6,4,9],[12,2,4,8],[12,6,3,4],[7,2,10],[7,8,4,1]]; order 0, …, 5; picks (3, 9, 1, 6, none, none).
- Agents 4 and 5 hold no pick and want every pick, so agents 0–3 are frozen. Their junk danger sets are {0, 2}, {4, 5},
  {7, 8} (agent 2: {0, 2, 8}), pairwise disjoint.
- A single absorber cannot avoid all of them with only one free slot. The junk needs two absorbers, which the free
  completion finds (agents 4 and 5).

**Independent check** (`k4/oc1_hall/verify_ttc_cex.py`, `verify_ttc_cex.log`; this workstream's raw brute force
`ohlib.absorb_brute`, SAT `extends_A`, `de_free` chains and rings):
- picks: no one-absorber completion (SAT and brute force agree);
- every state one chain or ring reaches (92): none has one.
- OC₁ᵖ, i.e. agents without a pick unrestricted, holds at the picks: allocation ({3}, {9}, {1}, {6}, {2, 4, 7},
  {0, 5, 8}), raw EFX₀.

**Are they cores?** `k4/oc1_hall/core_filter.py` peels by R1 and R2 (`core_filter_ttc.log`).
- 83 of the 84 are not cores: agent 4 of A is top-heavy (10 ≥ 7 + 2). After peeling, 71 leave fewer than two agents.
  The other 12 leave cores with n = 4 or 5, which satisfy OC₁ from every order.
- **Instance 36 is a connected core:** sets [[0,2,3,1],[6,4,5,9],[1,2,3,9],[1,6,7,8],[3,6,9],[1,3,6,9]], values
  [[3,7,8,6],[2,9,6,14],[14,2,8,10],[8,7,6,3],[14,4,12],[10,15,4,2]].
  - OC₁ fails for 24 of its 720 orders, all with picks (3, 9, 1, 6, none, none).
  - Both strict perturbations of agent 2's tie (v(2) + v(3) = v(9)) fail on the same 24 orders.
  - So a **strict connected k = 4 core with n = 6** violates OC₁, and hence OC₁-ED\* and Finding S\*. The TTC session's
    `is_core4` (`k4/c4_verify_H/hcore.py`, the ledger's IsCore4 with connectivity and strictness) accepts both
    perturbations: no failures. It rejects instance 36 itself only for the tie.
  - In it, agents 1 and 3 each have **two private goods** ({4, 5} and {7, 8}, worth less than the rest, so R2 does not
    peel them).

**What this means.**
- OC₁ "for every order" is false, even on strict cores. This workstream's random runs at n = 6–10 (§7) never produced
  the configuration: two pickless agents together with three disjoint danger pairs.
- *For TARGET₄*, a minimal counterexample is a strict connected core with n ≥ 6 (scope remark) and, by K4.MC2
  (CERTIFIED), has no agent with two private goods. So OC₁ restricted to that class is not refuted. Instance 36 lies
  outside it. Whether OC₁ (or OC₁-ED\*) holds on that class is open, and is the test to run next.
- *Repair OC₁ᵖ* (TTC session): agents without a pick take any number of junk goods and do not count as owners. All 84
  instances satisfy it at the picks.

**Does Lemma 2\* extend to pickless agents of unlimited capacity?** Claim, proof sketch only, not checked by
computation. Replace the single bundle X_o by the absorbing bundles: X_o, and one bundle Z_u for each agent u without
a pick.
- An agent u without a pick values no junk, so no junk bundle threatens u.
- u is threatened by any bundle of two or more goods that contains a good u values. Such goods are picks, so their
  holders are frozen (they take nothing), and the owner must not hold a good some pickless agent values.
- Demands become "no danger set of a frozen or multi-good agent lies inside one absorbing bundle". This is a partition
  condition, not one kept-out set. Exposure becomes "threatened by some absorbing bundle".
- DT's moves work bundle by bundle: a threatened movable holder takes a good of the danger set inside the bundle that
  threatens it.
- So Lemma 2\*'s proof carries over. Its count becomes: some partition of J into the absorbing bundles and a slot set
  H, in which every frozen or multi-good agent is safe against every absorbing bundle, and H has an SDR as in
  Corollary 2.1.
- With pickless agents present this is a multi-bin version of the transversal condition, close to the coordinator's
  matroid-partition form (§12).

**A second core counterexample** (TTC session, commit 14955fd on `claude/k4-ttc`,
`results/k4_ttc/oc1_core_candidate.json`; checked here).
- The instance: sets [[0,1,3,4],[1,2,5,6],[2,0,7,8],[0,1,2],[0,1,2]], values [[10,3,6,5],[10,3,6,5],[10,3,6,5],[4,3,2],
  [2,4,3]], n = 5, m = 9.
- `is_core4` reports no failures, so this is a strict connected core.
- With order 0, …, 4, the picks are (0, 1, 2, none, none). They have no one-absorber completion (SAT and
  `ohlib.absorb_brute`), and none of the 56 states one chain or ring reaches has one. OC₁ fails for 12 of the 120
  orders.
- Agents 0, 1 and 2 each have **two private goods** ({3, 4}, {5, 6}, {7, 8}). These are the three disjoint danger
  pairs, and n = 5 is certified for TARGET₄ anyway.

**The pattern.** Both core counterexamples build the disjoint junk danger pairs of frozen agents from agents with
two private goods. In the K4.MC2 class every agent has at most one private good. A junk danger pair of a frozen agent
then contains a good that another agent also values, so the pairs can overlap or be broken by other agents' slots,
and the pigeonhole need not apply. Whether OC₁-ED\* holds on that class is the open question. A direct test is OC₁ on
`k4_certs_5_n4_3`, `_n4_4` and `_pure` (n = 5, three or more 4-good agents) filtered to cores with no agent holding two
private goods.

## 17. The K4.MC2 class: no failure, and why the pickless pigeonhole breaks there (evidence)

**Random test** (`k4/oc1_hall/mc2_oc1.py`, `mc2_oc1_n5.log`).
- Of the 24,381 connected n = 5 cores with three, four or five 4-good agents (`k4_certs_5_n4_3`, `_n4_4`, `_pure`),
  12,727 have no agent with two private goods.
- 300 random strict profiles of those, every order, 1,119 distinct starts:
  - OC₁ holds on all, 1,043 at the picks and 76 after one chain or ring;
  - no start has two or more agents without a pick.

**The hand-made analogue** (`mc2_triangle.log`). Take the TTC n = 5 core and replace the three private danger pairs by
a triangle of shared junk goods, with one private good per agent:
- sets [[0,3,4,6],[1,4,5,7],[2,5,3,8],[0,1,2],[0,1,2]], values [[10,6,5,3],[10,6,5,3],[10,6,5,3],[4,3,2],[2,4,3]];
- `is_core4` reports no failures: a strict connected core in the K4.MC2 class.

Here is what happens.
- *At the picks.* With order 0, …, 4 the picks are (0, 1, 2, none, none), two agents are pickless, and there is no
  one-absorber completion, exactly as in the TTC core.
- *One chain repairs it.* For example, agent 1 takes its danger pair {4, 5}, and pickless agent 3 takes agent 1's pick
  1. Good 4 is also in agent 0's danger pair {3, 4}, and good 5 in agent 2's pair {5, 3}. So the move breaks all
  three demands at once, and a single absorber suffices.
- *Every order.* OC₁ holds from all 120 orders: 108 at the picks, 12 after one move.

**The structural reason.** This is a proof idea, not a lemma yet.
- The pigeonhole of §16 needs several frozen agents whose junk danger sets are pairwise disjoint and unreachable by
  any single improving move.
- A frozen agent's danger pair lies in its junk. In the K4.MC2 class at most one of its goods is private, so every
  junk danger pair contains a good shared with another agent.
- Agents without a pick value only picks, so that other agent holds a pick.
- When k takes its danger pair H₀ in an ED chain, the shared goods of H₀ leave the pool, and so break every danger
  set they belong to.
- The two-private-goods construction is exactly what prevents this: the danger pairs there are private, so absorbing
  one leaves the others intact.

A lemma would say: in the K4.MC2 class, after an ED chain from k with H₀ a danger set of k, every frozen agent whose
danger set met H₀ has at most one pool good left. That is the k ≤ 4 lever of §15 again, and the next item to prove
along with Finding D1.

## 18. OC₁ and OC fail from some orders inside the K4.MC2 class; the count explains why

**The instance** (TTC session, `results/k4_ttc/oc1_mc2_counterexample.json` on `claude/k4-ttc`; checked here, log
`verify_ttc_mc2_cex.log`).
- sets [[0,3,6,8],[1,4,7,6],[2,5,8,7],[0,1,2],[0,1,2]], values [[10,6,5,7],[10,6,5,7],[10,6,5,7],[4,3,2],[2,4,3]],
  n = 5, m = 9.
- `is_core4` reports no failures, and each agent has at most one private good: a strict connected core in the K4.MC2
  class.
- Agent i (i = 0, 1, 2) values its pick y_i at 10, a private good a_i at 6, a shared good b_i at 5, and b_{i−1} at 7.
  Agents 3 and 4 value only y₀, y₁, y₂.

**What fails.**
- With order 0, …, 4, the picks are (0, 1, 2, none, none). There is no one-absorber completion (SAT and raw brute
  force) and **no free completion**.
- None of the 232 improving moves (additions, chains, rings, |H| ≤ 4) gives either. A free completion needs two moves.
- Over all 120 plain orders, 12 fail OC₁, and the same 12 fail OC.
- **Every R1-priority order works**: 108 at the picks, 12 after one move.

**Why, in Lemma 2\*'s terms (multi-bin form, §16).**
- Each frozen agent i holds its top y_i = 10. Its three junk goods {a_i, b_i, b_{i−1}} = 6, 5, 7 are a *danger
  triangle*: every pair is worth more than 10. So in any absorbing bundle of three or more goods, at most one of them
  may sit.
- The only agents that can receive junk are the two pickless agents 3 and 4. The pick holders are all frozen (3 and 4
  want every pick), and a frozen agent can take junk only when its wanters are compensated. Pickless agents value no
  junk, so they cannot be.
- So the six junk goods go into two bins whose sizes sum to 6. The triangles are {3, 6, 8}, {4, 7, 6} and
  {5, 8, 7}; each of the six goods is in one or two triangles.
  - If one bin has at most two goods, the other holds at least four. Since the triangles cover all six goods, some
    triangle has two goods in the big bin, which threatens that agent. (A bin of exactly two goods is harmless: the
    strictness clause applies.)
  - If both bins have three goods, each triangle has three goods split over two bins, so by pigeonhole some bin holds
    two goods of some agent's triangle and threatens it.
- One chain cannot fix this. The improving moves give a pick to a pickless agent, which then becomes frozen (the
  other pickless agent wants it), and they remove at most one triangle's worth of goods. With two bins, the remaining
  two triangles still collide in the same way.

**What survives.**
- The statements about given states are unaffected: Lemmas 1, 2, 2\*, 4, Corollary 2.1, Propositions 3 and 5,
  Theorem F1₁ (one frozen agent), and the multi-bin count.
- All "for every order" conjectures (OC, OC₁, OC₁-ED\*, Finding S\*) are refuted, even on strict cores of the K4.MC2
  class, already at n = 5. TARGET₄ is certified there.
- The R1-priority forms survive on these instances, together with MD (value domination) and SD-C (some order). The
  pickless agents here come from a plain order that serves the frozen agents first. R1 priority processes them earlier.

A Theorem A₄ for R1-priority orders would have to show that this "two pickless bins against three triangles" pattern
cannot occur.

**OC₁-ED\* for R1-priority orders, on this workstream's data** (`ed_check.py` with `R1=1`, `ed_check_r1.log`).
- Picks are now those of R1-priority serial dictatorship (`k4/sdc/sdc_orders.sd(..., True)`), every order.
- On every one-absorber-hard start an ED chain leaves an S\* completion owned by x₀ or x_t: special 15, screen 144,
  suite 143, logs 1,157, random 240 + 149 + 7. That is **1,855 of 1,855**.
- The only S\*-hard starts without an ED repair are again lb4-owner-needs-from-base-n4m8. They complete at the picks
  with a compensated frozen slot.
- The TTC session's K4.MC2-class core satisfies OC₁ from all 120 R1-priority orders.

So the R1-priority form of OC₁-ED\* survives everything known.

## 19. Maximum-matching orders (coordinator's proposal): Lemma MAX

The coordinator observed (`k4/sdc/oc1_max_orders.py` on `claude/kind-lamport-y8fdme`) that every known OC₁ failure
comes from an order whose picks do not form a maximum matching of the agent–good relevance graph. The proposal is
**OC₁^max / OC₁-ED\*^max**: the same statements for every serial-dictatorship order whose picks form a maximum
matching. By the Pareto argument in the coordinator's `k4/attack_log.md`, such orders exist, so OC₁^max on cores
implies TARGET₄.

**Lemma MAX (K4.OCH.MAX).** Let the picks Y form a maximum matching, and let S be the set of agents reachable from a
pickless agent by an alternating path. Such a path runs u, g₁, j₁, g₂, j₂, … where u has no pick, g_l ∈ R_{j_{l−1}}
(with j₀ = u) is a pick, and j_l is its holder. Then:
1. No agent of S values a junk good.
2. Hence no dangerous frozen agent lies in S. So every agent on a want-chain above a dangerous agent x (its wanters,
   their wanters, …) holds a pick, and every such chain ends at an unfrozen pick holder.

*Proof.*
1. If j ∈ S valued a junk good g′, the alternating path from u to j followed by the edge j–g′ would be an augmenting
   path: u is unmatched, and g′ is unpicked, hence unmatched. Shifting along it gives u the good g₁, each j_l the good
   g_{l+1}, and j the good g′. That is a larger matching, a contradiction.
2. If a pickless agent u wanted the pick of some agent x, or of an agent above x (so that x is reached by the wanting
   arrows u → … → x), then x ∈ S, since wanting a pick means valuing it. By (1), x values no junk, so x is not
   dangerous.

   Hence for a dangerous x, no agent on any want-chain above x is pickless. Want-chains are finite (wanting points to
   earlier picks), so each ends at an agent whose pick nobody wants. That agent holds a pick, because a pickless agent
   would have been excluded. ∎

**Consequence.** The obstruction of §16 and §18 needs two ingredients:
- dangerous frozen agents (with junk danger sets) whose wanters are pickless;
- pickless agents as the only junk receivers.

At a maximum-matching start the first is impossible: frozen agents wanted by pickless agents value no junk at all.
Their goods are all picks, so pickless agents add no demand, and they freeze only non-dangerous agents. The dangerous
agents and their want-chains live entirely among pick holders, which is the setting of §5–§15.

Lemma MAX does not show that a maximum-matching start has no hard configuration. It removes the pickless pigeonhole.

**Checks** (`k4/oc1_hall/max_matching.py`, `max_matching.log`).
- The K4.MC2 core of §18: 50 of its 120 orders give maximum-matching picks. Lemma MAX's conclusion holds and OC₁ holds
  on all 50. The 12 failing orders all have non-maximum picks.
- special: 162 maximum-matching orders, screen: 3,832. Lemma MAX's conclusion holds on all of them, and so does OC₁.
- Since every check of this note covered *every* order, OC₁^max and OC₁-ED\*^max inherit all the n ≤ 5 evidence: §14's
  2,308 one-absorber-hard starts all have an ED repair, and those among them with maximum-matching picks are a subset.

**Proposed statement for the Finding D1 proof:** restrict to maximum-matching starts. Lemma MAX then guarantees that
k's want-chains consist of pick holders and end at an unfrozen pick holder: exactly the ED chain shape.

**OC₁-ED\*^max on this note's data, and R1 priority versus maximum matchings**
(`ed_check.py` with `MAX=1`, `ed_check_max.log`; `k4/oc1_hall/r1_vs_max.py`, `r1_vs_max.log`).
- (i) On every one-absorber-hard start whose picks form a maximum matching, an ED chain leaves an S\* completion owned
  by x₀ or x_t: special 15, screen 182, suite 183, logs 1,200, random 293 + 182 + 16. That is **2,071 of 2,071**. The only
  S\*-hard exception is again lb4-owner-needs-from-base, which is not one-absorber-hard.
- (ii) The two order classes are **incomparable**. Over 6,617 instances:
  - 384 of the 13,564 R1-priority pick vectors (in 229 instances) are not maximum matchings;
  - 803 of the 13,983 maximum-matching pick vectors are produced by no R1-priority order.
  - Every instance of this data has ν = n, so "maximum matching" means "every agent gets a pick". There are no pickless
    agents, and Lemma MAX is vacuous there.
- (iii) On the data neither form fails anywhere, so neither is weaker on the data. OC₁-ED\*^max is taken as central
  because its class always exists, Lemma MAX explains the known counterexamples, and on the 39 core counterexamples
  its starts complete at the picks.

## 20. The coordinator's receiver count for OC₁^max with ν = n: the inequality fails on data

**The sketch** (coordinator). Consider a maximum-matching start with ν = n, t frozen agents with junk danger
*triangles*, and r receivers (unfrozen pick holders).
- A failure needs about r ≤ 2t at the picks, and r < 2t − 1 after one chain.
- A slot count at k = 4 (shared triangle goods carried by receivers; at least two wanters per frozen pick; a wanter
  keeps at most one triangle slot) would force r ≥ 2t, leaving no room.

**Test** (`k4/oc1_hall/receivers_count.py`, `receivers_count.log`). At all 2,071 one-absorber-hard maximum-matching
starts, compute t₂ (frozen agents with a junk danger triangle), t₁ (other dangerous agents) and r.

| | starts |
|---|---|
| t₂ ≥ 1 | 82 |
| **r < 2t₂** | **26** |

The 26 have (t₂, t₁, r) = (1, 0, 1), (1, 1, 1), (2, 0, 2) or (2, 0, 3).
- Smallest: hall-local3, n = 3. Sets [[0,1,2,3],[2,4,5,6],[3,4,5,6]], values [[3,2,10,6],[8,2,3,4],[7,3,5,6]], order
  (1, 2, 0), picks (0, 2, 3), frozen {1, 2}, t₂ = 1, r = 1. Also ls-exchange-no-keep-n3m6.
- Every one of the 26 is repaired by an ED chain (§19).

So the inequality r ≥ 2t that the slot count would force is false at k = 4. Its premises fail in general: triangle
goods can be shared with frozen agents or with the frozen agent's wanters, and frozen picks can have a single
wanter. The regime r < 2t occurs, and one chain still repairs it. A counting proof of OC₁^max must credit what the
chain itself absorbs: the triangle pair H₀ goes to x₀, which owns. Counting receivers alone is not enough.

## 21. One dangerous agent: Lemma D1-red (proved) and the two open sub-lemmas

This answers the coordinator's request to write Finding D1 (§15: |D| = 1, ED-MIN, owner k) as a proof. The proved part
is a reduction, Lemma D1-red. What it leaves open is stated as two precise sub-lemmas, each with its smallest test
instance. Scripts: `k4/oc1_hall/d1_obstacles.py` (`d1_obstacles.log`) and `k4/oc1_hall/d1_subcases.py`
(`d1_subcases.log`). Both run on every data set (n ≤ 5, every order), at the 197 one-absorber-hard starts with
D = {k} of §15.

**Setting.** Y = SD(π) has no one-absorber completion, hence no S\* completion (an S\* completion is a one-absorber
completion), and D = {k}.
- A *canonical chain* from k is P = (k = x₀, x₁, …, x_t), t ≥ 1, in which each x_i (i ≥ 1) wants Y_{x_{i−1}}, and
  the head x_t is unfrozen at the picks.
- Applying P:
  - each x_i (i ≥ 1) gives up B_{x_i} and takes Y_{x_{i−1}} alone;
  - k takes a set H₀ from the *pool* Π = J ∪ B_{x_t}, with v_k(H₀) > p_k (H₀ is *improving*);
  - B′ denotes the state reached, J′ = Π ∖ H₀ its junk, and a = Y_{x_{t−1}} the head's new good.
- The owner is k. So W_k = B′_k ∪ J′ = Π, whatever H₀ is.
- The two *obstacles* at B′:
  - **HEAD:** x_t is frozen at B′, and threatened by Π at v_{x_t}(a);
  - **CROWD:** some holder u ≠ k at B′ (unfrozen, at most one good) has |H₀ ∩ R_u| ≥ 2 and
    v_u(H₀ ∩ R_u) > v_u(B′_u).

Three facts from serial dictatorship are used throughout.
- **(π)** If i wants Y_j at the picks, then j precedes i in π, by (I1). So k = x₀ ≺ x₁ ≺ ⋯ ≺ x_t along a canonical
  chain. If j ≺ i, then Y_i was available at j's turn, so v_j(Y_i) ≤ p_j.
- **(D)** Every frozen agent other than k values no junk good.
- **(U)** Nobody wants B_{x_t} at the picks. In particular, no pickless agent values it.

**Lemma D1-chain.** k has a canonical chain. If the picks form a maximum matching, the head of every canonical chain
holds a pick.

*Proof.*
1. k is frozen, so some x₁ wants Y_k. As long as x_i is frozen, some x_{i+1} wants Y_{x_i}.
2. By (π) these agents are distinct, so the walk stops at an unfrozen x_t.
3. With a maximum matching, x_t lies on a want-chain above the dangerous agent k, so it is not pickless by Lemma MAX
   (2). ∎

Without a maximum matching, x_t may be pickless. Then B_{x_t} = ∅ and Π = J, and everything below still holds.

**Proposition 3′ (the pool is improving; K4.OCH.D1POOL).** If z is unfrozen at the picks, then
v_k((J ∪ B_z) ∩ R_k) > p_k. In particular, every canonical chain from k has an improving H₀, hence an
inclusion-minimal one.

This is Proposition 3 (§5) carried from f = 1 to D = {k}.

*Proof.* Suppose v_k((J ∪ B_z) ∩ R_k) ≤ p_k. Apply Lemma 2\* at the picks with owner z and H = ∅.
- (G1): every agent other than z holds at most one good, and a bundle of at most one good threatens nobody.
- (G2): junk ranks below the pick of every agent that values it (I2), and pickless agents value no junk.
- (H1): W_z = B_z ∪ J.
  - A frozen q ≠ k values no junk (D). So W_z ∩ R_q ⊆ B_z, a single good worth at most p_q because z is unfrozen.
    Hence q is not threatened.
  - k is not threatened, since v_k(W_z ∩ R_k) ≤ p_k.
- No holder is non-movable. Nobody wants B_z, because z is unfrozen. And |B_z| ≤ 1, so no danger set lies inside B_z.

So H = ∅, with its empty system of representatives, satisfies Lemma 2\*'s condition. The picks then have an S\*
completion with owner z, a contradiction. ∎

**Lemma D1-red (K4.OCH.D1RED).** Let P be a canonical chain from k with an improving H₀, and let B′ be the state after
it. Minimality of H₀ is not needed. With owner k:
1. Lemma 2\*'s hypotheses (G1) and (G2) hold at B′. Moreover, no agent other than k wants a good of Π, so no holder
   wants a good of B′_k.
2. The agents frozen at B′, other than k, are frozen agents of the picks (k excluded) and possibly x_t.
   - Each of them except x_t is unthreatened by every subset of Π.
   - x_t is frozen at B′ only if some agent w ∉ P wanted a at the picks, i.e. x_{t−1}'s pick has a *second wanter*.
   - k wants no pick of the chain.
3. A holder at B′ that is exposed, for some H, is either x_t or an agent off P that is unfrozen at the picks. A holder
   is non-movable in Lemma 2\*'s sense iff it is exposed and crowded by H₀.
4. Hence Lemma 2\*'s condition C(B′, k) reads: some H ⊆ J′ satisfies
   - **(H1′)** x_t is not frozen at B′, or x_t is not threatened by Π ∖ H at v_{x_t}(a); and
   - H has a system of distinct admissible holders that covers every crowded exposed holder.

   In particular, **if neither HEAD nor CROWD occurs, B′ has an S\* completion owned by k**, with H = ∅.

*Proof.* At B′:
- B′_k = H₀;
- B′_{x_i} = {Y_{x_{i−1}}} for 1 ≤ i ≤ t;
- every other agent keeps its pick, or nothing.

Values rise exactly for k (v_k(H₀) > p_k) and for x₁, …, x_t, each of which wanted its new good. All other values are
unchanged.

1. *(G1) and (G2).* (G1) holds because every agent other than k holds at most one good. For (G2) in the strengthened
   form, let g ∈ Π and i ≠ k.
   - If g ∈ J and i values g, then i has a pick and v_i(g) ≤ p_i ≤ v_i(B′_i), by (I2).
   - If g = Y_{x_t} and i ≠ x_t, then v_i(g) ≤ v_i(B_i) ≤ v_i(B′_i), by (U).
   - If g = Y_{x_t} and i = x_t, then v_{x_t}(g) = p_{x_t} < v_{x_t}(a).
2. *The frozen agents.* Let q ≠ k be frozen at B′.
   - Suppose q is off P and unfrozen at the picks. Its good Y_q was unwanted at the picks, and the values that
     changed only rose, so Y_q is still unwanted. That is impossible. So q is frozen at the picks or
     q ∈ {x₁, …, x_t}. Each of x₁, …, x_{t−1} is frozen at the picks, since x_{i+1} wanted its pick. Hence
     q ∈ F ∖ {k} or q = x_t.
   - Let q ∈ F ∖ {k}. Then q values no junk (D), so Π ∩ R_q ⊆ {Y_{x_t}}, a single good worth at most
     p_q ≤ v_q(B′_q) by (U). Removing a good from any S ⊆ Π leaves at most that good, so q is not threatened by S.
   - Who wants a at B′?
     - Not x_{t−1}, which values a at p_{x_{t−1}}, below its new good.
     - Not x_j for j < t − 1: by (π), v_{x_j}(a) ≤ p_{x_j} < v_{x_j}(B′_{x_j}).
     - Not k: v_k(a) ≤ p_k < v_k(H₀). For t = 1, a = Y_k itself.

     So a wanter of a at B′ is off P. Its value did not change, so it wanted a at the picks.
   - By the same comparisons, k wants no good Y_{x_i} with i < t.
3. *The holders.* Let u be an exposed holder at B′, threatened by Π ∖ H at v_u(B′_u).
   - If u is frozen at the picks, or a middle agent x_i (0 < i < t), which is frozen at the picks, then the
     argument of 2 shows u is never threatened. So u = x_t, or u is off P and unfrozen at the picks.
   - Lemma 2\* calls an exposed holder non-movable if it wants a good of B′_k = H₀, which is impossible by 1, or if
     it has a danger set inside H₀, which is crowding.
4. *Conclusion.* By 1–3, (H1) of Lemma 2\* is (H1′), and its condition on systems of distinct representatives is the
   one stated.
   - If HEAD fails, H = ∅ satisfies (H1′).
   - If CROWD fails, no exposed holder is non-movable, so the empty system suffices.

   Lemma 2\* then gives the completion. With H = ∅, k takes J′, and the exposed holders serve themselves by Theorem
   DT's moves. ∎

*Remarks.*
1. *KWANT is harmless.* Obstacle (c) of `d1_obstacles.py` is "k wants a good held by another agent". By 2, such a good
   is not a chain pick, so it is the pick of some q ∈ F ∖ {k}, still held by q. A bundle of one good threatens nobody.
   All 6 such chains of the census repair.
2. *A longest canonical chain never has HEAD with every second wanter frozen at the picks* (case H-i below).
   - Suppose such a second wanter w exists. P_w = (x₀, …, x_{t−1}, w) continues past w, since w is frozen, by the walk
     of Lemma D1-chain. By (π), all its agents are distinct.
   - So P_w is a canonical chain with at least t + 1 steps, and P was not longest. ∎
3. *f = 1 with one wanter.* HEAD cannot occur there, since there is no second wanter. Theorem F1₁ settles these
   starts, but with another owner: case (B2) uses o ∉ {x, w}, (B3a) uses w, and (B3b) completes at the picks. So it
   does not give the ED-MIN form with owner k.

**Reduction of Finding D1.** Finding D1 follows from Lemma D1-chain, Proposition 3′, Lemma D1-red and the sub-lemmas
D1-H and D1-C below.
1. Take any canonical chain from k and any minimal improving H₀. Both exist.
2. If neither obstacle occurs, Lemma D1-red repairs.
3. If HEAD occurs and the chain fails, D1-H gives a repair.
4. If only CROWD occurs and the chain fails, D1-C gives a repair.

**Census.** All 321 canonical chains from k with a minimal improving H₀, at the 197 starts, owner k (`d1_obstacles.log`):

| chains | number | with an S\* completion owned by k |
|---|---|---|
| no obstacle | 276 | 276 |
| HEAD | 31 | 23 |
| CROWD | 8 | 6 |
| KWANT | 6 | 6 |
| **free of HEAD and CROWD** (Lemma D1-red applies) | **282** | **282** |
| all | 321 | 311 |

- Each of the 10 failing chains has exactly one of HEAD and CROWD (8 HEAD, 2 CROWD).
- 189 of the 197 starts have a chain free of both obstacles.
- The other 8 starts (4 configurations, listed below) are still repaired by a chain with an obstacle, through
  compensation.

*Checks of the proved parts* (`d1_subcases.py`, P1–P5; 0 violations on every data set):
- P1: the head always holds a pick. In fact all 197 starts have maximum-matching picks. This is observed, not proved,
  and not needed.
- P2: the pool is improving for every chain end (Proposition 3′).
- P3: the head is frozen after the chain only when there is a second wanter off the chain, and k wants no chain pick.
- P4: the frozen agents of the picks other than k value no junk, and crowded holders are x_t or off-chain agents
  unfrozen at the picks.
- P5: no chain free of HEAD and CROWD fails (Lemma D1-red).

**Sub-lemma D1-H (K4.OCH.D1H, open; narrowed below to D1-H(ii) for longest chains).** Let P be a canonical chain from k whose head is frozen after P, i.e. x_{t−1}'s
pick a has a second wanter w ∉ P at the picks. If no minimal improving H₀ makes C(B′, k) hold for P, then some
canonical chain P_w = (x₀, …, x_{t−1}, w, …) through such a w does, with a minimal improving H₀.
- Data (`d1_subcases.log`): 8 of 8 failing HEAD chains. By paths with HEAD:
  - **(H-i) every second wanter of a is frozen at the picks:** 5 paths. The same path never repairs, and P_w always
    does. By Remark 2, a longest chain is never in this case.
  - **(H-ii) some second wanter w is unfrozen at the picks:** 14 paths. Here w is a holder at B′. On 13 of them the
    same path repairs, with H containing a good of x_t's danger set. This is the duality of Theorem F1₁'s (B3): the
    agent that freezes the head is the one that unblocks it. The 14th, log557, is repaired through w, whose new value
    is higher, so that head is not threatened.
- **Smallest failing instance: log152** (n = 3, m = 5). Also r1173 (n = 3, m = 5).
  - Data: sets [[0,3,1],[2,1,4],[1,3,2,0]], values [[25,20,27],[43,58,35],[13,10,5,17]], order (1, 0, 2), picks
    (0, 1, 3), J = {2, 4}, F = {0, 1}, k = 1, W_1 = {0, 2}.
  - The chain (1, 2) with H₀ = {2, 4} fails. Agent 0 still wants good 1, so the head 2 is frozen. The head is
    threatened by {2, 3}, worth 15 > 13. No holder is left to keep good 3 out.
  - The chain through the frozen second wanter 0, (1, 0, 2), repairs: k takes {2, 4, 3}.

**Sub-lemma D1-C (K4.OCH.D1C; proved below outside three residual cases, by Proposition D1-C′).** If P has CROWD but not HEAD, and C(B′, k) fails for H₀, then another minimal
improving H₀′ on the same chain satisfies it.
- Data: 2 of 2 failing CROWD chains, which are one configuration (r1179 = log558). The other 6 CROWD chains repair by
  compensation: the crowded holder takes a junk good.
- **Smallest instance: r1179** (n = 4, m = 9).
  - Data: sets [[0,3,6,7],[1,4,6,7],[2,5,8],[3,4,5,8]], values [[8,1,6,4],[4,8,3,2],[4,2,3],[5,8,6,4]], order
    (0, 2, 3, 1), picks (0, 1, 2, 4), f = 1, k = 3, W_3 = {1}.
  - The chain (3, 1) has three minimal improving sets: {3, 5}, {3, 8} and {5, 8}.
  - {5, 8} crowds agent 2: 2 + 3 > 4. With it the chain fails.
  - {3, 5} crowds nobody and repairs (Lemma D1-red).
  - This is the starting point for a proof: k's pool goods number at most three (|R_k| ≤ 4), so a holder crowded by
    one minimal pair should leave another pair free. That is case (B2) of Theorem F1₁ in miniature.

**Conjecture D1-LONG (K4.OCH.D1LONG): REFUTED** by D1H-X (below, and `attempts/k4-oc1-hall-d1-long.md`). As first stated: At a hard start with D = {k}, some *longest* canonical chain from k,
with some minimal improving H₀, leaves an S\* completion owned by k.
- Data: 197 of 197 starts.
- Every longest chain works at 196 starts. The exception is log557 (n = 3, m = 6), where the two length-1 chains
  differ by case H-ii, as above.
- Every chain works at 191 starts.
- By Remark 2, for a longest chain only case H-ii of HEAD, and CROWD, are left to prove.

**The 4 configurations without a chain free of both obstacles.** Each is repaired by compensation:
- **lb4-n2m5-upgrade** (n = 2). Its only chain is (0, 1). H₀ = {2, 3} crowds the head 1 (4 + 5 > 8), and the head
  takes junk good 1. Completion [[2,3,0],[4,1]].
- **lil-noncore-n3.** k = 0's pick has two wanters, 1 and 2, both unfrozen (H-ii). With the chain (0, 1), the head
  is frozen by 2 and threatened by {4, 5, 6}, and the second wanter 2 takes good 6. Completion
  [[1,2,3,4,5,8],[0],[7,6]].
- **r461, r2749.** The same pattern (H-ii). The second wanter takes a junk good, or the head's released pick: in
  r2749 with the chain (0, 1), agent 2 takes good 1.

So the junk given to holders is small: 157 starts are repaired with none (k takes the whole pool), 38 with one good,
and 2 (r1179 and log558) with two. This counts DT's moves too, so it is not |H| of Lemma 2\*.

**D1-C is proved except for three residual cases** (`k4/oc1_hall/d1_crowd.py`, `d1_crowd.log`). The tool is the
duality of Theorem F1₁'s (B3), now at the picks: a holder that could be crowded is a helper for its favourite pool
good.

**Lemma D1-C₀ (favourites; K4.OCH.D1FAV).** Take a hard start with D = {k}, an agent z unfrozen at the picks,
Π = J ∪ B_z and Π_k = Π ∩ R_k. For an agent u ∉ {k, z}, unfrozen at the picks and valuing a good of Π, let b_u be
u's favourite good of Π.
- (a) |Π ∩ R_u| ≤ 3. For every S ⊆ Π ∖ {b_u}, u is not threatened by S at v_u(B_u) + v_u(b_u).
- (b) For every set U″ of such agents whose favourites are pairwise distinct and all lie in J,
  v_k(Π_k ∖ {b_u : u ∈ U″}) > p_k.

*Proof.*
- (a) u holds a pick: a pickless agent values no junk (I2) and does not value B_z (z is unfrozen). Since Y_u ∉ Π,
  |Π ∩ R_u| ≤ |R_u| − 1 ≤ 3. The goods of Π ∩ R_u other than b_u are at most two. Each is worth at most v_u(b_u),
  because b_u is u's favourite. Each is also worth at most v_u(Y_u): for junk by (I2), and for B_z because z is
  unfrozen. So any set of them is worth at most v_u(b_u) + v_u(Y_u), and removing a good only lowers the value.
- (b) Otherwise apply Lemma 2\* at the picks, with owner z and H = {b_u : u ∈ U″} ⊆ J, each b_u matched to u.
  - (G1), (G2), the frozen agents other than k, and the absence of non-movable holders: as in Proposition 3′.
  - k is not threatened, since (W_z ∖ H) ∩ R_k ⊆ Π_k ∖ H is worth at most p_k.
  - Each u ∈ U″ is admissible for b_u. If u is unexposed, this holds by definition. If u is exposed, it values b_u,
    and by (a) it is not threatened by W_z ∖ H ⊆ Π ∖ {b_u} at p_u + v_u(b_u).

  So the picks would have an S\* completion, a contradiction. ∎

**Proposition D1-C′ (K4.OCH.D1CP).** Take a hard start with D = {k}, and a canonical chain P from k without HEAD. Let
U′ be the agents off P, unfrozen at the picks, that value at least two goods of Π_k. Suppose their favourites b_u are
pairwise distinct and lie in J. Then:
- some minimal improving H₀ lies inside Π_k ∖ B(U′), by Lemma D1-C₀ (b) with z = x_t;
- every such H₀ that does not both crowd the head and contain Y_{x_t} leaves an S\* completion owned by k.

*Proof.* Without HEAD, (H1′) of Lemma D1-red holds for every H. If x_t is frozen at B′, it is unthreatened by Π, hence
by every subset, since being threatened is monotone. By Lemma D1-red (3), each crowded holder is x_t or an agent off P
unfrozen at the picks. The latter values two goods of H₀ ⊆ Π_k, so it lies in U′.

Let H consist of b_u for each crowded u ∈ U′, together with Y_{x_t} if the head is crowded. These goods are
pairwise distinct (distinct favourites in J, and Y_{x_t} ∉ J). They lie in J′ = Π ∖ H₀: H₀ avoids B(U′), and
Y_{x_t} ∉ H₀ when the head is crowded. Match each crowded holder to its good.
- A crowded u ∈ U′ is admissible for b_u by Lemma D1-C₀ (a). Its values and Π are those of the picks, since u is off P.
- A crowded head holds a. Π ∩ R_{x_t} ⊆ {Y_{x_t}} ∪ (J ∩ R_{x_t}), with at most two junk goods, each worth at most
  p_{x_t} < v_{x_t}(a). So after Y_{x_t} is matched to it, any set of its remaining pool goods is worth at most
  2p_{x_t} < v_{x_t}(Y_{x_t}) + v_{x_t}(a). It is admissible.

This system of representatives covers every crowded exposed holder, and Lemma D1-red (4) gives the completion. ∎

*The residual cases of D1-C*:
- **C-a:** two agents of U′ share their favourite;
- **C-c:** some favourite is Y_{x_t};
- **C-b:** every minimal improving H₀ ⊆ Π_k ∖ B(U′) crowds the head and contains Y_{x_t}.

*Check* (`d1_crowd.py`; 0 violations):
- Lemma D1-C₀ (b) holds for every subset U″, on all 227 chains without HEAD.
- Proposition D1-C′'s completion exists in all 276 cases where it applies.
- The proposition covers 224 of the 227 chains.
- The other 3 are C-b, and all are copies of lb4-n2m5-upgrade (n = 2). C-a and C-c never occur.

So on the data with n ≥ 3, **every canonical chain from k without HEAD is repaired by a proved argument.**

**Split (coordinator, 22:58).** Sub-lemma D1-H(ii) and the residual cases C-a to C-c went to the workstream
`proof/k4-d1`, which also received the material above. This note keeps D1-LONG's structure and the write-up.
The |D| ≥ 2 cases went to `proof/k4-oc1max-multi`.

**What is left for |D| = 1: one sub-lemma** (plus the residual cases C-a to C-c, which are absent from the data at
n ≥ 3). Take a longest canonical chain P. If P has no HEAD, Proposition D1-C′ repairs, outside C-a to C-c. If P has
HEAD, then by Remark 2 every second wanter is unfrozen at the picks, and this is the open case:

> **Sub-lemma D1-H(ii) (K4.OCH.D1H): REFUTED in this canonical form by D1H-X, see below.** Let P be a longest canonical chain from k whose head is frozen after P.
> So every second wanter w of a is unfrozen at the picks, and is a holder at B′. Then P, or some
> P_w = (x₀, …, x_{t−1}, w), with a minimal improving H₀, leaves an S\* completion owned by k.

- Data: 14 of 14 such paths. 13 repair on P itself, with a holder (usually w) taking a good of x_t's danger set.
  log557 repairs through w.
- Smallest instances: lil-noncore-n3 (n = 3, m = 9; it repairs on P, with H = {6}) and log557 (n = 3, m = 6; it needs
  P_w).
- Both P and P_w have the same length t, and in each the other wanter freezes the head. Only the head's at most three
  pool goods and the two wanters' values of a are involved.

**Update from `proof/k4-d1`** (`k4/d1.md` §3, PR #113; not refereed here). D1-C is proved there under the extra
hypothesis that every good is relevant to some agent, which cores satisfy. At a hard start with D = {k}, every
canonical chain without HEAD has some minimal improving H₀ with C(B′, k). Their new lemmas:
- **Lemma C3:** if the head is crowded by an H₀ containing Y_{x_t}, no other agent is unfrozen at the picks (via
  Proposition 3′ with owner o and helper x_t);
- **Lemma HC:** then the head has a robust compensation good, or the picks have a one-absorber completion with
  absorber x_{t−1}.

This covers C-a to C-c. Finding D1 then reduces to the starts where *every* canonical chain from k has HEAD.

*Cross-check* (`k4/oc1_hall/d1_allhead.py`, `d1_allhead.log`). In all the data these are 5 starts, 4 configurations:
lil-noncore-n3 with two orders, its logged copy log574, r461 and r2749. All have n = 3, t = 1 and f = 1, with two
wanters of Y_k, both unfrozen at the picks, and all are repaired. This is the f = 1, several-wanters case at n = 3
(§5, §11), which `proof/k4-d1` is now working on as "D1-H in all-HEAD form".

**Adversarial climbs against D1-LONG** (`k4/oc1_hall/climb_d1.py`, `climb_d1_n4.log`, `climb_d1_n5.log`,
`climb_d1_n6.log`; evidence).
- The objective is the number of repairing (longest chain, minimal H₀) pairs, minimized over the hard starts with
  D = {k}.
- n = 4: 40 rounds of 6,000 steps; 37 end at 1 and none at 0.
- n = 5: 30 rounds of 3,000 steps; the 13 rounds that stay hard end at 1.
- n = 6: random starts never reached a hard start with |D| = 1 in 12 rounds, so that run is not informative. The
  sampling at n = 6–8 below covers it.

**D1-LONG and D1-H(ii) are false in canonical form** (counterexample D1H-X, found by `proof/k4-d1`; re-verified by
`k4/oc1_hall/d1long_cex.py`, `d1long_cex.log`).
- Data: n = 3, m = 8. Sets [[0,1,5,7],[3,4,6,7],[0,2,5,7]], values [[26,3,25,27],[19,17,25,30],[9,14,7,29]], order
  (0, 1, 2), picks (7, 6, 2), D = {0}, and agents 1 and 2 both want good 7.
- Both canonical chains have HEAD for every improving H₀, and no completion is owned by k or by the head. After (0, 2)
  the off-chain second wanter 1 can own.
- The ED chain (0, 2), with the head also taking junk good 0 and H₀ = {1, 5}, repairs with owner k:
  [[1,5,2,4],[6,3],[7,0]].
- So step 3 of the Reduction of Finding D1 needs the head-junk option of §15's ED-MIN. Finding D1 itself (ED-MIN) is
  not refuted.
- The open statement is now D1-HJ (`proof/k4-d1`): at a hard start where every canonical chain from k has HEAD, some
  chain whose head adds at most one junk good, with a minimal H₀, repairs with owner k. Their data give 59 of 59.
- The n ≤ 5 data of this note have m ≤ 7 at n = 3, which is why this case never appeared.

**Theorem U** (`proof/k4-oc1max-multi`, `k4/oc1max_multi.md` §3; read here for |D| = 1 only).
- Setting: a longest canonical chain from k with head z, and any improving H₀ ⊆ J.
- Hypothesis: J threatens no unfrozen pick holder other than z, at its pick value; and if J threatens z, then z ends
  unfrozen.
- Conclusion: k owns an S\* completion. Lemma 2\* is applied with H = {Y_z}, so the owner's bundle is exactly J.
  - Y_z goes to z, whose slot {a, Y_z} is safe since v(J ∩ R_z) < 2p_z < v(a) + p_z. Otherwise it goes to a second
    wanter, unfrozen at the picks by Remark 2 and therefore unexposed.
- For |D| = 1 the argument is complete: the frozen agents other than k value no junk.
- For |D| ≥ 2 the hypothesis D_T = {k} gives it: every other dangerous agent, including a dangerous middle agent, is
  unthreatened by J at its pick value, hence also after the chain. Its authors have now made this explicit in
  `k4/oc1max_multi.md` §3.
- It applies at 15 of the 197 starts of §21. D1H-X lies outside it: J threatens both heads, and each ends frozen.

**Larger n** (`k4/oc1_hall/d1_big.py`, `d1_big_cores6.log`, `d1_big_n6.log`, `d1_big_n7.log`, `d1_big_n8.log`;
evidence). These runs use sampled orders, at most 60 per instance. The S\* completion is tested by SAT
(`big_sstar.sstar_sat`), an encoding written independently of the brute force used at n ≤ 5.

| data | instances | hard starts with \|D\| = 1 | D1-LONG holds | chains (RED / CPROP covered) | failures of the proved parts |
|---|---|---|---|---|---|
| n = 6 cores (one 4-good agent) | 120,000 | 121 | 121 | 230 (229 / 228) | 0 |
| random n = 6 | 120,000 | 154 | 154 | 301 (290 / 286) | 0 |
| random n = 7 | 60,000 | 22 | 22 | 46 (46 / 40) | 0 |
| random n = 8 | 40,000 | 12 | 12 | 21 (21 / 21) | 0 |

- Every chain free of HEAD and CROWD repairs (Lemma D1-red), and every chain that Proposition D1-C′ covers repairs:
  386 and 575 cross-checks in all.
- HEAD occurs on 7 chains (n = 6), and 2 of them repair.
- Hard starts with one dangerous agent become rare as n grows: 1 per 1,000 instances at n = 6, and 0.3 per 1,000 at
  n = 8.

## 22. OC₁^max and the R1-priority form fail at n = 4 (certifier); what breaks

The source is the ordinal CEGAR of `compute/k4-oc1max-cert`, verified by the coordinator (`k4/sdc/oc1max_cex_verify.py`,
`k4/sdc.md` §31 on `claude/kind-lamport-y8fdme`). It is re-analysed here with §21's machinery
(`k4/oc1_hall/oc1max_cex_analysis.py`, `oc1max_cex_analysis.log`). Both instances are perfect starts (ν = n = 4).

**cex1.** Sets [[0,1,2,5],[1,2,5,6],[3,4,5,6],[3,4,6]], values [[2,10,4,7],[10,3,4,8],[3,5,6,7],[3,2,4]], order
(0, 3, 2, 1), picks (1, 2, 5, 6), J = {0, 3, 4}, F = D = {0, 2, 3}.
- Agent 1 is the only unfrozen agent, and it holds its worst good 2.
- Agent 0 is dangerous but inert: its pool J ∪ {2} is worth 6 < p₀ = 10 to it.
- Agents 2 and 3 *share the junk danger pair {3, 4}*: 3 + 5 > 6 for agent 2, and 3 + 2 > 4 for agent 3.
- The canonical chains, each with H₀ = {3, 4}:
  - (2, 1): no HEAD and no CROWD, but agent 3 is still frozen and threatened by the pool;
  - (3, 1): CROWD, since agent 2 is crowded and nothing compensates it;
  - (3, 2, 1): agent 2 is threatened.
- No state one move away (chains and rings) has a one-absorber completion (SAT).

**cex2.** Sets [[0,4,5,6],[1,2,3,5],[1,3,5,6],[2,4,6]], values [[2,3,10,6],[3,10,6,8],[5,3,7,6],[4,3,2]], order
(3, 1, 2, 0), picks (4, 5, 6, 2), J = {0, 1, 3}, F = {1, 2, 3}, D = {1, 2}.
- Agents 1 and 2 share the junk danger pair {1, 3}: 3 + 6 > 8 and 5 + 3 > 6.
- The canonical chains:
  - (1, 0): CROWD, on agent 2;
  - (1, 2, 0): agent 2 is threatened;
  - (2, 0): agent 1 is threatened.

**What breaks.** Both starts have |D| ≥ 2, so §21 (|D| = 1: D1-red, D1-C′, D1-LONG) is not contradicted. What fails
is exactly §21's lever (D): the frozen agents other than the chain's first agent value no junk. Here a second
dangerous agent values the *same* junk pair as the first. There is at most one holder slot, so whoever owns the pair
must also hold the leftover junk, and then the other agent sharing the pair is threatened.

**Every order** (`oc1max_cex_analysis.log`, part 2). Every pick vector is a maximum matching.

| | distinct pick vectors | complete at the picks | after one move | need two moves |
|---|---|---|---|---|
| cex1 | 7 | 4 | 2 | 1 (the order above) |
| cex2 | 6 | 4 | 1 | 1 (the order above) |

- **Both failing starts also arise from R1-priority orders**, so the R1-priority alternative of §18–§19 is refuted as
  well. The printed order (0, 3, 2, 1) of cex1 is not itself R1-priority (`k4/sdc.md` §2), but the R1-priority order
  (3, 2, 0, 1) gives the same picks (paper session's correction). The test in `oc1max_cex_analysis.py` asks whether
  the pick vector arises from some R1-priority order.
- *Two sequential moves repair both.*
  - cex1: the chain (2, 1), then the chain (0, 1). The second chain starts at the inert dangerous agent 0 and gives
    agent 1 its top good.
  - cex2: the chain (1, 0), then a second chain from agent 1. So "one chain per dangerous agent" is not the shape of
    the repair.

**Consequences.**
- For TARGET₄, any finite sequence of improving moves is enough, because the final completion is EFX₀ whatever the
  bases were. These instances refute the *one-move* forms (OC₁^max, OC₁-ED\*^max, and the R1-priority forms), not
  the approach.
- §1–§21's lemmas about a given state (Lemmas 1, 2, 2\*, 4, MAX, D1-red, D1-C₀; Propositions 3, 3′, 5, D1-C′; Theorem
  F1₁) are unaffected.
- So is the conditional conjecture D1-LONG: for |D| = 1, one move should still suffice.
- The obstruction is a *shared junk danger pair* among dangerous agents together with a slot deficit. If s dangerous
  agents share one pair and there are no slots, one owner can absorb the pair, and the other s − 1 sharers then each
  need to be lifted by a move. So a fixed bound of two moves may fail once s = 3. That is an instance to search for at
  n = 5.

**Cross-workstream notes (`proof/k4-oc1max-multi`, `k4/oc1max_multi.md` on its branch; not refereed here).**
- *Proposition D1-C′ needs |D| = 1.* Lemma D1-C₀ (b) uses D = {k}. The |D| ≥ 2 session's instance T3 confirms that
  the conclusion fails otherwise.
  - T3: order (0, 1, 2), picks (0, 4, 1), D = {0, 1}.
  - The only canonical chain with an improving set is 1 → 2, with H₀ = {1, 3}. Its only obstacle is CROWD, on the
    head, and no owner works after it (checked here with `d1_subcases.analyse`).
  - In §21's terms this is case C-b: U′ = ∅, the head is crowded, and Y_{x_t} = 1 ∈ H₀. So C-b really occurs once
    |D| ≥ 2. The data have no instance of it with |D| = 1 and n ≥ 3.
- *Lemma KEEP* (theirs).
  - Setting: H₀ ⊆ J, and k is threatened by J alone.
  - Lemma 2\* with H = {Y_{x_t}}: the head's released pick goes to a holder admissible for it. That holder is the
    head itself when it is unfrozen after the chain, by the computation in Proposition D1-C′, or the second wanter.
  - The owner's bundle is then pure junk, and HEAD reduces to "the head, if frozen, is not threatened by J".
  - This bears on Sub-lemma D1-H(ii), and has been forwarded to `proof/k4-d1`.
- *Lemma D-red* (theirs) carries Lemma D1-red to any |D|. The only new obstacle is DEMAND: another dangerous agent,
  still frozen, threatened by the pool.
- *An n = 5 strict-core counterexample to OC₁^max* (TTC session).
  - Data: sets [[0,4,5,6],[2,3,4,6],[0,1,5,6],[2,4,5,6],[0,1,7,8]], values [[3,2,10,6],[4,1,6,8],[2,8,5,4],[5,4,8,2],[7,8,2,4]],
    order (1, 3, 4, 2, 0), picks (4, 6, 0, 5, 1), perfect.
  - It lies outside the K4.MC2 class: agent 4 has the private pair {7, 8}.
  - The mechanism is the same. D = {1, 3, 4}. Agents 1 and 3 share the *pool* pair {2, 4}, junk good 2 plus the chain
    end's released pick 4 (4 + 6 > 8 and 5 + 4 > 8). Agent 4 is inert.
  - Every canonical chain from 1 or 3, with H₀ = {2, 4}, leaves the other sharer frozen and threatened (DEMAND), with
    no HEAD and no CROWD.
  - So the shared pair need not be pure junk: it can contain B_{x_t}.
- *The owner need not be x₀ or x_t when |D| ≥ 2* (matching session, `proof/k4-matching`, `k4/matching.md`).
  - Their instance pw94: sets [[0,4,5,6],[1,4,5,6],[0,1,2],[1,0,3]], values [[20,18,12,19],[20,17,15,14],[4,5,1],[3,7,2]],
    picks (0, 1, 2, 3), perfect, D = {0, 1}.
  - Checked here: no ED chain leaves a completion owned by x₀ or x_t (`ed_check.classify`).
  - Yet every chain k → w (k ∈ {0, 1}, w ∈ {2, 3}) completes with the *other* wanter of Y_k as owner.
  - So OC₁ holds there, and only the owner restriction of OC₁-ED\* (b) fails. Both dangerous agents value the same
    three pool goods {4, 5, 6}, which again is a shared danger set.
- *Lemma M and Lemma EX* (matching session).
  - Lemma M is a full-witness matching form of Lemma 2\*: no movable/non-movable split, with the deficiency
    min_H (|H| − ν(Γ(H))).
  - Lemma EX is a sufficient condition after any chain, any owner and any |D|. Its condition (2) is checked in the
    slot graph of the picks, and it contains Lemma D1-red.
  - In EX, crowding is absorbed into the matching condition. That condition still has to be established, which is
    their Conjecture CM, so EX restates D1-C rather than proving it.

## 23. Integration: the proof plan for OC₂^max (coordinator's request, 23:35)

**The corrected statement.**
- OC₂^max: from every maximum-matching serial-dictatorship start, the picks, or the bases after at most two official
  moves in sequence, have a one-absorber completion.
- It is CERTIFIED for every strict profile of every core with n ≤ 4 (`compute/k4-oc1max-cert`, `k4/oc1cert.md`).
  n = 5 and a three-move search are running there.
- For TARGET₄ any finite number of moves would do, since the final completion is EFX₀ whatever the bases were.

### 23.1 Second reading of the matching session's Lemmas M and EX (`proof/k4-matching`, `k4/matching.md` §1, §3)

**Lemma M (S\* completability as a matching condition): CORRECT.** Both directions were read line by line.
- (⇒) The kept-out set H is the junk given to holders or dummies. (H1) holds because Q receives nothing. An exposed
  holder must receive a good it values that makes it safe, which is exactly an edge of Γ(H).
- (⇐) Bundles of at most two unwanted goods threaten nobody. Q's bundles fall under (G1) and only gain value. The
  owner gains. The matching handles the exposed holders, and the unexposed ones are safe at their base values.
- The formula follows from Mendelsohn–Dulmage (a covering matching plus a maximum one gives a maximum covering one)
  and König–Ore.
- Minor point: in the "min_H max_S (|S| − |N(S)|)" form, H ranges over the same restricted family ((H1), E(H)
  coverable) as in the first form.
- Lemma M is equivalent to Lemma 2\*, since both are exact. The movable holders' DT goods enlarge H.

**Lemma EX (a chain as an exchange in the picks' slot graph): CORRECT as a sufficient condition, but NOT exact.**
- The proof is sound:
  - values only rise along the chain;
  - agents off P that are unfrozen at Y stay unfrozen;
  - every good of H ⊆ J′ is unwanted at B′;
  - Ext agents hold one unwanted good;
  - every agent other than o is covered by (1′), by the matching, or by being an unexposed holder of N.
- The converse fails. (1′) requires every agent of P, and every agent of Ext, to be *unthreatened* by X outright, so
  the head cannot be compensated.
  - Instance: lb4-n2m5-upgrade (n = 2), chain (0, 1), H₀ = {2, 3}, owner k = 0.
  - B′ has an S\* completion owned by k, [[2,3,0],[4,1]] (EFX₀, raw): the crowded head takes junk good 1.
  - Yet no H ⊆ J′ = {0, 1} satisfies EX's hypotheses. H = {0, 1} is the only one meeting (1′), and it needs one
    matching edge, with N = ∅ and s = 1.
  - Script: `k4/oc1_hall/ex_not_exact.py`, log `ex_not_exact.log`.
- On this note's data at n ≥ 3, no head was compensated in Proposition D1-C′'s cases, so the gap is at n = 2 only.
  But "exact one-chain criterion" should read "sufficient".
- The remark "D1-red is EX with H = ∅" holds only when no holder is exposed. In general D1-red corresponds to EX with H
  equal to the goods of the DT moves, via Lemma M ⟺ Lemma 2\*.
- *Suggested exact version:* apply Lemma M at B′ directly, with the chain's single-good holders of B′ (Ext and an
  unfrozen head) as compensable holders at their B′ values. EX's picks-graph form is then a sufficient specialization.
- *Update:* the matching session has written this version as **EX\*** (`k4/matching.md` §5). It reports that EX\* is
  exact for the second move on all 3,308 failing profile–start pairs of the 11 n = 4 cores. In 35 of the 57 repairing
  pairs at the stored starts, the second chain's head collects two foreign picks.

### 23.2 The case tree

Each leaf is a named statement with its status and the session that owns it.

| # | case | statement | status | owner |
|---|---|---|---|---|
| 0 | maximum-matching start ⟶ perfect start | Lemma RED (k4/sdc.md §31) with Lemma MAX (§19) | RED: written proof, read here (§22 message, no hole; caveat: null agents count as ordinary agents for the one-absorber shape). MAX: proved | coordinator; this note |
| 1 | the picks complete, or a state completes | Lemma 1 (slots), Lemma 2\* / Lemma M (exact S\* count), **Lemma M^c** (exact one-absorber count at perfect starts, frozen slots included; assumes only (G2)) | Lemma 1, 2\*: proved, 2\* refereed. M, EX\*: refereed. M^c: written; exact on all data (2,226,322 owner tests) | this note; matching; k4-oc1max-multi |
| 2 | hard ⟹ D ≠ ∅ | Proposition T0: every unfrozen z has a dangerous agent threatened by J ∪ B_z (cf. Prop. 3′ here) | written proof | k4-oc1max-multi |
| 3 | \|D\| = 1: **one move** (an ED chain, the head possibly taking one junk good) | Lemma D1-chain, Prop. 3′, Lemma D1-red, Remark 2 (a longest chain avoids H-i), Lemma D1-C₀ and Prop. D1-C′ (§21) | proved | this note |
| 3a | \|D\| = 1, CROWD residuals C-a to C-c | D1-C via Lemmas C3 and HC (needs every good relevant) | written proof, not refereed | k4-d1 (PR #113) |
| 3a′ | \|D\| = 1, CROWD in general | Theorem D1-C: every canonical chain without HEAD has a minimal H₀ that repairs | written proof, not refereed (`k4/d1.md` §3) | k4-d1 |
| 3b | \|D\| = 1, every canonical chain has HEAD | **D1-H2** (refines D1-HJ): some canonical chain (prefix, u), or its extension (prefix, u, u′) in which the other wanter u′ of a takes y_u plus junk, repairs with owner k and a minimal H₀; no head junk on a single chain. **Proposition D1-H₃′**: D1-H2 holds on all 763 three-agent core structures (SMT, two encodings, ties included, no MC2). **Lemma CONTRACT** (t = 1): given S1 (a has exactly two wanters) and S2 (they are the only agents unfrozen at the picks), deleting the other agents leaves a three-agent core whose repairs lift | D1-H₃′ and CONTRACT: written, computer-verified, not refereed. **S2 is false** (S2-X, n = 4, a strict core), so CONTRACT covers only starts without extra active agents or a third wanter. **Open:** D1-H2 at all-HEAD starts with extra active agents or a third wanter, and t ≥ 2 | k4-d1 (`k4/d1.md` §7, 8a3bc43) |
| 4 | \|D\| ≥ 2 after a canonical chain | Lemma D-red: the obstacles are HEAD, CROWD and DEMAND | written proof | k4-oc1max-multi |
| 4a | the head's Θ(z) ⊆ {k} | Corollary TR: no DEMAND, so case 3 applies | written proof | k4-oc1max-multi |
| 4b | one truly dangerous agent | **Theorem U** (refereed) proves OC₁ outright at 2,880 starts; Lemma KEEP (refereed) and Corollary KEEP-1; KEEP-C (8 starts) open | proved plus open residue | k4-oc1max-multi |
| 4c | k takes a shared junk pair | Lemmas SET and OWN (the PWk(a) overlap step and its owner) | written proofs | k4-oc1max-multi |
| 4d | several truly dangerous agents, or DEMAND with none | **SLOT** (581 starts): one or two slots, the head's among them, cover what the chain leaves. Plain Lemma M suffices: counting existence is enough | **open** | k4-oc1max-multi |
| 4e | the head is a second dangerous agent | Lemma RING-red proves 151 starts. **RING** (45 starts left) is open. 27 of them have an M^c-certified repair with a compensated wanter, but every RING start also has a repair certified by plain Lemma M | proved plus open residue | k4-oc1max-multi |
| 4f | disjoint danger sets: one move | "one chain repairs" when no two dangerous agents share a pool danger set | **evidence** (k4-oc1max-multi, `k4/oc1max_multi/sharing.py`). Without sharing: 7,755 starts, all repaired by one move. 7,681 have a canonical chain from D owned by k, and 7,237 are covered by written lemmas (KEEP 4,657, OWN 632, D-red 1,835, RING-red 113). The 74 others fail only by CROWD (58) or the T3 ring shape (16), never by DEMAND. With sharing: 628 starts, all one move, 623 canonical. So sharing is necessary for every known two-move start, but not sufficient | k4-oc1max-multi |
| 5 | **no one-move repair: the second move.** One statement, **Sub-lemma SHARE₂** (K4.OCH.SHARE2), stated below the table | (i) and (ii) below | **open** | see 5a–5c |
| 5a | the shape of a two-move start: **R2**, then **LIFT-SHAPE⁺** | **R2** (TTC session): two or more receivers ⟹ one move. *Certified at n = 4* (compute/k4-oc1max-cert, PR #114: every failing start has exactly one receiver). At n = 5 the first ~700 pure cores agree. **Lemma R2-G2** (proved): after any chain to a receiver, no junk good is wanted. So R2 reduces to **R2-M**: Lemma M^c's condition with owner x₀. **LIFT-SHAPE⁺:** one receiver z; a canonical P₁ to z with a shared pool pair that leaves z unfrozen; a canonical P₂ to z giving z its favourite good; (L1)–(L3) | R2: certified at n ≤ 4, open in general (R2-M open). LIFT-SHAPE⁺: **certified at n = 4** (K4.MATCH.LIFT.N4; 112,880 starts; at n = 4 only H = ∅ or {z's best junk good} is needed), **REFUTED at n = 5** (K4.MATCH.LIFT; 5_pure#164; `attempts/k4-matching-lift-shape.md` on proof/k4-matching; re-verified by `k4/oc1_hall/liftshape_n5_check.py`). Items 1 and 2 hold there, item 3 fails | TTC session (R2); matching and k4-oc1max-multi (LIFT-SHAPE⁺) |
| 5b | SHARE₂ (ii), route M (matching) | Lemmas LIFT-red and LIFT-1 (k ≤ 4): under (L1)–(L3), h takes X minus z's best junk good g, and z takes {t, g} | **refereed** (with EX\*). With LIFT-SHAPE⁺, this route closes n = 4 only | matching |
| 5c | SHARE₂ (ii), route R (multi) | Lemma LIFT deletes k and its pair T; then OC2-REC, the one-move theory in I⁻ | LIFT: **refereed**. OC2-REC: open | k4-oc1max-multi |
| 5d | a wider single move instead: **OC₁′** (kgen-rounds) | non-end chain agents may also take goods of the end's released base | **holds on every n = 4 core** (all 112,880 starts, two independent checks), **fails at n = 5** (5_pure#164, three implementations agree; K4.SDC.OC1PMAX). The obstruction there is two disjoint conflicts, which no single move can settle (leaf 4a of §23.4) | proof/kgen-rounds; coordinator |
| 6 | three moves needed? | three sharers of one pool pair with no slots | none found. OC₂^max is certified at n ≤ 4, and holds on the first ~700 pure n = 5 cores. A targeted search is running at n = 5–7. OC₁^∃max (some maximum-matching order satisfies OC₁) is certified at n = 4 | compute/k4-oc1max-cert |

> **Sub-lemma SHARE₂ (K4.OCH.SHARE2; leaf 5, one statement; names reconciled 00:04).** Let Y be a one-absorber-hard
> perfect start (k ≤ 4, strict) with no one-move repair.
> - **(i) Shape.** Y has exactly one receiver z. Some dangerous agent k has a canonical chain P₁ to z whose set
>   H₀ = T ⊆ J ∪ {y_z} is improving for k and for a second dangerous agent (a shared pool danger set).
> - **(ii) Second move.** After P₁, deleting k and T leaves a perfect SD start of I⁻ = I − k − T. That start has a
>   one-move repair whose completion does not threaten k (OC2-REC). Lemma LIFT (refereed) lifts it back to I.
>   - The earlier form of (ii), "some canonical P₂ ends at z and gives z its favourite good" (LIFT-SHAPE⁺ item 3), is
>     certified at n = 4 but **refuted at n = 5** by 5_pure#164 (below). There, the repairing second moves include
>     chains vertex-disjoint from P₁ that settle an independent danger set.
>
> *How the names map.*
> - OC2-LIFT (§23.3) is the earlier, weaker form. It follows from (ii), because z then wants nothing, so every DEMAND
>   agent that z alone froze is unfrozen.
> - LIFT-EX (matching) is (i) together with (ii), certified by Lemma M at B₂ (route M, LIFT-red then LIFT-1).
> - OC2-REC (multi) is (ii), now the only general form; route M covers n = 4.
> - Both routes produce the same P₂. They differ only in how the final completion is certified.

**The open core at k = 4** (coordinator's summary, 00:00). OC₂^max follows from the proved and written leaves and
three precise lemmas:
1. **D1-H2** (leaf 3b; `proof/k4-d1`). The three-agent core is verified, and CONTRACT reduces t = 1 to it when there are
   no extra active agents. Open: all-HEAD starts with extra active agents or a third wanter (S2 is false, by S2-X),
   and t ≥ 2.
2. **R2** (leaf 5a; TTC session). Two or more receivers ⟹ one move.
3. **The second move** (§23.4 item 4). Either 4a, disjoint repairs in one round (smallest 5_pure#164), or 4b,
   SHARE₂'s sequential move OC2-REC (route R, leaf 5c). Route M (LIFT-SHAPE⁺) and OC₁′ are certified at n = 4 and
   false at n = 5. This item is not needed if **OC₁′** (leaf 5d) holds, since then one wider move suffices.

Leaves 4d (SLOT) and 4e (RING) of the one-move side are still open as well. They cover starts with one move, which R2
and LIFT do not touch.

### 23.4 The open core (00:36): exact statements, owners, smallest test instances

Everything else in the tree is proved, refereed or certified. A start is *hard* when it has no one-absorber completion
at the picks. Every statement is for k ≤ 4 and strict values. A *receiver* is an agent unfrozen at the picks that
holds a pick.

1. **D1-H2 with extra active agents** (`proof/k4-d1`). The route through S1 ∧ S2 is closed, because S2 is false.
   - Statement: D1-H2 at all-HEAD hard perfect starts with D = {k} and t = 1 that have extra *active* agents (unfrozen,
     outside W(a), valuing junk) or a third wanter of a.
   - Without either, Lemma CONTRACT reduces to the verified three-agent core. CONTRACT also deletes unfrozen agents that
     value no junk.
   - **S2 and its weakest needed form S2′ are false**, even in the K4.MC2 class. Smallest counterexample S2-X (k4-d1,
     `k4/d1/s2_probe.py`; re-verified here by `k4/oc1_hall/s2x_check.py`, `s2x_check.log`: `is_core4` = [], hard,
     all-HEAD):
     - n = 4, m = 9, sets [[0,1,5,7],[3,4,6,7],[0,2,5,7],[8,6,7,3]], values [[26,3,25,27],[19,17,25,30],[9,14,7,29],[14,11,1,7]],
       order (0, 1, 2, 3), picks (7, 6, 2, 8);
     - D = {0}; agents 1 and 2 want 7; agent 3 is unfrozen and values junk 3.
   - D1-H2 still holds at S2-X: the canonical chain (0, 2) repairs, because the extra agent supplies a slot. It also
     holds at all 76 such starts of k4-d1's probe.
   - S1 (exactly two wanters) has no counterexample in 4,159 climbed starts.
   - Smallest test: S2-X.
2. **D1 for t ≥ 2** (`proof/k4-d1`).
   - Statement: D1-H2 at all-HEAD starts whose longest canonical chain has t ≥ 2.
   - Test set: 456 starts in k4-d1's data; in 449 of them a middle agent is a free slot after the chain.
   - Next: an SMT check of the four-agent core (k, x, z, w).
   - Smallest test (k4-d1's data): n = 4, m = 7, sets [[1,2,4,5],[2,4],[0,3,4,5],[2,5,6]], values
     [[26,29,24,25],[20,29],[22,17,30,23],[29,21,25]], order (2, 1, 0, 3), picks (1, 2, 4, 6), k = 2, chains (2, 1, 0) and
     (2, 1, 3). It is not a core, since agent 1 values two goods. A strict-core example is expected from the SMT run.
3. **R2-M** (TTC session).
   - Statement: at a hard perfect start with at least two receivers, some canonical chain from a dangerous agent to a
     receiver meets Lemma M^c's (C1)–(C3), with owner x₀ and |J′ ∖ H| ≤ 1.
   - Smallest test (this note's data, `k4/oc1_hall/r2_smallest.py`, `r2_smallest.log`): c4-pareto-moves-n3m6.
     Sets [[0,1,2,3],[0,1,4,5],[2,3,4,5]], values [[8,6,4,1],[4,2,8,5],[4,6,8,3]], order (0, 2, 1), picks (0, 5, 4),
     D = {2}, receivers {0, 1}, |J| = 3, which matches Lemma R2-0's bound.
   - At n = 4 the smallest is Q2, picks (3, 7, 5, 4).
4. **The second move** (coordinator's split, 00:51). Two cases:

   **4a. A disjoint second repair (ROUND form).**
   - Statement: at a hard perfect start with no one-move repair whose conflicts split into independent parts, the
     parts are settled by vertex-disjoint moves, each a one-move repair of its part, in one round or in sequence.
   - Smallest test: 5_pure#164 (n = 5):
     - agents 0 and 1 must swap, and separately agent 3, whose pick is worth 2, must be upgraded from agent 4 or 2;
     - the chains (2, 3) and (1, 0) repair it;
     - no single chain or ring can.
   - This case should reduce to the one-move theory applied twice. What has to be proved is that the two parts do not
     interact: the second repair's completion must still satisfy the first part.
   - A failed construction, to avoid: gluing two copies at a junk good gives a sink, not three conflicts.
   - Owner: unassigned. Natural owner: `proof/kgen-rounds` (ROUND⁺).

   **4b. A genuinely sequential second move (OC2-REC).**
   - Statement: the second move uses the first one's result. Some dangerous k has a canonical chain P₁ to the receiver z
     with a shared pool pair T. The reduced state is a perfect SD start of I − k − T and has a one-move repair whose
     completion does not threaten k. Lemma LIFT (refereed) lifts it back.
   - Smallest test: 4_n4_3#58 (n = 4).
   - At n = 4 this case is closed twice over: by LIFT-SHAPE⁺ (K4.MATCH.LIFT.N4), and by **OC₁′^max**, whose single
     wider move repairs every n = 4 start (two independent checks of all 112,880 exported starts).
   - At n = 5, 5_pure#164 refutes LIFT-SHAPE⁺ (`liftshape_n5_check.py`) and OC₁′^max (K4.SDC.OC1PMAX, `k4/sdc.md` §31).
     It is a 4a case, though, so it does not refute OC2-REC.
   - Owners: `proof/k4-oc1max-multi` (OC2-REC); the matching session's exhaustive test.
   - **n = 4 closed for both 4a and 4b** (matching, `k4/matching/n5_census.py`,
     `results/k4_matching/n5_census_n4export.log` at cafae70; ledger K4.MATCH.REC.N4, CERTIFIED by them). Of the
     112,880 n = 4 starts with no one-move repair:
     - 99,840 are 4a-type (some repairing pair of chains from dangerous agents is vertex-disjoint);
     - 13,040 are 4b-type (none is);
     - OC2-REC holds on all of them, with witnesses re-verified by a self-contained checker, and every reduced repair
       is a Lemma EX\* exchange.

     So OC2-REC covers 4a as well at n = 4. The split matters only from n = 5 on.
5. **SLOT** (`proof/k4-oc1max-multi`).
   - Statement: either |D_T| ≥ 2, or D_T = ∅ with DEMAND from a second dangerous agent that values Y_z. Then some
     canonical chain from some k ∈ D leaves demands that fit Lemma M's count at B′, with owner k.
   - Smallest tests: induct-q4-rules (n = 3, m = 5) and hall-local3 (n = 3, m = 7).
6. **RING** (`proof/k4-oc1max-multi`).
   - Statement: if no canonical chain repairs, some ED chain repairs with owner k. In it, either the head is a dangerous
     agent d with Y_d ∈ H₀, or an unfrozen head takes junk.
   - Smallest test: T3 with order (0, 2, 1). Among the 18 starts without a compensated wanter, the smallest is Q2 with
     picks (3, 7, 5, 4).
7. **KEEP-C** (`proof/k4-oc1max-multi`).
   - Statement: if D_T = {k} and no KEEP or OWN chain exists, some canonical chain from k repairs with owner k.
   - Smallest test: n4_4#1715.0 (n = 5, m = 8).
8. **Existence** (`proof/k4-oc1max-multi`).
   - Statement: a hard start has a KEEP, OWN or clean chain, or else is in the SLOT or RING configuration.
   - The data show this in every start: the lemmas of 4a–4e assume a chain with the named property, and one is found
     each time.
9. **No third move** (compute/k4-oc1max-cert).
   - Statement: OC₂^max beyond n = 5.
   - No instance needing three moves is known. The search for three sharers of one pool pair is running.

For TARGET₄ only n ≥ 6 cores matter (scope remark at the top). Every item is stated for all n.

### 23.3 The single sub-lemma the second move needs

`k4/oc1_hall/oc2_cases.py`, `oc2_cases.log`. The instances are:
- the certifier's 11 n = 4 cores (`results/k4_oc1_hall/oc1max_cex_n4_from_cert.json`, copied from
  `compute/k4-oc1max-cert`);
- the TTC session's n = 5 strict core.

That is 12 instances; the coordinator's cex2 is 4_n4_3#77, so the log has 13 rows.

- **Every one has a shared pool danger set**: two dangerous agents k ≠ k′ and an unfrozen z such that a minimal
  improving set of k inside J ∪ B_z is also improving for k′ (§22's mechanism; DEMAND in Lemma D-red's terms). 12 of
  12.
- **Every one is repaired by a canonical first chain from a dangerous agent, followed by one official move**: 12 of
  12. The second move starts at a DEMAND agent in only 6 of the 12 instances. In the rest it starts at another
  dangerous agent (in cex1, the inert agent 0), at a frozen non-dangerous agent, or at an unfrozen agent. So the
  literal form "the remaining DEMAND agent has a canonical chain with exchange deficiency ≤ s" fails on 6 of 12.
- What every instance does have: a repair in which **the second move removes every DEMAND agent of the first chain**,
  either by starting at it or by unfreezing it, since it lifts every wanter of its good. 12 of 12.

> **Sub-lemma OC2-LIFT (K4.OCH.LIFT, open).** Let Y be a one-absorber-hard perfect start (k ≤ 4, strict) with no
> one-move repair. Then some canonical chain P₁ from a dangerous agent k, with an improving H₀, is followed by an
> official move P₂ such that:
> 1. every DEMAND agent q of P₁ either starts P₂ or is unfrozen after P₂ (P₂ raises every wanter of B_q above it);
> 2. the state after P₂ has a one-absorber completion.
>
> A DEMAND agent of P₁ is a dangerous agent q ≠ k that is frozen after P₁ and threatened by the junk together with
> k's new bundle.

Test instances:

| instance | n, m | D | shared pool danger set (k, k′, T, z) |
|---|---|---|---|
| **4_n4_3#58 (smallest)** | 4, 7 | {0, 2, 3} | (2, 3, {3, 4}, 1) |
| 4_n4_3#77 (= coordinator's cex2) | 4, 7 | {1, 2} | (1, 2, {1, 3}, 0) |
| 4_pure#20, #21 | 4, 7 | {0, 1} | (0, 1, {1, 2}, 3) |
| 4_pure#23 | 4, 7 | {1, 2, 3} | (2, 3, {2, 6}, 0) |
| 4_pure#24 | 4, 7 | {0, 2, 3} | (2, 3, {2, 3}, 1) |
| 4_pure#26 | 4, 7 | {0, 1, 2} | (1, 2, {1, 5}, 3) |
| 4_pure#29 | 4, 7 | {1, 2} | (1, 2, {1, 3}, 0) |
| 4_pure#36 | 4, 7 | {0, 2, 3} | (2, 3, {1, 3}, 1) |
| 4_pure#38, #45 | 4, 8 | {0, 1, 3}, {0, 2, 3} | (1, 3, {4, 5}, 2), (2, 3, {3, 4}, 1) |
| TTC n = 5 core | 5, 9 | {1, 3, 4} | (1, 3, {2, 4}, 0): T contains B_z |

*How the second move lifts, in the smallest case (4_n4_3#58).*
- The first chain is (2, 1): agent 2 takes {3, 4}, and the DEMAND agent is 3. Agent 3's good 6 is wanted by agent 1,
  which now holds 5.
- The second chain is (0, 1): agent 1 takes good 1 (its top), and agent 0 takes {2, 5}.
- Agent 1 no longer wants good 6, so agent 3 is unfrozen and becomes a holder.

The second move therefore works on the *wanters* of the DEMAND agent, not on the agent itself. A proof should pair
Lemma D-red's DEMAND with an unfreezing chain, in the style of Lemma Ωʳ (§4, §8): the chain to the unique unfrozen
agent gives it its top good.
