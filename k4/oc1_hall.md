# A Hall-type count for OC₁ (workstream `proof/k4-oc1-hall`)

Target: Conjecture OC₁ (K4.SDC.OC1, `k4/sdc.md` §29), which implies TARGET₄. For every serial-dictatorship order, the
picks have a one-absorber completion, or after one improving chain the bases have one. Notation is that of
`k4/sdc.md` §30. Y = SD(π), J = junk (unpicked goods), p_i = v_i(Y_i). Agent i *wants* g ∉ B_i if
v_i(g) > v_i(B_i). F = frozen agents (single-good holders whose good someone wants). D ⊆ F = dangerous agents (frozen
agents that value a junk good). W_x = the agents that want x's good.

Code: `k4/oc1_hall/` (`ohlib.py` is shared). Logs: `results/k4_oc1_hall/`. Every check uses the raw EFX₀ definition
(`ohlib.efx0`), and its own enumeration rather than SAT unless stated. Data sets are those of `k4/sdc`:
- special: T3, Q2, r4253, r3943;
- screen: 168 instances;
- suite: 158 instances;
- logs: the 1,534 hard profiles printed in `results/k4_sdc/*.log`, n ≤ 4;
- random strict core profiles: 3,000 with n ≤ 3 (seed 91), 1,500 with n = 4 (seed 92), 150 with n = 5 (seed 93).

Every order is tried, n ≤ 5. Everything called *evidence* is evidence only (PROMPT.md §5 rule 3).

## Status (end of burst 3)

| | statement | status |
|---|---|---|
| Lemma 1 | slot form of the one-absorber completion at SD picks: conditions (S1), (S2) | written proof; agrees with SAT on all 14,461 distinct starts, and with raw brute force on special and screen |
| Lemma 2 | slot count: under (G1), (G2), (G5′), (H3), an S\* completion with owner o exists iff some kept-out set H satisfies (H1) and \|H\| + θ(H) − ν(H) ≤ \|N₁\| | written proof (§4). Check (`lemma2_true_check.log`): H ranges over transversals of the demands only, at the picks and at every post-chain state (n ≤ 4). The count agrees with the raw S\* enumeration on all 248,341 owner tests. The (⇐) construction, with DT's moves actually used in 73,410 cases, is EFX₀ every time |
| Lemma 2\* | the same with (G5′), (H3) dropped: exposed holders that are not movable (they want a good of B_o, or have a danger set inside B_o) must be compensated, i.e. matched to a good of H | written proof (§6); `lemma2star_true_check.log`: 330,992 owner tests (frozen and multi-good owners included), 0 mismatches, DT's moves used in 76,395 |
| Prop. 5 (small ω) | at the picks, if some unfrozen o has ω_o = \|J\| − \|N₁(o)\| ≤ 1, the picks have an S\* completion with owner o; so every hard start has ω_o ≥ 2 for every unfrozen o | written proof (§9); 14,756 owner tests with ω ≤ 1, 0 failures |
| Cor. 2.1, Lemma 4 | (H2) is Hall's condition for a system of distinct admissible holders of H, so C(B, o) = a transversal of the demands with an SDR into the slots; robust helpers always suffice | written proofs (§6) |
| Prop. 3 (T2⁺) | f = 1: if some o ≠ x has v_x((J ∪ {Y_o}) ∩ R_x) ≤ p_x, the picks have an S\* completion with owner o | written proof (§5) |
| **Theorem F1₁** | f = 1, exactly one wanter, n ≥ 3: the picks or one swap x → w have an S\* completion. This covers the open sub-case "x improves only with three goods" of `k4/sdc.md` §30 | written proof (§5); the proof run literally succeeds on all 3,329 such starts |
| Finding S\* | OC₁ holds with the narrower completion S\*: one owner (any agent); one junk good each for single-good holders that are not frozen; nothing for frozen agents and multi-good holders | evidence: 0 failures on 14,461 distinct starts with n ≤ 5 (every order), and on 48,123 distinct starts with n = 6–10 (sampled orders, SAT, §7) |
| Finding B | at every hard start (no S\* completion), some repairing chain starts at a dangerous frozen agent k, and after it k owns: all but 1 of the 2,676 hard starts with n ≤ 5. In that one start (§29's dichotomy instance) the chain end owns. At n = 6–10, every one of the 1,300 hard starts is repaired by a chain after which a dangerous agent that gave its pick away owns | evidence |
| Finding F1 | f = 1: at every hard start, some swap x → w with an *inclusion-minimal* improving set H₀ ⊆ J ∪ {Y_w} repairs with x as owner, also when \|W_x\| = 2 | evidence: all 100 f = 1 hard starts |
| Finding F1W | f = 1, several wanters: hard starts occur only at n = 3 in the data (n − 2 = 1 slot). For n ≥ 4, the picks have an S\* completion with a wanter as owner on 219 of 220 starts | evidence (§5) |
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

Next:
1. f = 1 with several wanters, n ≥ 4: the picks with a wanter as owner (Corollary 2.1, with helpers). One n = 4 start
   (red-b1-blocked-improvement) needs the swap, because x needs two goods kept out and only one admissible holder
   exists.
2. f = 2 (§8): the chain removes both demands, by passing through the other frozen agent or by unfreezing it. A count
   for "after the chain" needs Lemma Ωʳ's unfreezing term inside Corollary 2.1.
3. The chain lemma in general.

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
  - Since Σ_i |R_i| ≥ 2m − (number of private goods) in a core, a hard start with small f needs nearly every agent to
    have four goods.
  - In the data, the least ω over unfrozen owners at the hard starts runs from 2 to 8 (`omega_sstar.log`; e.g. screen
    2: 30, 3: 112, 4: 57, 5: 27, 6: 6, 7: 2).
- **The chain must beat a large excess.** Unlike LB⁺ at k = 3, where the bad case has excess one, one chain here
  must overcome ω up to 8. It does so by moving junk into the chain agents' new bases, H₀ and the H_i, and into k's
  owned bundle, which Lemma 2's count then accepts.

*Check* (`k4/oc1_hall/omega_sstar.py`, `omega_sstar.log`). On every distinct start of every data set, every
unfrozen owner with ω_o ≤ 1 passes the raw S\* enumeration: 14,756 owner tests, 0 failures.
