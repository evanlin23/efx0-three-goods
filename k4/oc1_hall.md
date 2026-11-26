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

## Status (end of burst 2)

| | statement | status |
|---|---|---|
| Lemma 1 | slot form of the one-absorber completion at SD picks: conditions (S1), (S2) | written proof; agrees with SAT on all 14,461 distinct starts, and with raw brute force on special and screen |
| Lemma 2 | slot count: under (G1), (G2), (G5′), (H3), an S\* completion with owner o exists iff some kept-out set H satisfies (H1) and \|H\| + θ(H) − ν(H) ≤ \|N₁\| | written proof (§4); the count agrees with the raw S\* enumeration on 31,459 owner tests; the (⇐) construction, run literally, is EFX₀ in all 312,502 cases (picks and post-chain states) |
| Prop. 3 (T2⁺) | f = 1: if some o ≠ x has v_x((J ∪ {Y_o}) ∩ R_x) ≤ p_x, the picks have an S\* completion with owner o | written proof (§5) |
| **Theorem F1₁** | f = 1, exactly one wanter, n ≥ 3: the picks or one swap x → w have an S\* completion. This covers the open sub-case "x improves only with three goods" of `k4/sdc.md` §30 | written proof (§5); the proof run literally succeeds on all 3,329 such starts |
| Finding S\* | OC₁ holds with the narrower completion S\*: one owner (any agent); one junk good each for single-good holders that are not frozen; nothing for frozen agents and multi-good holders | evidence: 0 failures on 14,461 distinct starts |
| Finding B | at every hard start (no S\* completion), some repairing chain starts at a dangerous frozen agent k, and after it k owns: all but 1 of the 2,676 hard starts. In that one start (§29's dichotomy instance) the chain end owns | evidence |
| Finding F1 | f = 1: at every hard start, some swap x → w with an *inclusion-minimal* improving set H₀ ⊆ J ∪ {Y_w} repairs with x as owner, also when \|W_x\| = 2 | evidence: all 100 f = 1 hard starts |
| Finding F1W | f = 1, several wanters: hard starts occur only at n = 3 in the data (n − 2 = 1 slot). For n ≥ 4, the picks have an S\* completion with a wanter as owner on 219 of 220 starts | evidence (§5) |
| refuted | the GDT shape (frozen agents take nothing, owner unfrozen) is too narrow for OC₁: 9 distinct screen starts have no repair in it | `oc1_shapes_screen.log` |
| refuted | canonical chains only (each middle agent wants its predecessor's pick, no middle junk): 15 of 234 screen hard starts have no canonical repair (e.g. adaptive-p1, where the middle agent gains only with a junk good) | `greedy_rules.log` |

**Scope remark.** OC₁ is used for TARGET₄ only on cores, and k = 4 cores with n ≤ 5 are certified already (ledger
K4.R5c, K4.R5d, K4.R5p). So a proof of OC₁ for n ≥ 6 implies TARGET₄, and the exceptions at n = 2, 3 (where only a
frozen owner works, §5) do not matter for TARGET₄. The data, however, all have n ≤ 5.

Next:
1. f = 1 with several wanters, n ≥ 4: the picks with a wanter as owner (Lemma 2).
2. A Theorem A₄-type count tracing the deficit to one dangerous agent.
3. The chain lemma: k owns (Theorem B form), or the end owns (Theorem B₄ form).

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
- Middle junk is needed on 17 screen starts (canonical 217 of 234).

**f = 1** (`k4/oc1_hall/f1_study.py`, `f1_study.log`). Exactly one frozen agent x. Its wanters W hold their second
goods, and every other agent holds its top. On every f = 1 hard start:
- 13 + 2 screen, 13 + 2 suite, 17 + 3 logs, 46 + 2 random n ≤ 3, 2 random n = 4 (|W| = 1 + |W| = 2), 100 in all;
  none among the special instances or the random n = 5 profiles;
- some swap x → w (w takes Y_x; x takes an inclusion-minimal set H₀ ⊆ (J ∪ {Y_w}) ∩ R_x with v_x(H₀) > p_x; Y_w ∖ H₀
  becomes junk) has an S\* completion with owner x;
- "every minimal H₀, owner x" fails on 5 of them (2 logs, 2 random n ≤ 3, 1 random n = 4).

This covers the two open sub-cases of `k4/sdc.md` §30: several wanters, and three-good improvements.

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
3. *Exactness on data* (`k4/oc1_hall/deficit_check.py`, `deficit_check.log`). The *deficit* of o is
   min over H with (H1) of |H| + θ(H) − ν(H) − |N₁|, computed by `ohlib.deficit`. Over every unfrozen owner of every
   distinct start of every data set (31,459 tests): deficit ≤ 0 iff the raw S\* enumeration
   `ohlib.shaped_completion` succeeds (0 mismatches).
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

**Lemma 2's construction, run literally** (`k4/oc1_hall/lemma2_check.py`, `lemma2_check.log`). At every state
reached (picks, and every state one improving chain reaches) and every owner o:
- whenever (G1), (G2), (G5′), (H3) hold and the least count of `ohlib.deficit` is at most |N₁|, `ohlib.lemma2_build`
  is run and its output checked: 312,502 constructions, all EFX₀, all keeping the bases, 0 failures.
