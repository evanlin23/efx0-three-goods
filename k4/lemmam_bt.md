# Lemma M by the big-top induction: two counterexamples

Workstream `proof/k4-lemmam-bt`. Target: **Lemma M** of `k4/rulef.md` (PR #72, row K4.RF.M): for every strict profile
of every k = 4 core some first agent a is in class K0 or K1 of rule RK (Lemma K certifies the run of τ_a = (a, then
index order) without rotation, or after one rotation). The brief asked for a proof along the big-top programme of
`k4/rulef.md` §6: (a) with exactly one big-top agent q, the run of τ_q satisfies M1 (|σ_F| ≤ κ₀) or Lemma KR's
hypotheses; (b) with several, some big-top agent works; (c) with none, some agent sharing its top works. Notation as in
`k4/lb4.md`, `k4/c4.md` and `k4/rulef.md`; H_t is the core of `k4/c4.md` §7.

**Status** (rows K4.LMBT.*; written proofs here are not yet refereed).
- **Step (a) is false** (Proposition Q, §2): on H_3 plus one big-top agent q whose top is private (n = 14, m = 34, a
  connected k = 4 core with a strict profile and exactly one big-top agent), LB₄ʳ(τ_q) has no output with at most one
  rotation under any upgrade policy. So q is in neither K0 nor K1. Rule RK takes a gadget-1 agent there, in K0.
- **Lemma M is false** (Proposition HH, §3): on HH_3, two copies of H_3 sharing one good (n = 26, m = 65, a connected
  k = 4 core with a strict profile, every agent with four goods, none big-top), **no first agent works with at most one
  rotation**: for every a, LB₄ʳ(τ_a) has no output with at most one rotation, under every upgrade policy, every owner,
  the owner's needs from its base or its bundle. Hence no first agent is in K0 or K1 (Lemma K's certificates are
  outputs), so Lemma M fails, and so do rule F with one rotation (K4.AD.F) and the Lean hypotheses
  `EFX.LB4R.TheoremRuleF` and `EFX.LB4R.RuleFConn` (K4.RF.LEAN: their implications stay proved, their hypothesis is
  false at every instance size that holds HH_3). HH_3 satisfies K4.D: two adaptive insertion steps (a gadget-1 agent of
  each copy) need no rotation.
- Both proofs are Proposition H's count (`k4/c4.md` §7, K4.C4.R, PROVED) with one more ingredient: in HH_t every first
  agent leaves one copy to index order, and the copy that holds the first agent gives back at most one slot place.
- **Computations** (§4): Lemma K's classes of every first agent on HH_3 by two implementations (`k4/lemmam_bt.py`,
  written from the text of `k4/rulef.md` §2 on PR #33's model; `k4/rulef.c` of PR #72); LB₄ʳ with at most one rotation
  exactly, by PR #33's two independent encodings of Lean's `Output` (`k4/c4_verify_H/lb4r.py`, `enc_b.py`).
- What it means for the route (§5): a rule that chooses only the first agent needs at least (t − 1)/2 rotations on
  HH_t (Corollary HH), so no fixed rotation bound saves it; we expect the same for any fixed number of chosen insertion
  steps (several copies of H_t; not proved).
  The insertion agent has to be chosen adaptively at every insertion step, as LB₄'s search over insertion sequences
  does.

## 1. The count of Proposition H, as a lemma

Let P′ be a valid pre-allocation and X a completion with owner o that satisfies (OC₄) (in Lean's `Output` the
owner's needs come from its bundle, so frozen status is computed with N_o^X; with the needs from the base it is the
same argument). Write J for the junk of P′. A free agent x ≠ o (free in X) receives at most 2 − |B_x| junk goods,
*its slot places*; a frozen agent receives none; and every good of J ∖ X_o lies in a slot place of some agent ≠ o.

**Lemma P (protecting goods).** Let F′ be a set of agents other than o, and for each f ∈ F′ let Π(f), Σ(f) ⊆ J be such
that in X some good of Π(f) is outside X_o, or some good of Σ(f) lies in f's own slot place. Suppose the sets Π(f) are
pairwise disjoint except for c goods, each in exactly two of them, and Σ(f) ∩ Π(f′) = ∅ for all f, f′. Then
|F′| ≤ S_X + c, where S_X is the number of slot places of the agents other than o that are free in X.

*Proof.* Assign to f a good of Π(f) outside X_o if there is one, else a good of Σ(f) in f's own slot place. The
assigned goods lie in J ∖ X_o, so in distinct slot places, and two agents get the same good only if it is one of the c
shared goods of the Π's (a good of Σ(f) sits in f's own place and is in no Π(f′), and different agents' own places are
different). So |F′| − c ≤ |J ∖ X_o| ≤ S_X. ∎

We call f *forced* with (Π(f), Σ(f)). Proposition H's proof (`k4/c4.md` §7) is this lemma with c = 0 and the following
forced agents of H_t; we use them as they are.
- (F1) x_{j,i} holding exactly {a_{j,i}} (plus a slot good if free), with b_{j,i}, c_{j,i} ∈ J: forced with
  Π = {b_{j,i}, c_{j,i}}, Σ = {g_j} ∩ J. (If b, c ∈ X_o and x's slot does not hold g_j, x holds a bundle worth 8. If
  X_o ⊄ R_x, removing a good outside R_x leaves at least 6 + 4. If X_o ⊆ R_x, then B_o ⊆ R_x is disjoint from J and
  from x's base, so B_o ⊆ {g_j}, B_o is not empty in any state reached below, and X_o = {g_j, b, c}: removing g_j
  leaves 10 > 8.)
- (F2) ℓ holding {g_1} with u, u′ ∈ J: forced with Π = {u, u′}, Σ = {z} ∩ J (the same argument: 9 > 8, or B_o = {z}
  and X_o = {z, u, u′}).

Proposition H bounds, for every state reached from H_t's index run with q rotations and every completion, the
*balance* of each group of agents, (slot places of its agents other than o, free in X) − (its forced agents):
ℓ at most 0, an untouched gadget exactly −2, a touched gadget at most +1 (`k4/c4.md` §7, "Counting"; the owner's needs
from its bundle are covered there). An untouched gadget j is one whose agents hold their index-run bases: y_j holds
e_j, each x_{j,i} holds {a_{j,i}}, frozen.

## 2. Proposition Q: a single big-top agent first can need two rotations

**The core H_t + q.** Add to H_t (agents in H_t's index order) an agent q with the last index, R_q = {p, b_{1,1},
c_{1,1}, u}, values (8, 4, 3, 2), p a new good. q is big-top (8 > 4 + 3) and strictly balanced (8 < 9); p is its only
private good; x_{1,1} and ℓ now share goods with q (fewer private goods, which the core conditions allow). It is a
connected k = 4 core with a strict profile
(`k4/check4.py`'s `is_core` and type domains; `k4/lemmam_bt_hh.py core Hq3`), and q is its only big-top agent (ℓ, the
x's and the y's have a = 8 < 6 + 4 or 6 + 5).

**Proposition Q.** For t ≥ 3, on H_t + q, LB₄ʳ(τ_q) has no output with at most one rotation, under each of the three
upgrade policies, every owner (or none), the owner's needs from its base or its bundle. In particular q is in neither
class K0 nor class K1, and step (a) of `k4/rulef.md` §6 is false.

*Proof.* *Phase 1.* q is inserted first and takes p; nobody else values p, so no agent has lost a good, and the next
insertion step takes ℓ (index 0). From there the run is H_t's index run (`k4/c4.md` §7, Proposition H, "Phase 1"):
nobody else values the goods q took. *Upgrades:* q needs nothing, and H_t's agents admit none (Proposition H). So the
state is H_t's index-run state plus q holding {p}. *Rotations:* q is never frozen (nobody values p) and never a chain
end (it needs nothing), so every RotStep is one of H_t's and touches one gadget. *Owner:* ω = |NA| − σ with
σ = 2n − m = 2(4t + 2) − (10t + 4) = −2t, so ω ≥ 1 and an owner is required (`Output`; a base of three or more goods
forces its agent to be the owner anyway).
*Count.* Take a completion X with owner o satisfying (OC₄) of a state reached with at most one rotation. Let F′ be the
forced agents of H_t's groups (F1, F2): their Π's are disjoint (b, c are x's goods, u, u′ ℓ's; q values b_{1,1}, c_{1,1},
u, but q is not in F′, so c = 0). The argument of (F1), (F2) is unchanged: a base B_o ⊆ R_x or ⊆ R_ℓ is never q's {p}.
The balance of H_t's agents is at most −2(t − 1) + 1 = −2t + 3 (Proposition H; at least t − 1 gadgets untouched), and q
adds at most one slot place. By Lemma P, 0 ≤ S_X − |F′| ≤ −2t + 4 < 0 for t ≥ 3. ∎

Lemma K's certificates are completions of this kind (`k4/rulef.md` §2), so q ∉ K0 ∪ K1. The data agree: Lemma K's
least deficit at q's run is 5 under each policy and at least 2 after every single rotation, and `k4/rulef.c` puts q in no
class, while rule RK takes agent 1 (x_{1,1}) in K0 (§4). On H_2 + q the count allows one rotation. So the
data of `k4/rulef.md` §5.2 ("with exactly one big-top agent, that agent is in K0 or K1", n ≤ 4) do not extend: q's
insertion changes nothing in the part of the core that decides the run.

## 3. Proposition HH: no first agent works with one rotation

**The core HH_t.** Take two copies A and B of H_t (agents ℓ_A, x^A_{j,i}, y^A_j and ℓ_B, x^B_{j,i}, y^B_j; goods
likewise) and identify ℓ_B's good u^B with ℓ_A's good u^A =: u. Agents in index order: ℓ_A, ℓ_B, A's gadget agents in
H_t's order, B's gadget agents in H_t's order. Values as in H_t. Each ℓ keeps one private good (u′), each x two (b, c),
and every agent has four goods with a = 8 < 6 + 4 or 6 + 5 (none big-top). n = 8t + 2, m = 20t + 5; for t = 3, n = 26,
m = 65. HH_t is a connected k = 4 core with a strict profile (`k4/lemmam_bt_hh.py core HH3`).

**Proposition HH.** For t ≥ 3 and every agent a of HH_t, LB₄ʳ(τ_a), τ_a = (a, then index order), has no output with at
most one rotation, under each of the three upgrade policies, every owner (or none), the owner's needs from its base or
its bundle, and chains ending at any agent that is not frozen. Hence no first agent is in K0 or K1, Lemma M fails on
HH_3, and so does rule F with at most one rotation.

Fix a. Let D be the copy containing a and C the other one.

**Lemma 1 (Phase 1).** (i) Each ℓ picks its g_1, so u is never picked; each x picks its a or its b; every agent gets a
pick. (ii) The agents of C are processed exactly as in H_t's index run: ℓ_C first, at an insertion step, then the rest
of C by P-steps, with ℓ_C, x, y picking g_1, a, e. (iii) In D, with j the gadget of a (j = 0 if a = ℓ_D):
- gadgets k < j: (α) y_k holds e_k, each x_{k,i} holds a_{k,i} (if j = 0, every gadget);
- gadget j: (β1) if a ∈ {x_{j,2}, x_{j,3}, y_j}: y_j holds a_{j,1}, x_{j,1} holds b_{j,1}, x_{j,2}, x_{j,3} hold their a's;
  (β2) if a = x_{j,1}: y_j holds a_{j,2}, x_{j,2} holds b_{j,2}, x_{j,1}, x_{j,3} hold their a's;
- gadgets k > j: (β2).

*Proof.* (i) An x takes its g_j only if its a, b and c are gone; b and c are its private goods and it picks one good,
so it never takes g_j, and ℓ finds g_1 available. An x finds b available; a y finds e_j available unless it took it.
(ii) The agents of C value only goods of C and u. Before the first agent of C is processed, no good of C has been
picked and u never is, so no agent of C has lost a good, and the first one is processed at an insertion step, as the
unprocessed agent of least index; ℓ_C has the least index in C, so it is ℓ_C. Afterwards, by induction, the agents of C
processed so far and their picks are a prefix of H_t's index run: an agent outside C changes no good of C, the P-step
key of an agent of C depends only on goods of C, ties among C's agents are broken by their relative index order, which
is H_t's, and while an agent of C is unprocessed some agent of C has lost a good (H_t's index run has no insertion step
after ℓ), so no insertion step intervenes.
(iii) P-step keys are (rank of the favourite remaining good, goods left, index). If a = y_j: it takes a_{j,1}; only
x_{j,1} has lost a good and it takes b_{j,1}. If a = x_{j,2} (or x_{j,3}): it takes its a; y_j (key (0, 3)) takes a_{j,1};
x_{j,1} takes b_{j,1}. If a = x_{j,1}: it takes a_{j,1}; y_j (key (1, 3)) takes a_{j,2}; x_{j,2} takes b_{j,2}. In each case
the block ends there. The next insertion steps take ℓ_A, then ℓ_B (indices 0, 1; a block of C is (ii)). When ℓ_D takes
g_1, the x's of gadget 1 that are unprocessed have lost g_1 (key (0, 3)) and take their a's before y_1 (key (1, 3) once
a_{1,1} is gone), which then takes e_1 = g_2, and so on: gadgets 1, …, j − 1 end in (α), and the unprocessed x's of gadget
j take their a's when g_j goes. y_j holds an a, so e_j = g_{j+1} stays junk and the cascade stops. Each later gadget k is
reached by an insertion step at x_{k,1} (its least index), which takes a_{k,1}; y_k (key (1, 3); the other x's have lost
nothing, g_k being junk) takes a_{k,2}; x_{k,2} takes b_{k,2}; then x_{k,3} is inserted and takes a_{k,3}: (β2). ∎

**Lemma 2 (upgrades).** C admits no upgrade under any policy (Proposition H). In D:
- no upgrades and envy-free upgrades give the Phase 1 state (an x holding b has {b, c} worth 10 < a + g = 11 and
  {b, g} worth 9 < 12, so no envy-free pair; a y holding a_{k,1} needs nothing; a y holding a_{k,2} holds a needed good;
  a y holding e_k has no junk good; ℓ and the x's holding a need nothing);
- need-shrinking upgrades: every x holding b takes c ({b, c} is worth 10 > 8, and c beats g), and then every y of a
  (β2) gadget takes e ({a_2, e} worth 9 > 8). At the fixpoint a (β1) gadget has x_1 on {b_1, c_1} and y on {a_1},
  free, with no needs; a (β2) gadget has x_2 on {b_2, c_2}, y on {a_2, e}, and x_1, x_3 on their a's, nobody frozen;
  (α) gadgets are unchanged.

(Lemmas 1 and 2 checked on HH_3 and HH_4, every first agent and every policy, against PR #33's model of Phase 1 and the
upgrades: `k4/lemmam_bt_hh.py lemmas`, `results/k4_lemmam_bt/lemmas.log`, 0 mismatches.)

**Lemma 3 (rotations).** Needs stay in gadgets: an x needs at most its a, a y only a's of its gadget, ℓ nothing (it
holds its top). So every need chain lies in one gadget, ℓ_A and ℓ_B are never on a chain, and one RotStep touches one
gadget, of C or of D.

*Proof of Proposition HH.* ω = |NA| − σ with σ = 2n − m = −4t − 1, so ω ≥ 1 and an owner is required. Take a state
P′ reached with at most one rotation and a completion X with owner o satisfying (OC₄). Let F′ consist of the forced
agents of C (Proposition H's lists, (F1), (F2) for ℓ_C), the agents of D holding exactly their a, with b, c junk ((F1)),
and ℓ_D ((F2)). The Π's are disjoint except u ∈ Π(ℓ_A) ∩ Π(ℓ_B): c = 1. The arguments of (F1), (F2) hold in HH_t:
X_o may contain goods of the other copy, which only puts X_o outside R_x, and a base inside R_x (or R_ℓ) is g_j (or z).
By Lemma P, the balance of all agents is at least −1. We show it is at most −2.

*Balance of C.* By Proposition H (C's states are H_t's), at most −2t if the rotation is not in C and at most −2t + 3 if
it is.

*Balance of D, no rotation in D: at most 1.* Count each agent: a free agent with a one-good base gives at most 1 (at
most 0 if forced), a frozen agent 0 (−1 if forced), a two-good base 0, the owner 0 (it is free in P′, since the others'
needs are unchanged, and it is not forced). ℓ_D gives at most 0. By Lemmas 1, 2:
- (α): y_k at most +1, its three x's frozen and forced: −2.
- (β1), no upgrades or envy-free: y_j frozen (x_{j,1} needs a_{j,1}), x_{j,1} at most +1, x_{j,2}, x_{j,3} free and forced
  (y_j needs nothing): at most +1. Need-shrinking: x_{j,1} 0, y_j at most +1, the others 0: at most +1.
- (β2), no upgrades or envy-free: y frozen (x_2 needs a_2), x_2 at most +1, x_1 frozen and forced (y needs a_1), x_3
  free and forced: at most 0. Need-shrinking: x_2, y on two goods, x_1, x_3 free and forced: 0.
The owner's needs from its bundle unfreeze an agent only if the owner needed its pick and no longer does: in D only an
owner x holding b with c in its bundle (10 > 8), which frees y; in (β1) the gadget is then x_{j,1} 0, y at most +1, the
others 0, and in (β2) x_2 0, y at most +1, x_1 −1, x_3 0; the bounds stand. (An owner y in (α) keeps needing its a's: its
bundle meets R_y only in e.) With gadget j at most +1, gadgets k > j at most 0 and gadgets k < j at −2, the balance of D
is at most 1.

*A rotation in D touches one gadget, which then has balance at most +1.* The frozen agents of D are the x's of (α)
gadgets, and, without need-shrinking upgrades, y in (β1) and (β2) and x_1 in (β2); after need-shrinking upgrades (β)
gadgets have none. The chains and bases O (O ⊆ R_k ∩ (J ∪ B_end), valid only if the head's value-based needs avoid J):
- (α), x_{k,i} → y_k: O ⊆ {b, c, g_k} ∩ J (e_k ∉ R_x), valid O ∈ {{b}, {b, c}, {b, g}, {b, c, g}}. y_k now holds a_{k,i}
  and needs the a's above it. For i = 1: x_2, x_3 free and forced 0, y at most +1 if x_1's base has two or more goods
  (x_1 then 0) and frozen otherwise (x_1 on {b} at most +1): at most +1. For i = 2, 3: x_1 (and x_2) frozen and forced,
  so at most 0 and −1. (This is Proposition H's touched gadget.)
- (β1), y → x_1: x_1 takes a_1, y takes O ⊆ R_y ∩ J = {e}, so y needs all three a's: x's frozen and forced (−3), y at most
  +1 (a one-good base O has a slot place in Lean's `Output`): −2.
- (β2), x_1 → y → x_2: x_2 takes a_2 (b_2 returns to J, so x_2 is forced), y takes a_1, x_1 takes a valid
  O ∈ {{b_1}, {b_1, c_1}, {b_1, g}, {b_1, c_1, g}}: y frozen and x_1 at most +1 if O = {b_1}, else x_1 0 (or the owner)
  and y at most +1; x_2, x_3 free and forced: at most +1. (β2), y → x_2: y takes {e} and needs every a: −2.
An owner among these agents changes nothing (an owner x_1 on {b_1} with c_1 in its bundle frees y, and the gadget stays at
most +1). So with a rotation in D, D's balance is at most 2: the touched gadget at most +1, gadget j at most +1, the
others at most 0.

*Total.* Rotation in C: at most (−2t + 3) + 1 = −2t + 4. Rotation in D: at most −2t + 2. No rotation: at most −2t + 1.
For t ≥ 3 each is at most −2 < −1, so no such completion exists. Every output of LB₄ʳ is such a completion with an
owner (or none, excluded by ω ≥ 1 when every base has at most two goods; a base of three or more goods makes its agent
the owner), so LB₄ʳ(τ_a) has no output with at most one rotation. ∎

**Corollary HH (rotations grow with t).** For every first agent a of HH_t, LB₄ʳ(τ_a) has no output with fewer than
(t − 1)/2 rotations (nested RotSteps, every policy, every owner). So no fixed bound on the rotations makes "one chosen
first agent, then index order" work.

*Proof.* Needs stay in gadgets in every state reached by any number of rotations: an x's goods are worth at least 3 and
its base is never empty, so it never needs g_j (worth 3), and its other goods are in its gadget; likewise a y never needs
e_j, and ℓ_A, ℓ_B keep g_1 and need nothing (nobody ever needs g_1). So every RotStep touches one gadget, bases stay
nonempty (chain agents take picks, the head a nonempty O), and each agent has at most one slot place. With R_C rotations
touching C and R_D touching D: C's balance is at most −2t + 3R_C (Proposition H holds for any number of rotations:
untouched −2, touched at most +1, ℓ at most 0); in D the untouched gadgets keep the bounds of the proof above (at most
+1 for the gadget of a, at most 0 or −2 for the others), ℓ_D gives 0, and a touched gadget at most 4 (four agents, at
most one slot place each). Lemma P with c = 1 needs −2t + 3R_C + 1 + 4R_D ≥ −1, so 3R_C + 4R_D ≥ 2t − 2 and
R_C + R_D ≥ (t − 1)/2. ∎

All rotations in C (the copy left to index order) would need R_C ≥ (2t − 2)/3; with the bound "a touched gadget of D
has balance at most +1", which holds for one rotation (proof above) but is not shown for several, the same bound
(2t − 2)/3 would hold in general. This is the count that matters for a rule with a rotation budget: the copy left to
index order is a single block of Phase 1 (ℓ's insertion and then P-steps only), and it needs about 2t/3 rotations. A rule
that chooses the inserted agent at every insertion step avoids that block on HH_t altogether (two choices, no rotation,
below); HH_t does not decide whether such a rule can always keep one rotation per block.

*K4.D holds on HH_3.* The insertion sequence (x^A_{1,2}, x^B_{1,2}, then index order) runs both copies as in Lemma 1(iii)
with j = 1, and its state has an `Output` without rotation (`k4/lemmam_bt_hh.py d2 HH3`, checked against the raw EFX₀
definition): what fails is the restriction to one chosen insertion step.

## 4. Computations

All on one worker; `k4/lemmam_bt_hh.py` (instances, drivers), `k4/lemmam_bt.py` (Lemma K on PR #33's model).
- `core`: HH_3 and H_3 + q are connected k = 4 cores, every type a strict balanced core type; HH_3 has no big-top
  agent, H_3 + q exactly one (q).
- `classes`, H_3 + q and HH_3 (this file's Lemma K, Remark 4's kept-out sets included, every policy of LB₄ʳ): on HH_3,
  for every first agent and policy, Lemma K's least deficit at the Phase 1 + upgrade state is at least 4 and after every
  single RotStep at least 1 (the least values, 4 and 1, at the first agents x_{1,2}, x_{1,3}, y_1 of either copy: 6 for
  the copy left to index order, minus 1 for the other copy, minus 1 for the shared u, then minus 3 for the best
  rotation, exactly the count of §3); the least deficits are equal under the three policies, and C₄⁰'s hypothesis fails
  at every first agent (ω ≥ 1 and 4-good agents exposed). So none of the 26 first agents is in K0 or K1, also for RK₃
  (`results/k4_lemmam_bt/classes_HH3.log`). On H_3 + q, q: least deficit 5, at least 2 after each of the 18 RotSteps
  (`classes_Hq3.log`).
- `rk`, H_3 + q (`k4/rulef.c` of PR #72, LB₄ʳ's own owner search skipped): the first big-top agent (`-A42 -Q0`) is q,
  in no class; rule RK (`-A41`) takes agent 1 in K0 (`results/k4_lemmam_bt/rk_Hq3.log`).
- `rkall`, HH_3 (`k4/rulef.c -A41 -E1 -Y1 -N1`, one first agent per run, LB₄ʳ's owner search skipped):
  `results/k4_lemmam_bt/rk_HH3.log` (running, one worker; it follows the exact checks).
- `exact`, encodings A (`k4/c4_verify_H/lb4r.py`, SAT) and B (`k4/c4_verify_H/enc_b.py`, MILP), Lean's `Output` with
  the owner's needs from its bundle, every owner and none, every state of the three policies and every state one
  RotStep away: H_3 + q, first agent q: 19 states, no output (`exactA_Hq3.log`; B: `exactB_Hq3.log`). HH_3, every first
  agent (37 to 100 states each): `exactA_HH3.log`, `exactB_HH3.log` (running, one worker, about 3 minutes per first
  agent and encoding).
- `d2`, HH_3: the insertion sequence (x^A_{1,2}, x^B_{1,2}) = agents (3, 15), need-shrinking upgrades, owner ℓ_A: an
  `Output` without rotation, EFX₀ by the raw definition, one bundle above two goods (`d2_HH3.log`). The suite records
  `k4/suite/instances/lmbt-HH3.json` and `lmbt-Hq3.json` carry these witnesses (H_3 + q: rule RK's sequence, x_{1,1}
  first).

## 5. What this means for the route

- Lemma M, rule F with one rotation (K4.AD.F), `TheoremRuleF` and `RuleFConn` are false. Their implications in Lean
  (K4.RF.LEAN) stay proved, with a false hypothesis at every instance size that holds HH_3 (n ≥ 26, m ≥ 65).
- With R rotations rule F still fails on HH_t once t > 2R + 1 (Corollary HH): a single chosen first agent needs a
  number of rotations that grows linearly with the core. We expect the same for any fixed number L of chosen insertion
  steps (not proved, not checked by computation): L + 1 copies of H_t glued in a chain leave one copy to index order;
  the count of §3 would have to be redone for several chosen agents in one copy.
- The big-top programme of `k4/rulef.md` §6 cannot be repaired by a better choice of the single first agent: the
  obstruction is not where the big-top agent is, but that the profile can need two independent choices. An existence
  statement over longer insertion sequences, chosen at every insertion step (LB₄'s search, K4.LB4; or rule F applied
  at each insertion step), is not touched by these instances.
