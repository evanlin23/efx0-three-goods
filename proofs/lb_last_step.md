# The last step of construction LB, and a construction that never fails (LB⁺)

Workstream `proof/lb-last-step`, ledger items S2.R, S2.LB+, S2.LB, D, T; open item 8. Construction LB and its
soundness theorem are in `proofs/construction.md` §3 (workstream `compute/large-bundle`, PR #9); notation as there.

**Status.** This is a written proof. Two independent reviews found no error. Machine-checked in Lean (PR #18:
`EFX.target`, `EFX.LB.corollaryD`, `lean/EFX/{PreAlloc,Blocks,OwnerR,Rotation,LBPlus,CorollaryD,Target}.lean`); the
ledger claims S2.R, S2.LB+, D and T.

**Change of target (PROMPT.md §5 rule 5).** The task was S2.LB: LB's Phase 2 always finds an owner for the overflow
bundle. This file proves a slightly different statement that serves the same purpose. §4 identifies an owner that
works in every case but one, the *bad case*. In the bad case, one *rotation* along a chain of agents gives a new
partial allocation that is still sound and has an owner (§5). The resulting construction LB⁺ never fails, whatever
insertion rule Phase 1 uses (§6). This gives a proof of conjecture D for every instance in which every agent values exactly three
goods and is balanced, connected or not, and with L2 and L3 a proof of TARGET. S2.LB itself stays a conjecture, and D does not need it.
S2.LB would follow if LB's lookahead never reached the bad case. LB never reaches it on any core with n ≤ 6, nor on any
connected core with n = 7, 11 ≤ m ≤ 14 or n = 8, m ∈ {15, 16} (§7; one labelling per isomorphism class).

Summary of what is proved here, with a complete proof (§1–§6):
- **Theorem 1′ (soundness of pre-allocations).** A generalization of `proofs/construction.md` Theorem 1 to any "valid
  pre-allocation", not only LB's.
- **Theorem A (the owner r).** After any run of Phase 1 and LB's upgrades, the last-processed agent that is not
  upgraded, r, is a valid owner unless the bad case holds. In the bad case, the leader k of the last block holds only its top,
  {b_k, c_k} ⊆ J ∪ {Y_r} (so one of them may be r's pick), k is frozen, every need chain from k ends at r, and the junk
  parts of the exposed pairs are disjoint.
- **Theorem B (rotation).** In the bad case, move every agent of a need chain from k to r one step up the chain. Then k
  takes {b_k, c_k}. The result is a valid pre-allocation, and either it needs no large bundle or k is a valid owner.
- **Theorem C (LB⁺ never fails).** With any insertion rule in Phase 1, LB's upgrades, then owner r, or else Theorem B,
  the output is EFX₀ and has at most one bundle of more than two goods.
- **Corollary D.** Every instance in which every agent values exactly three goods and is balanced (a_i < b_i + c_i)
  has an EFX₀ allocation with at most one bundle of more than two goods. In particular every core has one (conjecture
  D, connected or not), and with L2 and L3, **TARGET holds**.

The proof does not use connectivity, the "at most one private good" condition of cores, L5, or any computation. The
cross-checks in §7 are evidence only. `src/lbplus.c` runs LB⁺ exactly as written below. It asserts every lemma, and it
checks every output against the raw EFX₀ definition. It runs on every core with n ≤ 6 under every ranking profile and
every sequence of insertion choices, on every connected core with n = 7, 11 ≤ m ≤ 14 and n = 8, m ∈ {15, 16} under LB's
own and under random choices, and on random non-core instances. It found 0 failures in 5.8 × 10⁹ runs, of which
1.3 × 10⁶ needed the rotation. A separate Python implementation agrees with it.

## 0. Setting

An *instance* has agents N = [n] and goods M = [m]; valuations are additive. Every agent i values exactly three goods
R_i = {a_i, b_i, c_i}, with v_i(a_i) ≥ v_i(b_i) ≥ v_i(c_i) > 0 and v_i(g) = 0 for g ∉ R_i. Every agent is
*balanced*: v_i(a_i) < v_i(b_i) + v_i(c_i). Ties are broken once and for all, and ≻_i denotes the resulting strict
order a_i ≻_i b_i ≻_i c_i. Goods valued by nobody are allowed. Every core (PROMPT.md §3) is such an instance.

An allocation X is EFX₀ if v_i(X_i) ≥ v_i(X_j ∖ {h}) for all i ≠ j and h ∈ X_j. A bundle with one good is never
strongly envied, since X_j ∖ {h} = ∅.

## 1. Phase 1 (serial dictatorship with R1 priority) and its invariants

Phase 1 processes the agents one at a time. G is the set of remaining goods, initially M. Each processed agent i takes
its ≻_i-favourite good of R_i ∩ G as its *pick* Y_i, or nothing (Y_i = none) if R_i ∩ G = ∅, and Y_i leaves G. The
next agent is chosen as follows.
- *R1 step:* if some unprocessed agent i has |R_i ∩ G| ≤ 2, the next agent is one such agent (any of them).
- *Insertion step:* otherwise every unprocessed agent has R_i ⊆ G, and the next agent is any unprocessed agent. It
  takes its top a_i.

Construction LB (`proofs/construction.md` §3, `src/construct.py`) is one instance of this: its R1 steps take the agent
of smallest key and its insertion steps use a lookahead. **Nothing below depends on these choices.** After the last
agent, the goods left in G are the *junk* J₀.

- **(I1)** If g ∈ R_i and g ≻_i Y_i (or Y_i = none), then g was picked before i's turn. Agent i took its favourite
  remaining good, so every good it prefers was gone.
- **(I2)** If g ∈ R_i ∩ J₀, then Y_i ≠ none and Y_i ≻_i g. The good g was still in G at i's turn.
- **(I3)** If R_k ⊆ G at k's turn, then k was processed in an insertion step, since R1 steps process only agents with
  |R_i ∩ G| ≤ 2.

A *block* is an insertion step together with the R1 steps that follow it before the next insertion step. The first
step is an insertion step, because initially every agent has all three goods. Each block has exactly one insertion
agent, its *leader*.
- **(B1)** When a block starts, every unprocessed agent i has R_i ⊆ G. This is the condition for an insertion step.
- **(B2)** Let j be an agent and g ∈ R_j with g ≻_j Y_j (or Y_j = none). Then g was picked by an agent processed
  before j *in j's block*. By (I1) g was picked before j's turn. If it had been picked in an earlier block, then j, still
  unprocessed when j's block started, would have had g ∉ G, contradicting (B1).

## 2. Pre-allocations and their soundness

**Definition.** A *pre-allocation* P = (Y, U) consists of
- picks Y_i ∈ R_i ∪ {none}, the picked goods distinct, and
- a set U of *upgraded* agents, where every u ∈ U has Y_u = b_u and also holds c_u. The goods c_u (u ∈ U) are distinct
  and are nobody's pick.

The *junk* is J = M ∖ ({picks} ∪ {c_u : u ∈ U}). For an agent i ∉ U, its *needs* are
N_i = {g ∈ R_i : g ≻_i Y_i}, or N_i = R_i if Y_i = none. The *needed-alone set* is NA = ⋃_{i ∉ U} N_i.

P is *valid* if
- **(V1)** J ∩ NA = ∅, and
- **(V2)** b_u, c_u ∉ NA for every u ∈ U.

In a valid P, every good of NA is the pick of an agent outside U: it is not junk (V1), not c_u and not b_u (V2).

The agents split as follows. An agent i ∉ U is *frozen* (i ∈ F) if Y_i ∈ NA. The *terminals* are T = N ∖ (U ∪ F).
The *slots* are cap(i) = 0 for i ∈ U ∪ F, cap(i) = 1 for i ∈ T with a pick, and cap(i) = 2 for i ∈ T without one.
S = Σ_i cap(i) and ω = |J| − S. The *base* of an agent is base(i) = {Y_i} (∅ if none) for i ∉ U, and {b_i, c_i} for
i ∈ U.

**Completions.** Let o ∈ T ∪ U be an *owner* (or no owner), and C ⊆ J. The completion puts:
- X_i = base(i) for i ∈ F ∪ U, i ≠ o;
- X_i = base(i) ∪ C_i for i ∈ T, i ≠ o, where the C_i partition C and |C_i| ≤ cap(i);
- X_o = base(o) ∪ (J ∖ C). With no owner, C = J.

A completion satisfies the *owner constraint* (OC) if no agent x ∉ U, x ≠ o, with Y_x = a_x has {b_x, c_x} ⊆ X_o.

**Theorem 1′ (soundness).** Let P be a valid pre-allocation. Every completion of P that satisfies (OC) is an EFX₀
allocation, for every additive valuation consistent with the rankings and balanced. Only X_o can have more than two
goods.

*Proof.* Every good is in exactly one bundle, and only X_o can exceed two goods. Fix i and j ≠ i with |X_j| ≥ 2. Then
j ∉ F, and X_j ∩ NA = ∅, since X_j consists of Y_j (∉ NA: j ∉ F, or j ∈ U and V2), possibly c_j with j ∈ U (V2), and
junk (V1).
- If i ∈ U: X_i ⊇ {b_i, c_i}, so R_i ∩ X_j ⊆ {a_i} and v_i(X_j ∖ {h}) ≤ v_i(a_i) < v_i(b_i) + v_i(c_i) ≤ v_i(X_i).
- If i ∉ U and Y_i = none: R_i = N_i ⊆ NA, so R_i ∩ X_j = ∅ and v_i(X_j ∖ {h}) = 0.
- If i ∉ U has a pick: no good of R_i ∩ X_j is in N_i ⊆ NA, and none is Y_i ∈ X_i, so each is ranked below Y_i and
  worth at most v_i(Y_i) ≤ v_i(X_i) to i. If |R_i ∩ X_j| ≤ 1 we are done. Otherwise R_i ∩ X_j consists of two goods
  ranked below Y_i, so Y_i = a_i and R_i ∩ X_j = {b_i, c_i}. If |X_j| = 2, then X_j ∖ {h} is one of b_i, c_i, worth at
  most v_i(a_i). If |X_j| ≥ 3, then j = o and i ≠ o, and (OC) excludes {b_i, c_i} ⊆ X_o.

Only i's own valuation was used, together with a_i ≻ b_i ≻ c_i and balance. ∎

This is `proofs/construction.md` Theorem 1 with LB's Phase 1 invariants replaced by (V1)–(V2).

**Lemma 1 (owner criterion).** Let P be valid with ω ≥ 1, and o ∈ T ∪ U. The *exposed* agents are
E_o = {x ∉ U, x ≠ o : Y_x = a_x and {b_x, c_x} ⊆ J ∪ base(o)}. Suppose that
- no x ∈ E_o has {b_x, c_x} ⊆ base(o), and
- some H ⊆ J with |H| ≤ S − cap(o) meets {b_x, c_x} for every x ∈ E_o.

Then P has a completion with owner o that satisfies (OC).

*Proof.* Since |J| = S + ω > S − cap(o), H extends to C ⊆ J with |C| = S − cap(o). This exactly fills the slots of
the terminals other than o. Let X_o = base(o) ∪ (J ∖ C). Take x ∉ U, x ≠ o, with Y_x = a_x and {b_x, c_x} ⊆ X_o.
Then {b_x, c_x} ⊆ J ∪ base(o), so x ∈ E_o. So H meets {b_x, c_x} in a good of C, which is not in X_o: a contradiction.
∎

Every choice works here: any C ⊇ H of size S − cap(o), and any split of C into the slots. The argument uses only
H ⊆ C, and Theorem 1′ covers every completion that satisfies (OC).

If ω ≤ 0, the completion with no owner (C = J, |J| ≤ S) has all bundles of at most two goods. It satisfies (OC)
vacuously.

## 3. LB's Phase 2 state is a valid pre-allocation

Phase 2 of LB starts from the picks of Phase 1, with U = ∅ and J = J₀. It *upgrades*: while some k ∉ U has
Y_k = b_k, c_k ∈ J and b_k ∉ NA (NA computed for the current U), it puts k in U and removes c_k from J. The
loop may pick such k in any order (LB takes the smallest index). Different orders can give different sets U, but the
proof below uses only (UT) and validity, which hold for every order. The upgrades only shrink NA. When the loop stops:

- **(UT)** no k ∉ U has Y_k = b_k, c_k ∈ J and b_k ∉ NA.

The resulting (Y, U) is a valid pre-allocation. (V1): by (I2), a junk good is ranked below the pick of every agent that
values it, so it is in no N_i. (V2): c_u was junk, so it is in no N_i. b_u ∉ NA held when u was upgraded, and NA only
shrinks. The frozen agents, slots, ω, and LB's overflow bundle are exactly those of `proofs/construction.md` §3. LB's
owner constraint is (OC), and LB's search for (o, J_L) succeeds iff some owner satisfies Lemma 1's conclusion.

## 4. Theorem A: the owner r, and the bad case

Fix a run of Phase 1 and the Phase 2 state P = (Y, U) above, with ω ≥ 1. Let r be the last-processed agent not in U.
It exists: the first processed agent is an insertion agent holding its top, and U contains only agents holding their
b.

- **(A1) r ∈ T.** If Y_r ∈ NA, some j ∉ U has Y_r ∈ N_j. By (I1), Y_r was picked before j's turn, so j was processed
  after r and is not in U, contrary to the choice of r. If Y_r = none, then r ∉ F by definition.
- **(A2)** Every agent processed after r is in U, and r lies in the last block B*. The leader of any later block would
  hold its top, so it would not be in U.
- **(A3) Exposed agents are leaders.** Let x ∈ E_r. Then x ∉ U and x ≠ r, so x was processed before r (A2). At x's
  turn, a_x = Y_x was available. So was every junk good, since junk is never picked, and so was Y_r, which r picked
  later. Since {b_x, c_x} ⊆ J ∪ {Y_r}, we get R_x ⊆ G at x's turn. By (I3), x is the leader of its block. Hence every
  block contains at most one agent of E_r, and E_r ∩ B* ⊆ {k*}, where k* is the leader of B*.
- **(A4) Need chains.** For x ∈ F, some j ∉ U has Y_x ∈ N_j (definition of F), and j ≠ x. By (B2), j is processed
  after x, in x's block. Repeating from j while it is frozen gives a *need chain* x = x₀, x₁, …, x_t of distinct agents
  of x's block, with x_{i+1} ∉ U, Y_{x_i} ∈ N_{x_{i+1}}, x₀, …, x_{t−1} ∈ F and x_t ∈ T. For x ∉ U let τ(x) be x if
  x ∈ T, and otherwise the end of some need chain from x. It is a terminal in x's block, so it has cap ≥ 1.
- For x ∈ E_r, write π_x = {b_x, c_x} ∩ J. It is not empty, since at most one of b_x, c_x is Y_r. No x ∈ E_r has
  {b_x, c_x} ⊆ base(r) = {Y_r}.

**Theorem A.** r is a valid owner (Lemma 1 applies to o = r), except possibly in the following *bad case*:
- E_r ∩ B* = {k*} with k* ≠ r and k* ∈ F;
- every need chain from k* ends at r; and
- the sets π_x (x ∈ E_r) are pairwise disjoint.

*Proof.* The agents τ(x), x ∈ E_r ∖ B*, lie in distinct blocks other than B* (A3), so they are distinct terminals other
than r. Hence S − cap(r) ≥ |E_r ∖ B*|. The first condition of Lemma 1 was checked above. For the second, let H contain
one good from each π_x, choosing a common good when two of them meet.
- If E_r ∩ B* = ∅, then |H| ≤ |E_r| = |E_r ∖ B*| ≤ S − cap(r).
- Otherwise E_r ∩ B* = {k*} by (A3). Then k* ≠ r, since r ∉ E_r, and |E_r ∖ B*| = |E_r| − 1.
  - If k* ∈ T, or some need chain from k* ends at a terminal other than r, then τ(k*) can be chosen in B* ∖ {r}. It is
    one more terminal, distinct from the others, so S − cap(r) ≥ |E_r| ≥ |H|.
  - If two of the sets π_x meet, one good of H serves both, so |H| ≤ |E_r| − 1 = |E_r ∖ B*| ≤ S − cap(r).

If neither sub-case applies, the three conditions of the bad case hold. ∎

## 5. Theorem B: the rotation

Assume the bad case. Let k = k*, and fix a need chain k = x₀, x₁, …, x_t = r (t ≥ 1). It exists: k ∈ F, and every
need chain from k ends at r. If there are several, any one may be used; nothing below depends on the choice. Define P′ = (Y′, U′):
- Y′_{x_i} = Y_{x_{i−1}} for 1 ≤ i ≤ t: every agent of the chain takes the good it needed from its predecessor;
- Y′_k = b_k, and U′ = U ∪ {k}: k gives up a_k and takes b_k and c_k, which are free because
  {b_k, c_k} ⊆ J ∪ {Y_r} (k ∈ E_r);
- all other agents keep their picks and upgrade status.

The good Y_r, if r had a pick, is released, and the new junk is J′ = (J ∪ {Y_r}) ∖ {b_k, c_k}. Every pick of P other
than Y_r is still a pick in P′, possibly of another agent of the chain, and every c_u (u ∈ U) is still held by u. Write
W = J ∪ {Y_r}. Then J′ ∪ {b_k, c_k} ⊆ W.

**Theorem B.** P′ is a valid pre-allocation. If ω′ ≤ 0 its completion without owner has all bundles of at most two
goods. Otherwise k is a valid owner of P′.

*Proof.*
(a) *P′ is a pre-allocation.* Y′_{x_i} ∈ R_{x_i}, since x_i needed it. The goods b_k, c_k lie in W, so they are not
picks of P′ and not c_u (u ∈ U), and the other goods only change owner along the chain. Y′_k = b_k.

(b) *NA′ ⊆ NA.* For x_i (i ≥ 1), Y′_{x_i} ≻ Y_{x_i} (or Y_{x_i} = none), so N′_{x_i} ⊆ N_{x_i}. Agent k had N_k = ∅
and is now in U′. Nobody else changes.

(c) *Validity.* J′ ⊆ W. By (V1), J ∩ NA = ∅, and by (A1), Y_r ∉ NA, so J′ ∩ NA′ = ∅. For u ∈ U, b_u, c_u ∉ NA ⊇ NA′.
For k, b_k, c_k ∈ W, so they are not in NA ⊇ NA′.

(d) *Terminals outside B\* survive.* Let x ∈ T ∖ B*. Then x ∉ U′, and Y′_x = Y_x ∉ NA ⊇ NA′, so x ∈ T′ with the
same cap.

(e) *E′_k ⊆ E_r ∖ {k}.* Here E′_k = {x ∉ U′, x ≠ k : Y′_x = a_x, {b_x, c_x} ⊆ J′ ∪ {b_k, c_k}}, and J′ ∪ {b_k, c_k}
⊆ W. Let x ∈ E′_k.
- If x is not on the chain, then Y_x = Y′_x = a_x, x ∉ U, x ≠ r and {b_x, c_x} ⊆ W. So x ∈ E_r.
- x = x_i with 1 ≤ i ≤ t − 1 is impossible. Y_{x_i} is a pick other than Y_r, so it is not in W. Since a_{x_i} = Y′_{x_i}
  ≻ Y_{x_i}, the good Y_{x_i} is b_{x_i} or c_{x_i}, which contradicts {b_{x_i}, c_{x_i}} ⊆ W.
- x = r is impossible. Y_r ≠ a_r, because r needs Y_{x_{t−1}}.
  - If Y_r = none, b_r was picked by another agent (I1), so b_r ∉ W.
  - If Y_r = c_r, b_r ∈ N_r was picked by another agent (I1), so b_r ∉ W.
  - If Y_r = b_r, then (UT) applies to r (r ∉ U, b_r ∉ NA by A1), so c_r ∉ J. As c_r ≠ Y_r, c_r ∉ W.

  In each case {b_r, c_r} ⊄ W.

(f) *No exposed pair lies in base′(k) = {b_k, c_k}.* If x ∈ E′_k had {b_x, c_x} ⊆ {b_k, c_k} (so the two pairs are
equal), then x ∈ E_r ∖ {k} by (e),
and π_x = π_k ≠ ∅, contradicting the disjointness in the bad case.

(g) *Counting.* By (f), every x ∈ E′_k has a good of {b_x, c_x} in J′. Let H′ contain one such good for each x. By (e),
|H′| ≤ |E_r| − 1 = |E_r ∖ B*|. The terminals τ(x) (x ∈ E_r ∖ B*) are distinct, lie outside B*, and have cap′ ≥ 1 by
(d). So |H′| ≤ S′ = S′ − cap′(k), since cap′(k) = 0 (k ∈ U′). Lemma 1 applies to P′ and o = k when ω′ ≥ 1. ∎

## 6. Theorem C and the corollaries

**Construction LB⁺.** Run Phase 1 (§1, any choices), then LB's upgrades (§3, any order). If ω ≤ 0, return the
completion without owner. Otherwise test r exactly by Lemma 1's condition: let H be a *minimum* hitting set of the sets
π_x = {b_x, c_x} ∩ J (x ∈ E_r). If |H| ≤ S − cap(r), return a completion with owner r (Lemma 1). Otherwise rotate
along a need chain from k* to r (Theorem B, any chain). Return the completion of P′ without owner if ω′ ≤ 0, and with
owner k* otherwise.

The "otherwise" branch is always the bad case. This is the contrapositive of Theorem A: whenever r fails Lemma 1's
test, the three conditions of the bad case hold. So LB⁺ never meets an invalid r outside the bad case. The test must be
Lemma 1's exact condition, a minimum hitting set compared with S − cap(r). Taking one good per exposed pair without
reusing shared goods can overestimate |H| and reject a valid r outside the bad case (remark 2).

**Theorem C.** For every instance of §0 and every run of Phase 1, LB⁺ returns an allocation that is EFX₀ for every
consistent balanced additive valuation, with at most one bundle of more than two goods.

*Proof.* The pre-allocation is valid (§3, Theorem B(c)). The returned completion satisfies (OC): vacuously when there
is no owner, and by Lemma 1 with owner r (Theorem A) or owner k* (Theorem B). Apply Theorem 1′. ∎

**Corollary D.** Every instance in which every agent values exactly three goods and is balanced has an EFX₀
allocation with at most one bundle of more than two goods. In particular conjecture D holds for every core, connected
or not (ledger D, open item 5).

**Corollary T (TARGET).** Every additive instance with |R_i| ≤ 3 for every agent has a complete EFX₀ allocation.
*Proof.* By the CORE theorem of `proofs/lemmas.md` (L2 peeling and L3 junk, by induction), it suffices that every core
has an EFX₀ allocation. A core satisfies (K1) |R_i| = 3 and (K2) balance, so it is an instance of §0, and Corollary D
applies. ∎

Remarks.
1. *Size of the large bundle.* X_o = base(o) ∪ (J ∖ C) has |base(o)| + cap(o) + ω = ω + 2 goods, for o ∈ T as for
   o ∈ U. In any valid pre-allocation each good of NA is the pick of exactly one frozen agent, so |F| = |NA|. Counting
   goods then gives ω = m − 2n + |NA| = |NA| − σ with σ = 2n − m, as in `proofs/construction.md` Lemma 2. The rotation
   does not increase NA (Theorem B(b)), so it does not enlarge the large bundle.
2. LB⁺ is polynomial: Phase 1 is O(n) steps, the upgrades O(n²), and one rotation. With LB's lookahead, Phase 1 is
   O(n³) evaluations. *A sufficient shortcut for the test, not its definition:* one good per exposed pair gives a
   hitting set of size |E_r|. If |E_r| ≤ S − cap(r), r is valid. Otherwise the exact test needs a minimum hitting set.
   In the sub-case of Theorem A where only overlapping π-sets save r, H must use a shared good. Example (second
   review of PR #13): n = 5, m = 8, rankings 0:(5,0,2), 1:(1,2,6), 2:(3,4,7), 3:(3,4,0), 4:(1,3,4), order 0, 1, 4, 3,
   2 with 0 and 1 inserted (an R1 order other than LB's, which §1 allows). Then r = 2, the sets π_x are {0, 2} and {2, 6}, one slot is available, and H = {2} works.
   The minimum is easy to compute here, since the sets π_x have at most two goods each. `src/lbplus.c` computes it by
   brute force.
3. What the proof uses about a core: each agent values exactly three goods and is balanced. It does not use that
   every good is valued, the private-good condition, connectivity, or L5.
4. *Labellings.* LB breaks ties by index, so its output depends on how agents and goods are labelled. Theorem C does
   not: it holds for every choice at every insertion and R1 step, hence for every labelling and every tie-break rule.
   Theorem A and Theorem B do not use the tie-break either. By contrast, the S2.LB evidence in §7 (LB's own runs never
   reach the bad case) covers one labelling per isomorphism class, the one `cores_nauty.py` produces. That is evidence
   only, like `results/construct_relabel.log`.

## 7. What remains of S2.LB, and the computations

**S2.LB (LB never fails) stays a conjecture.** LB's owner search succeeds iff some owner satisfies Lemma 1's
conclusion. By Theorem A it succeeds unless the run reaches the bad case (and even then another owner may work). So
S2.LB follows from: *LB's lookahead never produces the bad case*. This is not proved. A tempting shortcut is false:
"if the last insertion step has minimal lookahead count, r is a valid owner", whatever the earlier insertion choices.
It fails at n = 6, m = 10, in 106 runs with non-LB earlier choices (`attempts/lb-last-insertion-lookahead.md`). D does
not need S2.LB.

**Cross-checks (evidence for the proof, not part of it).** `src/lbplus.c` implements LB⁺ literally. It builds every
completion as in Lemma 1, with one good per exposed pair, not by LB's search. It asserts every claim of Theorems A and B:
(A1), (A2), (A3); the bad-case structure whenever r fails; the need chain staying in B*; the rotation improving every
chain agent; P′ valid; NA′ ⊆ NA; (e); (f); (g). It checks every output with `construct.c`'s raw EFX₀ check: three
balanced realizations, and at most one bundle of ≥ 3 goods. That check does not use the proof's reasoning. Driver:
`src/lb_owner.py --bin=lbplus`. Modes:
- 0: LB's own Phase 1;
- 1: every sequence of insertion choices (a tree of runs; LB's R1 order);
- 2: random insertion *and* R1 choices.

Results (`results/lbplus.log`; 0 assertion failures and 0 raw-check failures everywhere):

| runs | scope | runs | rotated (owner k after it) |
|---|---|---|---|
| mode 1 | every core, n = 2–5, every m, every profile, every insertion sequence | 23,403,096 | 16,318 (28) |
| mode 1 | every core, n = 6 | 2,449,875,384 | 354,024 (1,588) |
| mode 0 | every core, n = 2–6 | 146,640,096 | 0 |
| mode 0 | every connected core, n = 7, m = 11–14 | 1,030,724,352 | 0 |
| mode 0 | every connected core, n = 8, m = 15, 16 | 89,019,648 | 0 |
| mode 2 | every core n = 5 (10 random runs per profile), n = 6 (2), connected n = 7, m = 11–14 (1), n = 8, m = 15, 16 (1) | 1,431,141,696 | 400,670 (12,690) |
| random non-cores | n = 5 (300 instances per m, m = 3–15, mode 1), n = 6 (100 per m, m = 4–14, mode 2), n = 7 (30 per m, m = 5–16, mode 2) | 673,459,632 | 556,089 (320,111) |
| total | | 5,844,263,904 | 1,327,101 (334,417) |

The independent Python implementation `src/lbplus.py` gives the same tallies as `src/lbplus.c` on all 40 levels
(n = 2–5, modes 0 and 1): runs, no owner, owner r, rotated, and the outcome after the rotation. Its own raw checks
also found 0 failures.

Mode 0 never rotates: on these cores, with the labelling `cores_nauty.py` produces, LB's own runs never reach the bad
case. This is the evidence for S2.LB, not part of the proof. Modes 1 and 2 rotate often, so the rotation is needed as
soon as the insertion rule is not LB's lookahead. In mode 1 at n = 6, 195,234 runs at m = 8 have no valid owner at all
before the rotation (`results/lb_tree.log`, `any_bad`).

Instrumentation that led here (evidence):
- `src/lb_owner.c`: the last-processed agent z works except when upgraded, 32 profiles at n = 6, m = 10; r works on
  every LB run with n ≤ 6.
- `src/lb_expose.c`, `src/lb_block.c`: exposure and block statistics.
- `src/lb_tree.c`: the lookahead-only lemma and its counterexamples.

Reproduce (from `src/`; times on 4 CPUs):
```
python lb_owner.py 5 --bin=lbplus --mode=1           # every core n = 5, every profile, every insertion choice: ~5 s
python lb_owner.py 6 --bin=lbplus --mode=1           # n = 6: ~7 min
python lb_owner.py 6 --bin=lbplus --mode=0           # LB's own runs, n = 6: ~1 min
python lb_owner.py 7 14 13 12 11 --bin=lbplus --mode=0          # ~25 min
python lb_owner.py 6 --bin=lbplus --mode=2 --seed=1 --reps=2    # random insertion and R1 choices
python lb_owner.py 5 3 4 5 6 7 8 9 10 11 12 13 14 15 --bin=lbplus --mode=1 --random=300:1   # random non-cores
python lbplus.py 4 --mode=1                          # the Python implementation (n = 5: ~1 h)
python lb_owner.py 6 --bin=lb_tree                   # results/lb_tree.log (X5)
```
