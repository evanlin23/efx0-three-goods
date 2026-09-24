# Structure of a minimal counterexample (plan Step 3.3)

Workstream `proof/min-counterexample`. An independent route to TARGET by induction, in the style of the four-colour
theorem: show that a minimal counterexample contains no *reducible configuration*, and (eventually) that every
candidate core contains one. Work in progress; the status of each statement is given where it is stated.

Notation as in `proofs/lemmas.md`: R_i is agent i's set of relevant goods, θ_i(B) = v_i(B) − min_{g ∈ B} v_i(g) is the
largest value i can see in B after deleting one good (θ_i(B) = 0 if |B| ≤ 1; F1), agent i is *safe* in X iff
v_i(X_i) ≥ θ_i(X_j) for all j ≠ i, and a good is *alone* if its bundle is exactly {g}.

## 0. The inductive statement, and why plain EFX₀

A *counterexample* is an additive instance with |R_i| ≤ 3 for every agent and no EFX₀ allocation. A *minimal
counterexample* is one with the fewest agents n and, among those, the fewest goods m.

We induct on plain EFX₀ existence (TARGET itself), not on conjecture D or on EFX₀ with a boundary condition:
- The hypothesis then holds for *every* instance with fewer agents, or with n agents and fewer goods, cores or not:
  arbitrary additive valuations with at most three relevant goods, top-heavy agents, agents with one or two relevant
  goods, worthless goods. A reduction may therefore replace a configuration by any gadget built from such agents, and
  it never has to show that the smaller instance is a core. A stronger statement (D, or EFX₀ with a boundary condition)
  would have to be re-proved for every gadget instance a reduction uses.
- D is not closed under the operations the reductions use: it does not pass to disjoint unions (`proofs/lemmas.md`,
  note after L6), and a reduction that deletes a configuration generally leaves a non-core.
- The cost: nothing is known about the EFX₀ allocation Y of the smaller instance beyond the EFX₀ inequalities, so a
  reduction must extend *every* such Y. The one normalization available for free is F2 (rotation along envy cycles),
  which lets us assume that Y's envy graph is acyclic.
If a reduction fails only because Y can be "wrong" at the boundary, that is recorded, since it would be the evidence
for strengthening the statement.

## 1. Basic facts about a minimal counterexample

**Lemma M0.** Let H be a minimal counterexample, with n agents and m goods. Then:
- (a) every instance with |R_i| ≤ 3 and fewer than n agents, or with n agents and fewer than m goods, has an EFX₀
  allocation;
- (b) H is a connected core;
- (c) replacing H's values by a strict balanced realization of any strict ranking profile consistent with them gives
  again a minimal counterexample (so we may assume that each agent ranks its three goods strictly, and only the
  rankings matter);
- (d) n ≥ 8, β = 2n − m + 1 ≥ 3 (i.e. m ≤ 2n − 2), m ≥ n + 4, and some good is relevant to at least three agents.

*Proof.* (a) is minimality. (b) If H is not a core, one of the cases 1–3 of the proof of the CORE theorem
(`proofs/lemmas.md`) applies and reduces H, via L3 or L2, to an instance with fewer agents or with the same agents and
fewer goods; that instance has an EFX₀ allocation by (a), and L3/L2 extend it to H. If H is a core but not connected,
each component has fewer agents (L6: each has at least two), so has an EFX₀ allocation by (a), and L6 combines them.
(c) The new instance H_σ has the same n and m. If it had an EFX₀ allocation X, every agent would satisfy one of the
cases T, P, B, C, E of L5 in X, and by L5(iv) X would be EFX₀ for H. (d) n ≤ 7 is R5, β ≤ 2 is T2 (β = 1: L8; β = 2:
D2), m ≤ n + 3 and "no good relevant to three agents" are T3. ∎

(d) uses results that rest on computation (R5) and on two published theorems (T3); the lemmas below do not use (d)
unless they say so.

## 2. Local reductions: the soundness lemma

A *configuration* in H is a set S of agents together with a set I of goods that no agent outside S values. Write
∂ = (∪_{s ∈ S} R_s) ∖ I for its *boundary goods* (valued by an agent of S and by some agent outside S). A *reduction*
replaces (S, I) by a gadget (S′, I′): new agents S′ that value only goods of I′ ∪ ∂ (any additive valuations with at
most three relevant goods), and new goods I′ that no agent outside S′ values; the outside agents, their valuations and
the other goods stay. The result H′ must be smaller: |S′| < |S|, or |S′| = |S| and |I′| < |I|. By M0(a), H′ has an
EFX₀ allocation Y.

*Local state of Y.* Call L′ = I′ ∪ ∂ the local goods of H′. The local state of Y records, for each s′ ∈ S′, the set
Y_{s′} ∩ L′ and whether Y_{s′} contains a good outside L′; and, for each bundle Y_j of an outside agent that meets L′,
the set Y_j ∩ L′ and whether Y_j contains a good outside L′ (these bundles unlabeled). Goods outside L′ are relevant
to no agent of S′, so every agent of S′ is safe or not according to the local state alone.

*Extension.* From the local state, build an allocation X of H: every outside agent keeps its bundle, minus the goods of
I′, plus possibly some goods of I; the *moved items* (the boundary goods that agents of S′ held in Y, and, for each
s′ ∈ S′, the set of goods outside L′ that s′ held, moved as a whole) go to agents of S, or to outside agents whose bundle
in Y consisted of goods of I′ only; each agent of S also gets some goods of I. For a bundle B write
U(B) for its goods valued by some outside agent (goods of ∂, and goods outside L′ ∪ I), and say B is *inner* if it
contains a good of I or I′. Say B is *dominated* by a bundle B′ if |B| ≤ 1, or U(B) = ∅, or U(B) ⊆ U(B′) and
(B is not inner, or B′ is inner, or U(B) ≠ U(B′)).

**Lemma M1 (local reductions are sound).** Suppose that for every local state in which every agent of S′ is safe there is
an extension X in which (i) every agent of S is safe and (ii) every bundle of X that is not a bundle of Y is dominated
by some bundle of Y. Then H has an EFX₀ allocation. Hence a minimal counterexample contains no such configuration; we
call the configuration (with the rankings of its agents) *reducible*.

*Proof.* Take Y EFX₀ for H′ (M0(a)) and the extension X of its local state. All goods of H are allocated: outside goods
stay in outside bundles or move with an agent of S′'s bundle to an agent of S, boundary goods stay or move likewise, and
the goods of I are placed by the extension.
- Agents of S value only goods of I ∪ ∂. For s ∈ S and any bundle B, θ_s(B) depends only on B ∩ R_s and on whether B
  contains a good outside R_s, which X's description determines; (i) is exactly the statement that s is safe.
- Let j be an outside agent. It values no good of I or I′, so v_j(X_j) ≥ v_j(Y_j): either X_j and Y_j have the same
  goods outside I ∪ I′, or Y_j ⊆ I′ and v_j(Y_j) = 0. Bundles of X that are bundles of Y
  (the other outside bundles unchanged) threaten j exactly as in Y. For any other bundle B of X, take B′ from (ii).
  *Claim: θ_j(B) ≤ θ_j(B′).* If |B| ≤ 1 or U(B) = ∅, θ_j(B) = 0 (j values nothing in B other than goods of U(B)).
  Otherwise U(B) ⊆ U(B′). Note that θ_j is monotone under inclusion: for B₁ ⊆ B₂, θ_j(B₂) = v_j(B₁) + v_j(B₂ ∖ B₁) −
  min_{B₂} v_j ≥ v_j(B₁) − min_{B₁} v_j, because the minimum over B₂ is at most the minimum over B₁ and, if it is
  attained in B₂ ∖ B₁, at most v_j(B₂ ∖ B₁). If B is not inner, B = U(B) ⊆ B′ and monotonicity gives the claim. If B
  is inner, it contains a good worthless to j, so θ_j(B) = v_j(U(B)); if B′ is inner too, θ_j(B′) = v_j(U(B′)) ≥
  v_j(U(B)); if not, U(B) ⊊ U(B′) = B′ and θ_j(B′) = v_j(B′) − min_{B′} v_j ≥ v_j(U(B)), since B′ ∖ U(B) contains a
  good worth at least the minimum.
  Now θ_j(B′) ≤ v_j(Y_j): if B′ ≠ Y_j because j is safe in Y, and if B′ = Y_j by F1. So θ_j(B) ≤ v_j(Y_j) ≤
  v_j(X_j). ∎

The lemma is deliberately conservative: it keeps every outside bundle's outside-visible part, and it asks for one
dominating bundle that works for all outside agents at once. A configuration that fails it may still be reducible by
an argument that uses more of Y.

**Deleted boundary goods.** A reduction may also delete some boundary goods from H′ altogether (outside agents that
valued them simply lose them). The extension must then place each deleted good g in a bundle of an agent of S, and
the domination condition forces that bundle to be exactly {g} (no bundle of Y contains g). The proof of M1 is
unchanged: j's value and every bundle not containing g are as before, and {g} threatens nobody.

## 3. Peeling pairs: private tops

A *P-agent* is an agent with a private good (p_e for agent e); a *Q-agent* has none.

**Lemma M2 (private top next to a P-agent).** In a minimal counterexample there is no agent e whose most valuable
good is its private good p_e and that has another good b valued by exactly one other agent f, where f is a P-agent.

*Proof.* Let c be e's third good and d, p_f the other goods of f (c = d is allowed). Let H′ be H minus the agents e, f
and the goods p_e, p_f, b. No agent of H′ values p_e, p_f or b, and H′ has fewer agents, so it has an EFX₀ allocation Y
by M0(a). Let X be Y together with X_e = {p_e} and X_f = {p_f, b}.
- e holds its top good p_e. Every other bundle meets R_e = {p_e, b, c} in at most one good (b lies in X_f, which does
  not contain c), so its threat to e is at most max(v_e(b), v_e(c)) < v_e(p_e).
- f holds two of its goods; every other bundle meets R_f in at most d, and v_f(d) < v_f(p_f) + v_f(b) by balance (L8).
- An outside agent j keeps Y_j; X_e is a singleton, and X_f consists of goods j does not value, so neither threatens
  j; the other bundles are those of Y. So X is EFX₀, a contradiction. ∎

This is Lemma M1 with S = {e, f}, I = {p_e, p_f, b} and no gadget; `src/reduce.py` confirms it for all 12 rankings of
e with p_e on top and of f (log below). Its content in terms of shapes: on a thread (a maximal path of P-agents joined
by goods of degree 2, L11) with at least two agents, no agent ranks its private good first.
