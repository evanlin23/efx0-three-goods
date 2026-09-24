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

**Restricted classes.** For k ≥ 1 let 𝒞_k be the class of instances with |R_i| ≤ 3 whose incidence graph (agents and
goods, an edge when the agent values the good) has only connected components of cyclomatic number at most k. Deleting
agents or goods cannot raise the cyclomatic number of any component (the cycle space of a subgraph is a subspace), so
𝒞_k is closed under the CORE reductions (L2, L3) and under splitting into components (L6). A *minimal counterexample
within 𝒞_k* (fewest agents, then fewest goods, among the instances of 𝒞_k without an EFX₀ allocation) therefore
satisfies M0(a) within 𝒞_k, M0(b), M0(c), and has β ≤ k. Every lemma below also holds for a minimal counterexample
within 𝒞_k, because each smaller instance H′ that a reduction uses lies in 𝒞_k when H does; this is checked for each
reduction (deleting agents and goods is always fine).

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
unchanged: j's value and every bundle not containing g are as before, and {g} threatens nobody. (Not used below.)

**Lemma M1(b) (an unenvied bundle).** By F2 we may assume that the envy graph of Y is acyclic (rotate envy cycles; each
rotation keeps EFX₀ and raises Σ_i v_i(Y_i), so this stops), so some bundle Y_z is envied by nobody. Let the local state
also record which bundle Y_z is: a bundle of an agent of S′, an outside bundle meeting L′, or an outside bundle not
meeting L′ (empty, or holding goods outside L′ only); only states in which no agent of S′ envies Y_z need an extension
(S′-agents value only local goods, so this is a local condition). Then M1 holds with two relaxations: goods of I may
also be added to Y_z if it is an outside bundle, and in (ii) a bundle B of X may instead satisfy U(B) ⊆ U(Y_z).

*Proof.* Only the outside agents' part changes. If U(B) ⊆ U(Y_z), then, since an outside agent j values only goods
counted in U, θ_j(B) ≤ v_j(B) = v_j(U(B)) ≤ v_j(U(Y_z)) = v_j(Y_z) ≤ v_j(Y_j) ≤ v_j(X_j), the third inequality because j
does not envy z (or j = z). Adding goods of I to the outside bundle Y_z changes neither its owner's value nor U. ∎

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

This is Lemma M1 with S = {e, f}, I = {p_e, p_f, b} and no gadget (H′ is H minus agents and goods, so it lies in 𝒞_k
with H); `src/reduce.py` confirms it for all 12 rankings of e with p_e on top and of f (families RPT-e, RPT-f of §4).
Section 4 subsumes it.

## 4. No good of degree 2 is shared by two P-agents

**Theorem M3.** In a minimal counterexample (or a minimal counterexample within 𝒞_k, for any k), no good valued by
exactly two agents is valued by two P-agents.

Equivalently, in the language of L11: every thread (maximal path of agents of H-degree 2 and goods of degree 2) carries
at most one P-agent, and every good of degree 2 is valued by a Q-agent.

*Setting.* Let e, f be P-agents sharing a good g that no one else values; R_e = {gl, g, p}, R_f = {g, y, pf} with p, pf
private. If gl = y, this common good G is valued by at least one agent outside {e, f} (otherwise {e, f} with its five
goods would be a whole component, n = 2); if gl ≠ y, each of gl, y is valued by an agent outside {e, f} (a good valued
only by e and f besides g would again make {e, f} a component). So there are two configurations, *pair* (gl ≠ y,
boundary goods gl, y) and *loop* (gl = y = G, boundary good G), each with interior goods I = {g, p, pf} and 36 ranking
profiles. For each profile at least one of the following reductions satisfies Lemma M1 (with M1(b) where marked):
- **RPT-e / RPT-f** (e resp. f ranks its private good first): Lemma M2.
- **DEL** (M1(b)): delete e, f and I; no gadget. H′ ⊆ H.
- **CON-e** (pair only, M1(b)): delete e, g, p and let f value gl where it valued g (same rank, so f stays a balanced
  agent with the same ranking); gadget S′ = {f′}, I′ = {pf}. **CON-f** symmetrically. In the incidence graph this
  contracts the path gl – e – g into gl and deletes the leaf p, so H′ is a minor of H: it lies in 𝒞_k with H
  (contracting an edge of a connected graph keeps its cyclomatic number).
- **GAD** (loop only, M1(b)): replace e, f, g, p, pf by one agent h valuing G at 2 and a new good q at 1. In the
  incidence graph this deletes the cycle G – e – g – f – G (and the leaves p, pf) and hangs the path G – h – q on G, so
  every component's cyclomatic number stays or drops.

Coverage (`results/min_cex_reductions.log`): pair profiles are covered by RPT-e 12, RPT-f 12, DEL 23, CON-e 26, CON-f 26,
together all 36; loop profiles by RPT-e 12, RPT-f 12, DEL 23, GAD 23, together all 36.

*Proof.* Each reduction has fewer agents, and its H′ lies in the class (above). By Lemma M1 (and M1(b)) the
configuration is reducible under every profile, so it does not occur in a minimal counterexample. The statement "every
admissible local state has an extension" is a finite check per reduction: `src/reduce.py` enumerates the local states
of Y and finds the extensions, and `src/min_cex.py` writes them all as a certificate (`results/min_cex_reductions.json.gz`:
169 reductions, 8,274 local states with their extensions). `tools/check_reductions.py`, written separately, enumerates
the local states again in a different way, judges agents of S by the case table of L5 instead of the raw definition,
re-checks every extension against the rules of M1 and M1(b), and re-derives the coverage of the 72 profiles from the
agents' rankings in the certificate (`results/check_reductions.log`: 0 problems, all 36 + 36 profiles covered). ∎

Status: CERTIFIED (the reductions are verified by two implementations; the reasoning around them is proved). RPT is
also proved by hand (M2). Two examples of what the certificates contain:
- *DEL, both agents rank g first and their private good second* (pair, e: g > p > gl, f: g > pf > y). Take any EFX₀
  allocation Y of H minus {e, f, g, p, pf} and add X_e = {g}, X_f = {pf, p}. Agent e holds its top good g, and its
  other two goods lie in different bundles (p in X_f, gl elsewhere): case T. Agent f holds pf (its b) and its top good g
  is alone: case B. Outside agents value nothing in X_e or X_f. This is the profile that CON-e and CON-f both miss.
- *GAD.* In H′ the agent h is safe only if it holds G or G is alone: otherwise h holds at most q (value ≤ 1), while
  the bundle containing G has at least one other good, worth at most 1 to h, so its threat to h is at least 2. So the
  gadget forces what the loop needs from the rest: G held by the loop side or alone.

## 5. Size of a minimal counterexample

**Corollary M4.** Let H be a minimal counterexample (or one within 𝒞_k) with n agents, m goods, cyclomatic number
β = 2n − m + 1, q Q-agents, and t = Σ (deg g − 2) over the goods of degree at least 3. Then

  n ≤ 5(β − 1) − t, equivalently 5m ≤ 9n − t.

*Proof.* Let π = n − q be the number of P-agents; each has exactly one private good (K3), so L4 reads 3n = 2m − π + t,
i.e. 2m = 3q + 4π − t, and β − 1 = 2n − m = (q + t)/2. Count incidences between agents and shared goods: P-agents have
two shared goods, Q-agents three, so 3q + 2π = Σ_{g shared} deg g = 2m₂ + Σ_{deg g ≥ 3} deg g, where m₂ is the number of
goods of degree 2. By M3 each good of degree 2 is valued by a Q-agent, and distinct goods use distinct Q-agent
incidences, so m₂ ≤ 3q. For deg g ≥ 3, deg g ≤ 3(deg g − 2), so Σ_{deg g ≥ 3} deg g ≤ 3t. Hence 3q + 2π ≤ 6q + 3t,
π ≤ 3(q + t)/2 = 3(β − 1), and n = q + π ≤ 2(β − 1) − t + 3(β − 1). ∎

Before M3 the only bound was m ≤ 2n − 2 (β ≥ 3); now a minimal counterexample has at most 9n/5 goods, and for each β
only finitely many cores remain. With T3 (t ≥ 1, m ≥ n + 4, i.e. n ≥ β + 3): β + 3 ≤ n ≤ 5β − 6.

## 6. TARGET for cyclomatic number at most 3

**Theorem M5.** Every instance in 𝒞_3 has an EFX₀ allocation. Hence TARGET holds for every instance whose core (from
any sequence of the CORE reductions) has only connected components with β ≤ 3, i.e. m_C ≥ 2n_C − 2 for each component.

*Proof.* Suppose not, and let H be a minimal counterexample within 𝒞_3: a connected core with β ≤ 3 (§1). β = 1 is
L8 and β = 2 is D2, so β = 3 and m = 2n − 2. Every connected core with n ≤ 6 is covered by R1, with n = 7, m = 12 by R2,
and with n = 8, m = 14 by R4; so n ≥ 9. By M4, n ≤ 10 − t ≤ 10. So H is a connected core with (n, m) = (9, 16) or
(10, 18) in which no good of degree 2 is valued by two P-agents (M3). Of the 2,477 and 4,619 connected cores with these
(n, m), exactly 15 and 5 have that property, and each of these 20 has an EFX₀ allocation under every ranking profile
(certificates below), contradicting M0(c). The second sentence: each CORE reduction step extends EFX₀ allocations
(L2, L3) and components combine (L6). ∎

The proof uses no published theorem (neither Mahara nor Afshinmehr et al.): only L2, L3, L6, L8 and D2 (proved), R1,
R2, R4 and M3 (certified), and the certificate for the 20 cores. As M4 predicts, the 20 cores are tight: the 15 with
n = 9 have t = 1 (six P-agents, one good of degree 3) or t = 0 (five P-agents, four Q-agents), the 5 with n = 10 have
t = 0 and every thread carrying exactly one P-agent.

## 7. Sanity check: β = 2 in three lines

Within 𝒞_2 a minimal counterexample has β = 2 (L8), so n ≤ 5 − t ≤ 5 by M4, and R1 covers every connected core with
n ≤ 6. So M3 + M4 + R1 reprove TARGET for 𝒞_2 (the EFX₀ part of D2/T2) without D2's construction; they do not give D2's
bound on the large bundle.
