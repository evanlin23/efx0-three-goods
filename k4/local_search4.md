# Two-phase local search for k = 4 cores (Algorithm LS4)

Workstream `proof/k4-localsearch`. Ledger rows `K4.LS.*`. This carries the two-phase local search of
`proofs/local_search.md` (Algorithm LS2, Theorem C, row LS3) from three to four relevant goods per agent. It is a
route to TARGET₄ that does not go through construction LB₄ (`k4/SCOUT.md` §5).

**Status.**
- **Negative result (the main finding).** The k = 3 scheme does not carry over as it stands. Theorem C allows *any* choice of moves. At k = 4 there is a *dead end* (n = 4, m = 7, a pure core): a junk-free EFX₀ partial allocation that LS4 reaches from the empty allocation with 15 single-agent rebundles, and that no complete EFX₀ allocation weakly Pareto-dominates (§4, `attempts/k4-ls-dead-end.md`; replayed by an independent brute force). Hence:
  - conjecture TP₄ ("every stable state can be completed by a placement") is false;
  - no two-phase local search whose Phase 1 makes Pareto improvements with arbitrary choices, and whose Pareto move set contains single-agent rebundles, proves TARGET₄.

  A local-search proof for k = 4 needs a choice rule that provably avoids dead ends, or moves that make some agent worse off.
- *Proved here, pending review.*
  - Algorithm LS4 is sound and makes at most Σ_i (2^{d_i} − 1) ≤ 15n Phase-1 moves (Theorem 1). Every output is a complete EFX₀ allocation. It fails only at a stable state that no placement completes.
  - Such a state has at least two sources (Lemma 5, Proposition 4: the k = 4 form of LS2's champion step).
  - It has an agent with four goods: for cores whose agents all have three goods, LS4 never fails (Proposition 3, conditional on the proof of Theorem C of `proofs/local_search.md`, itself pending review).
- *Computation (EVIDENCE).* LS4 with its default choice rule never fails on:
  - n ≤ 3: every profile, ties included (300 million strict profiles; 24.7·10⁹ tied ones);
  - n = 4 with one or two 4-good agents: every profile (7,247,232 and 724,847,616);
  - large random samples of every other n = 4 and n = 5 certificate class,

  except on 20 of the 21.9 million sampled profiles of pure n = 4 cores (§5). They are in 10 cores with m = 7, 8, 9 (4, 5 and 1 cores). There LS4 stops at a state that no M1, R or X move improves and that no placement completes. Of the 19 logged such states, 8 are dead ends and 11 still admit coalition moves (brute force).
- *Not proved:* a polynomial bound on the running time. The number of moves is linear, but the implementation finds exchange cycles and the Phase-2 split by enumeration.

## 0. Setting and notation

An instance with additive values; R_i = {g : v_i(g) > 0}, d_i = |R_i| ≤ 4. The algorithm and Theorem 1 need nothing
else. TP₄ is stated for k = 4 cores (K4.CORE in `k4/SCOUT.md`): d_i ∈ {3, 4}, every agent strictly balanced, at most
d_i − 2 private goods, every good valued by someone; connectivity is not needed.

*Strict types.* The algorithm runs on V_i = 32 v_i + w_i, with w_i(g) = 2^(position of g in R_i) on R_i and 0 elsewhere,
for integer values v_i (every type has an integer representative in [1, 16]⁴, K4.OT).
- V_i is *strict*: its 2^{d_i} subset sums on R_i are distinct, since the parts w_i(S) < 32 are distinct.
- V_i *refines* v_i: v_i(S) > v_i(T) implies V_i(S) > V_i(T).
- Conversely V_i(S) ≥ V_i(T) implies v_i(S) − v_i(T) ≥ (w_i(T) − w_i(S))/32 > −1/2, so v_i(S) ≥ v_i(T), because the values are integers. Hence **an allocation that is EFX₀ for V is EFX₀ for v**, since EFX₀ is a conjunction of weak inequalities v_i(A) ≥ v_i(B).
- The algorithm only compares subset sums of one agent. So its run depends only on the strict type of V (the order of its subset sums on R_i).

For real values, K4.TIE reduces tied profiles to strict ones. §5 covers the tied profiles of n ≤ 3 cores directly.

*Partial allocations.* Y assigns each good to at most one agent; U is the pool (unallocated goods).
- σ_i := V_i(Y_i).
- Y is *junk-free* if Y_i ⊆ R_i for all i.
- The *threat* of a nonempty bundle B to agent i is θ_i(B) := max_{g∈B} V_i(B ∖ {g}). It equals V_i(B) if B contains a good outside R_i, and V_i(B) − min_{g∈B} V_i(g) otherwise.
- Agent i is *safe* if σ_i ≥ θ_i(Y_j) for every j ≠ i with Y_j ≠ ∅. Y is EFX₀ if every agent is safe; the pool imposes nothing.
- A set Z is *threat-free for agent h* if θ_x(Z) ≤ σ_x for every x ≠ h.
- i *envies* j if V_i(Y_j) > σ_i. A *source* is an agent nobody envies.

*Levels.* ℓ_i := #{T ⊆ R_i : V_i(T) < σ_i} ∈ {0, …, 2^{d_i} − 1} for junk-free Y. It strictly increases with σ_i, since V_i is strict. Φ := Σ_i ℓ_i ≤ Σ_i (2^{d_i} − 1) ≤ 15n.

## 1. Two general lemmas

**Lemma A (threat bound; `proofs/local_search.md` Lemma 3, which never uses k).**
- θ_i is monotone: ∅ ≠ B′ ⊆ B implies θ_i(B′) ≤ θ_i(B).
- Let Y be EFX₀ and let Y′ be a partial allocation such that
  - (i) V_h(Y′_h) ≥ σ_h for every h, and
  - (ii) every nonempty Y′_j is contained in a bundle of Y, or is threat-free for j with respect to Y.

  Then Y′ is EFX₀.

*Proof.* Monotonicity: for B = B′ ∪ D, max_{g∈B} V(B ∖ g) ≥ max_{g∈B′} V(B ∖ g) ≥ max_{g∈B′} V(B′ ∖ g).

Fix h and j ≠ h with Y′_j ≠ ∅.
- If Y′_j ⊆ Y_l, then θ_h(Y′_j) ≤ θ_h(Y_l). This is ≤ σ_h: if l ≠ h because Y is EFX₀, and if l = h because θ_h(B) ≤ V_h(B).
- Otherwise θ_h(Y′_j) ≤ σ_h by (ii).

In both cases θ_h(Y′_j) ≤ σ_h ≤ V_h(Y′_h). ∎

**Lemma B (envy is inside R).** If Y is EFX₀ and i envies j, then Y_j ⊆ R_i.

*Proof.* Otherwise Y_j contains a good g ∉ R_i, and θ_i(Y_j) ≥ V_i(Y_j ∖ g) = V_i(Y_j) > σ_i. ∎

## 2. Algorithm LS4

Start with Y_i = ∅ for all i and U = M. Repeat:
1. **(M1, single-agent rebundle)** Some agent h has a set Z ⊆ R_h ∩ (Y_h ∪ U) with V_h(Z) > σ_h that is threat-free for h. Then Y_h := Z; the goods of Y_h ∖ Z go to U.
2. **(R, rotation)** The envy graph has a cycle. Each agent on it takes the bundle of the agent it envies.
3. If U = ∅, output Y. If Phase 2 below applies, apply it and output the result.
4. **(X, exchange cycle)** There are distinct agents i_0, …, i_{L−1}, L ≥ 2, and pairwise disjoint sets Z_t ⊆ R_{i_t} ∩ (Y_{i_t} ∪ Y_{i_{t+1}} ∪ U) (indices mod L) such that each Z_t meets Y_{i_{t+1}}, V_{i_t}(Z_t) > σ_{i_t}, and Z_t is threat-free for i_t. Then each i_t takes Z_t; every other good of these agents' bundles goes to U. So an agent may keep part of its own bundle and take part of the next one; the rest of both goes to the pool.
5. Otherwise stop: **failure**.

**Phase 2.** Let U ≠ ∅.
- (a) If some bundle Y_e is empty: Y_e := U.
- (b) Else, if some source s values no good of U and Y_s ∪ U is threat-free for s: Y_s := Y_s ∪ U.
- (c) Else, if there are a source s* and J ⊆ U ∖ R_{s*} with Y_{s*} ∪ J threat-free for s*, and the goods of U ∖ J can be given one each to distinct sources s ≠ s* with u ∉ R_s and Y_s ∪ {u} threat-free for s: do so (*DM*: a dump plus solo goods).
- (d) Else, if some assignment of each good of U to a source that does not value it gives an EFX₀ allocation (found by exhaustive search): use it. This fallback is needed rarely (§5).

*Choice points.* Any valid choice may be taken. The implementation `k4/ls4alg.c` takes, in step 1, the first agent in index order with a move and its least valuable improving Z. In step 2 it takes the first cycle found. In step 4 it takes the first cycle in order of length, then agent set, then order, then sets. In Phase 2 it takes the first s, s*, J and matching found. Theorem 1 holds for every choice; the evidence of §5 is for this rule.

Every rule compares subset sums of single agents only, so the run is determined by the profile of strict types.

## 3. Soundness and termination

**Theorem 1.**
- (i) Every state Y of LS4 is a junk-free EFX₀ partial allocation.
- (ii) Every move of steps 1, 2 and 4 raises Φ by at least 1. So LS4 performs at most Σ_i (2^{d_i} − 1) ≤ 15n₄ + 7n₃ moves.
- (iii) Every output is a complete allocation that is EFX₀ for V, hence for v.
- (iv) LS4 fails only at a state Y with U ≠ ∅ where no M1, R or X move applies and none of (a)–(d) applies.

*Proof.* The empty allocation is junk-free and EFX₀.

(i) and (ii):
- *M1.* Z ⊆ R_h, so no junk is created. Only h's bundle changes, and h's value rises. Z is threat-free for h, so Lemma A applies: every other bundle is an old bundle. ℓ_h rises and the other levels are unchanged.
- *R.* By Lemma B each agent on the cycle receives a subset of its own relevant goods. Each strictly improves, and the new bundles are old bundles, so Lemma A applies.
- *X.* The Z_t are disjoint subsets of R_{i_t}. Each mover strictly improves, the others keep their bundles, and each new bundle Z_t is threat-free for its holder, so Lemma A applies.

In each case Φ strictly increases and is bounded, so there are at most Σ_i (2^{d_i} − 1) moves.

(iii) *Phase 2 (d)* gives an EFX₀ allocation by definition. *Phase 2 (b), (c).* Every receiver r gets goods outside R_r, so all values σ_h are unchanged. Consider h and a bundle X_j with j ≠ h.
- If j received nothing, θ_h(X_j) = θ_h(Y_j) ≤ σ_h, since Y is EFX₀.
- If j received, θ_h(X_j) ≤ σ_h by the threat-freeness condition.

So X is EFX₀ and complete.

*Phase 2 (a)* is applied only after step 1 found no move, so Lemma 2 below applies.
- V_e(u) ≤ σ_e = 0 for every u ∈ U by (F1), so e values nothing in U.
- For h ≠ e: θ_h(U) ≤ V_h(U) = V_h(U ∩ R_h) ≤ σ_h by (F2).
- Every other bundle and every value is unchanged.

(iv) is the case analysis of the loop. ∎

**Lemma 2 (what the absence of M1 moves gives; uses d_h ≤ 4).** Let Y be junk-free and EFX₀ with no M1 move. Then:
- (F1) V_h(u) ≤ σ_h for every agent h and every u ∈ U;
- (F2) V_h(U ∩ R_h) ≤ σ_h for every agent h.

*Proof.* (F1) Otherwise h can take Z = {u}: θ_x({u}) = 0 for every x, a valid M1 move.

*Pairs.* If P ⊆ U ∩ R_h has two goods and V_h(P) > σ_h, then h can take P. By (F1), θ_x(P) is the larger of x's two single values, which is ≤ σ_x. This would be a valid M1 move. So V_h(P) ≤ σ_h.

(F2) If U ∩ R_h ≠ ∅, then σ_h > 0 by (F1), so Y_h ≠ ∅ and W := U ∩ R_h has at most 3 goods. Let x ≠ h.
- If W ⊄ R_x, then θ_x(W) = V_x(W ∩ R_x), and |W ∩ R_x| ≤ 2, so it is ≤ σ_x by (F1) and the pair bound.
- If W ⊆ R_x, then θ_x(W) = max_g V_x(W ∖ g) is the value of a set of at most two goods of U ∩ R_x, ≤ σ_x by (F1) and the pair bound.

So W is threat-free for h, and V_h(W) > σ_h would give a valid M1 move. ∎

## 4. Stable states: a dead end, three goods, one source

**Conjecture TP₄ (refuted).** "Let Y be a junk-free EFX₀ partial allocation of a k = 4 core with U ≠ ∅, and suppose no M1, R or X move applies. Then Phase 2 (a), (b) or (c) applies." (With (d) in place of (c) the statement is also false: Proposition 7.)

TP₄ would have made LS4 correct for every choice of moves, and with K4.CORE and K4.TIE it would have given TARGET₄. It is false.

**Proposition 7 (a dead end; n = 4, m = 7).** Take the pure core with agents
- 0: goods 0:8, 2:10, 5:6, 6:3;
- 1: goods 0:5, 3:2, 4:4, 6:8;
- 2: goods 1:1, 2:8, 4:6, 6:4;
- 3: goods 1:2, 3:3, 5:6, 6:10;

and let Y = {2} | {6} | {1, 4} | {3, 5}, U = {0}. Then:
- (i) Y is reached from the empty allocation by 15 M1 moves (LS4's own run);
- (ii) no M1, R, X or coalition move applies, and no placement of good 0 gives an EFX₀ allocation;
- (iii) no complete EFX₀ allocation X has V_i(X_i) ≥ σ_i for all i.

*Proof.* By computation from the raw definition, in two independent programs: `k4/ls4alg.c` with `-DTRACE`, and the plain-Python brute force `k4/ls4_attempts.py` (all 4⁷ allocations; `results/k4_ls4_attempts.log`).

The core of (ii) by hand: the sources are agents 2 and 3 (agent 2 envies agent 0, agent 3 envies agent 1). Good 0 at agent 2 gives agent 1 the threat 5 + 4 = 9 > 8, and at agent 3 it gives agent 0 the threat 8 + 6 = 14 > 10. Each claim compares subset sums of one agent, so it holds for every valuation with these strict types. ∎

By (iii), a two-phase search that may reach Y cannot succeed, whatever moves it makes afterwards, as long as each move leaves every agent at least as well off. Single-agent rebundles reach Y, so every Pareto move set containing them can reach Y under some choices.

The dead end is a matter of choices. The same profile succeeds under the alternative rule `-DALT` (most valuable rebundle, rotating agent order, longest cycles first), and every profile has *some* successful Pareto path: an allocation's valued part is a junk-free EFX₀ partial allocation, and a coalition move can jump to it from the empty allocation. But neither rule tried avoids dead ends in general: the default rule fails on 20 and `-DALT` on 23 of 21.9 million sampled pure n = 4 profiles (§5). A local-search proof needs a choice rule with a *proof* that dead ends are avoided, or non-Pareto moves.

The shape of (c) is also forced, in the following sense. Some state stable under every Pareto move, even every coalition move, admits no single dump (b). The only complete EFX₀ allocation that is at least as good for everyone as that state splits the pool over two sources (`attempts/k4-ls-single-dump.md`). So Phase 2 must be able to split the pool, as LS2's matching does at k = 3.

**Proposition 3 (three goods; conditional on `proofs/local_search.md` §4).** If every agent of the core has three goods, TP₄ follows from Claims 2–4 of Theorem C of `proofs/local_search.md`.

*Proof.* Every step of LS2 is an M1, R or X move of LS4:
- LS2's steps 1, 3, 4 and 5 give EFX₀ results (Claim 1) in which one agent takes a set of its own goods from its bundle and the pool, so they are M1 moves.
- Step 2 is R.
- Step 6 (champion path s = t_0 → … → t_r = i, with i taking {u, y} ⊆ Y_s ∪ U) and step 7 (the cycle C of Claim 3) are X moves:
  - each agent takes a subset of its successor's bundle, plus at most one pool good, that meets the successor's bundle;
  - the taken sets are disjoint and every agent strictly improves;
  - each new bundle is either an old bundle, whose threat to anyone other than its old holder is bounded because Y is EFX₀, and to its old holder by θ ≤ V, or a pair {u, y} of two goods nobody envies.

Now let Y be as in TP₄. If some bundle is empty, (a) applies. Otherwise steps 1–7 of LS2 do not apply, so by Claims 2 and 4, LS2's Phase 2 (b) gives a complete EFX₀ allocation. In it, a one-good source s* that values no good of U (Claim 2 (e)) receives U ∖ D(T), and each u ∈ D(T) goes alone to a distinct one-good source M(u) ≠ s* that does not value it. Every bundle of an EFX₀ allocation is threat-free for its holder, and the σ_h are unchanged. So this placement is a DM placement, and (c) applies. ∎

**Lemma 5 (champions; the k = 4 form of LS2's step 6 and Claim 2 (h)).** Let Y be junk-free and EFX₀, with no M1 and no X move. Let s be a source at which the single dump (b) fails, that is, s values a good of U, or Y_s ∪ U is not threat-free for s. Among all pairs (h, Z) of an agent h and a set Z ⊆ (Y_s ∪ U) ∩ R_h with V_h(Z) > σ_h, take one with |Z| minimum. Then:
- Z is threat-free for h;
- Z meets both Y_s and U;
- h ≠ s;
- h is not reachable from s by an envy path.

*Proof.* Such pairs exist.
- If s values u ∈ U, take (s, Y_s ∪ {u}).
- Otherwise V_h((Y_s ∪ U) ∖ g) > σ_h for some h ≠ s and g. Take (h, ((Y_s ∪ U) ∖ g) ∩ R_h).

*Threat-free.* For every agent x and g ∈ Z, the set Z ∖ g has fewer goods than Z. By minimality V_x(Z ∖ g) ≤ σ_x, so θ_x(Z) ≤ σ_x.

*Z meets U.* If Z ⊆ Y_s, then h ≠ s (since V_s(Z) ≤ σ_s), and h envies s, contradicting that s is a source.

*Z meets Y_s.* If Z ⊆ U, then V_h(Z) ≤ V_h(U ∩ R_h) ≤ σ_h by (F2) of Lemma 2.

*h ≠ s.* If h = s, then Z ⊆ R_s ∩ (Y_s ∪ U) is an M1 move.

*h is not reachable.* Suppose s = t_0 → t_1 → … → t_r = h is a simple envy path, r ≥ 1. Then the following is an X move: each t_q (q < r) takes Y_{t_{q+1}}, and h takes Z.
- Y_{t_{q+1}} ⊆ R_{t_q} by Lemma B, and t_q strictly improves.
- Y_{t_{q+1}} is threat-free for t_q: for x ≠ t_{q+1} because Y is EFX₀, and for x = t_{q+1} because θ ≤ V.
- Z meets Y_s = Y_{t_0}, and no other agent takes from Y_{t_0}.
- The taken sets are disjoint. ∎

**Proposition 4 (one source).** If Y is as in TP₄ and has exactly one source, then (a) or (b) applies. So TP₄ holds for such states, for any instance with d_i ≤ 4. The dead end of Proposition 7 has two sources.

*Proof.* If some bundle is empty, (a) applies. Otherwise the envy graph is acyclic, since no R move applies. A backward walk from any agent along envy edges ends at a source, which is s. So every agent is reachable from s. By Lemma 5 the single dump at s cannot fail. ∎

**Lemma 6 (the Phase-2 constraints).** Let Y be junk-free and EFX₀, s a source, and 𝓔(s) the family of sets E ⊆ Y_s ∪ U that some agent envies (V_h(E) > σ_h). Then:
- (i) For J ⊆ U ∖ R_s, the set Y_s ∪ J is threat-free for s iff no member of 𝓔(s) is a proper subset of Y_s ∪ J.
- (ii) Every inclusion-minimal E ∈ 𝓔(s) is contained in R_h for each agent h envying it, and is threat-free for h. If no M1 move applies, E meets both Y_s and U, and h ≠ s.

*Proof.* (i) Y_s ∪ J is not threat-free iff (Y_s ∪ J) ∖ g ∈ 𝓔(s) for some x ≠ s and g. Since 𝓔(s) is closed upward within Y_s ∪ U, this holds iff some E ∈ 𝓔(s) satisfies E ⊆ (Y_s ∪ J) ∖ g for some g, that is, E is a proper subset of Y_s ∪ J. The envier is not s, because s values no good of J and V_s(E ∩ Y_s) ≤ σ_s.

(ii) Removing a good outside R_h from E keeps h's value, so minimality gives E ⊆ R_h. No proper subset of E is envied by anyone, so θ_x(E) = max_g V_x(E ∖ g) ≤ σ_x for every x. The rest is as in Lemma 5. ∎

So Phase 2 must choose a dump s* and a set L ⊆ U of pool goods to remove, such that:
- L meets the pool part E ∩ U of every minimal envied set E at s*, except that E = Y_{s*} ∪ J is allowed;
- the goods of L can be matched to other sources, alone.

Phase 1's exchange cycles instead use disjoint pool parts of minimal envied sets at different sources, or keep own goods. At k = 3 every pool part is a single good: LS2's dirty goods. That is why a system of distinct representatives decides between the two there. At k = 4 pool parts have up to three goods, so "meeting every pool part" involves a choice. The Hall-type duality that would decide between a DM placement and an exchange cycle is not known.

So a stable state without a placement needs at least two sources, the dump fails at each of them, and each source's champion is reachable only from other sources. At k = 3, LS2 closes this case with a system of distinct representatives: the champion sets there differ in a single pool good per source, so either they can be chosen disjoint, giving an augmented cycle, or Hall's condition fails and a matching gives the placement. At k = 4, champion sets at different sources can need the same pool goods (`attempts/k4-ls-exchange-no-keep.md`), and the repair keeps own goods instead. An exchange argument that handles this is what is missing.

**Where the k = 3 proof stops at four goods.** Each of the following is observed in LS4's stable states:
- *Lemma 1 of `proofs/local_search.md` fails.* A 4-good agent's safety is not a condition on single goods: it compares sets, type by type (K4.OT: 12 behaviourally distinct types per ranking).
- *Lemma 2 fails.* An agent may envy a bundle of two or three goods. A source with two goods may envy. So backward envy walks need not end at one-good sources.
- *m ≤ 3n.* One-good sources need not exist.
- *Placement constraints are not per good.* At a source s, a minimal set J ⊆ U such that Y_s ∪ J is not threat-free can have one, two or three goods. Two-good sets whose goods are both valued by the envier occur at n = 3 (`k4/ls4.c`, counters B1, B2a, B2b, B3). At k = 3 every such constraint is "u must sit alone next to the source's single good".
- *Exchange cycles must keep own goods and can be long.* Cycles without keep fail at n = 3 (`attempts/k4-ls-exchange-no-keep.md`). Length ≤ 2 fails at n = 3 (`attempts/k4-ls-short-cycles.md`). Cycles in which at most one agent takes pool goods fail at n = 5 (§6).

## 5. Computational evidence (not part of any proof)

`k4/ls4alg.c` implements LS4 exactly as in §2. The driver `k4/ls4alg_run.py` takes the cores from the certificate files `results/k4_certs_*.json.gz` (complete core lists by the orbit count of `k4/check4.py`) and the types from `k4/check4.py`'s `core_domains`. After every Phase-1 step the program checks junk-freeness, EFX₀ and the rise of Φ. It checks every output for completeness, EFX₀ under V, and EFX₀ by the raw definition v_i(X_i) ≥ v_i(X_j) − v_i(h) with the integer representative.

*Ties.* A tied profile runs exactly like the strict profile of its perturbations (§0). With `--ties`, every balanced weak type of `core_domains(..., ties=True)` is attached to the strict type of its perturbation 32 v + w, and the output is also checked by the raw definition against every attached tied type. So one strict run covers every tied profile that maps to it. Every tied type maps into the strict domain (asserted).

*Sensitivity test* (`results/k4_ls4_sensitivity.log`). Without exchange cycles (`-DNOX`) the n = 2 run reports failures. So does a Phase 2 that dumps U unchecked (`-DBADDUMP`), and the raw check reports it too. Both runs have exit status 1.

**Results** (LS4 with its default rule; "profiles" are strict type profiles; the certificate files' core lists).

| class | cores | profiles | how | failures | notes | log |
|---|---|---|---|---|---|---|
| n = 2 | 5 | 189,216 (all tied profiles too) | exhaustive | 0 | X used 732 times; dump always single | `results/k4_ls4_2_ties.log` |
| n = 3 | 51 | 299,837,376 (all 24,690,461,987 tied profiles too) | exhaustive | 0 | X used 3,474,924 times (cycles of length 2, 3); DM split needed 1,232 times; the exact-search fallback never | `results/k4_ls4_3_ties.log` |
| n = 4, one 4-good agent | 135 | 7,247,232 | exhaustive | 0 | DM split 77,900 times | `results/k4_ls4_4_n4_1.log` |
| n = 4, two 4-good agents | 309 | 724,847,616 | exhaustive | 0 | DM split 7,152,104 times; exact-search fallback 5,632 times | `results/k4_ls4_4_n4_2.log` |
| n = 4, three 4-good agents | 339 | 33,900,000 | 100,000 random per core | 0 | | `results/k4_ls4_4_sample.log` |
| n = 4, pure | 219 | 21,900,000 | 100,000 random per core | **20** (10 cores: m = 7, 8, 9 with 4, 5 and 1 cores; 13, 6 and 1 failures) | stable states where LS4 stops without a placement; 8 of the 19 logged are dead ends (§4), 11 admit coalition moves. Rule `-DALT`: 23 failures on the same sample (`results/k4_ls4_4_pure_alt_sample.log`, `attempts/k4-ls-alt-rule.md`) | `results/k4_ls4_4_sample.log` |
| n = 5, one 4-good agent | 1,735 | 34,700,000 | 20,000 random per core | 0 | | `results/k4_ls4_5_n4_1_sample.log` |
| n = 5, two 4-good agents | 5,468 | 54,680,000 | 10,000 random per core | 0 | exact-search fallback needed 839 times (DM shape failed) | `results/k4_ls4_5_n4_2_sample.log` |

In the n = 4 samples with three or four 4-good agents the exact-search fallback was needed 1,938 times: states where a junk placement exists but not in DM shape.

*Every stable state, not only those LS4 reaches* (`k4/ls4_allstates.c`). All junk-free EFX₀ partial allocations of each profile are enumerated. For those with a nonempty pool and no M1, R or X move, Phase 2 is checked.
- n = 2, exhaustive: 24,508 stable states, all completed by a single dump (`results/k4_ls4_allstates_2.log`). Without X, it reports failures.
- n = 3, 510,000 random profiles: 191,274 stable states, all completed by a single dump (`results/k4_ls4_allstates_3_sample.log`).

*Dead ends* (`k4/ls4_deadend.c`). These are junk-free EFX₀ partial allocations that no complete EFX₀ allocation weakly dominates, reachable or not.
- n = 2: none, exhaustive (`results/k4_ls4_deadend_2.log`).
- n = 3: none in 1,020,000 random profiles (`results/k4_ls4_deadend_3_sample.log`).
- n = 4: none in 424,000 random profiles of the cores with m ≤ 6 (`results/k4_ls4_deadend_4_m6_sample.log`). With m ≤ 7, 34 of 1,000,000 random profiles have one (`results/k4_ls4_deadend_4_sample.log`), each reachable from the empty allocation by single-agent rebundles. Rerun on the 288 cores with m = 7 (`results/k4_ls4_deadend_4_m7_sample.log`, which lists them), 34 of 576,000 profiles have one, in 20 cores: 8 pure, 7 with three 4-good agents, 5 with two. So dead ends exist in classes where LS4's default rule never failed; LS4 simply does not reach them there.

So the smallest dead end has n = 3 or n = 4. An exhaustive search at n = 3 would take about 13 CPU-hours with `k4/ls4_deadend.c`; it was not run.

## 6. Variants that fail (`attempts/k4-ls-*.md`; replayed by `python3 k4/ls4_attempts.py`)

`k4/ls4_attempts.py` is an independent brute force in plain Python, working from the raw definition and the explicit integer values. It enumerates every move of each family and every completion.

| variant | smallest failing configuration found | file |
|---|---|---|
| LS4 itself, with arbitrary choices (conjecture TP₄) | n = 4, m = 7 (pure core): a *dead end* reached by 15 M1 moves, which no complete EFX₀ allocation weakly dominates (Proposition 7) | `attempts/k4-ls-dead-end.md` |
| Phase 1 = M1 and R only | n = 2, m = 4: a stable state with no completion at all | `attempts/k4-ls-no-exchange.md` |
| exchange cycles without keeping own goods (includes the k = 3 champion cycles) | n = 3, m = 6: a stable state with no completion at all | `attempts/k4-ls-exchange-no-keep.md` |
| Phase 2 = one dump only | n = 4, m = 7: stable even under all coalition moves; the only EFX₀ completion splits the pool | `attempts/k4-ls-single-dump.md` |
| exchange cycles of length ≤ 2 | n = 3, m = 5: a stable state with no completion at all | `attempts/k4-ls-short-cycles.md` |
| exchange cycles with at most one pool-using agent | n = 5, m = 8: a stable state with no completion at all | `attempts/k4-ls-one-pool-agent.md` |
| Phase 2 = "clean" placement plus solo matching, ignoring values | n = 3, m = 5: a stable state that a single dump completes but the clean rule does not | `attempts/k4-ls-clean-placement.md` |
| Phase 2 (c) by the simplest polynomial split (§7) | n = 4, m = 6: a stable state with dump-plus-solo placements that the split misses | `attempts/k4-ls-simple-split.md` |
| Phase 2 (d), any junk placement, in place of (c) | the dead end of Proposition 7 (n = 4, m = 7) has no placement at all | `attempts/k4-ls-exact-placement.md` |
| LS4 with the choice rule `-DALT` | n = 4, m = 7: 5 moves reach a stable state with no completion (not a dead end: coalition moves exist) | `attempts/k4-ls-alt-rule.md` |

Each configuration is replayed by `k4/ls4_attempts.py`. The failure counts are single-implementation sample counts from `k4/ls4.c` (the exploratory engine, `k4/ls4_run.py`) or from `k4/ls4alg.c`:
- length ≤ 2: 6,432 failures in 5,100,000 random n = 3 profiles, and 302 in 219,000 pure n = 4 ones;
- at most one pool-using agent: 3 in 5,468,000 n = 5 profiles;
- clean placement: 8,821 failures in 304,901 stable n = 3 states;
- simplest split: completes 0 of 79 sampled n = 5 states that need a split;
- `-DALT`: 23 in 21,900,000 pure n = 4 profiles.

## 7. Complexity

- The number of Phase-1 moves is at most Σ_i (2^{d_i} − 1) ≤ 15n (Theorem 1).
- Steps 1 and 2 and Phase 2 (a), (b) take polynomial time.
- The implementation finds step 4's exchange cycles and Phase 2 (c)'s split by enumeration: over agent sequences and over subsets of the pool.
  - Cycles of length up to 5 occur at n = 5 (`results/k4_ls4_5_n4_2_sample.log`, counters L2–L5), and capping the length at 2 fails already at n = 3 (§6).
  - The simplest polynomial split fails: keep at the dump every pool good that is individually harmless there and match the rest. It never worked in the 79 sampled n = 5 states that needed a split (`k4/ls4.c`, counter dm1), because pair constraints bind at the dump (Lemma 6).
  - Edge-local validity (threat-freeness of each Z_t with respect to the old values, which is how X is defined) loses nothing in the samples. So an exchange cycle is a cycle in a product graph on (agent, kept part of its bundle). The only non-local constraint is that the pool goods used by different agents must be disjoint.
- Whether an improving exchange cycle, and a DM placement, can always be found in polynomial time is open. So is whether a Hall-type argument as at k = 3 decides between them. Both questions matter only for a choice rule that avoids dead ends (§4).

## 8. Status

- Theorem 1, Lemmas A, B, 2, 5, 6 and Proposition 4 (no failure with one source): written proofs here, pending review (ledger K4.LS.SOUND, K4.LS.ONE, CONJECTURE until reviewed).
- Proposition 3 (LS4 never fails on three-good cores): conditional on Theorem C of `proofs/local_search.md`, pending review (K4.LS.K3).
- Proposition 7, a dead end at n = 4, m = 7: by two independent computations (K4.LS.DEAD, EVIDENCE under the owner's claim policy for new rows). It refutes conjecture TP₄ and every two-phase Pareto local search with arbitrary choices whose Pareto move set contains single-agent rebundles.
- LS4 with its default choice rule: the evidence of §5 (K4.LS.RUN).
- Weaker variants fail: §6 (K4.LS.VAR).
- Open:
  - a choice rule, or a non-Pareto move, with a proof that dead ends are avoided;
  - polynomial-time search for exchange cycles and splits.
