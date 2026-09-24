# EFX₀ in cores by local search: moves, potential, and where the argument stops

Workstream `proof/local-search`. This is a route to TARGET that does not go through conjecture D. The route keeps a partial EFX₀ allocation of a core and applies moves that raise a potential, as in the existence proofs for identical valuations, three agents, multigraphs and hypergraphs of girth ≥ 4 listed in `proofs/citations.md`. None of those papers was read for this work; their methods are known here only from the summaries in `proofs/citations.md`, and nothing below depends on them.

**Summary.**
- Proved: in a core, partial EFX₀ is ordinal and local (Lemma 1). Envy between bundles has a rigid form (Lemma 2). A single threat bound covers all the moves used (Lemma 3).
- Proved (Theorem A): if every allocated good is held by an agent that values it, the four elementary moves (fill an empty bundle, swap for an unallocated good, rotate an envy cycle, add an unallocated good to an unenvied singleton) never get stuck.
- So the only obstruction is *junk*: goods held by agents that do not value them. Two ways of dealing with junk were tested exhaustively.
  - **One phase** (§4): junk is part of the state, with the potential (sum of levels, number of allocated goods). With seven move types, no partial EFX₀ state of any connected core with n ≤ 5 is stuck. At n = 6 the search can get stuck: a run of 8 potential-raising moves from the empty allocation ends in a stuck state (core 687, m = 9; replayed by an independent Python implementation). So this move set and this potential do not prove TARGET.
  - **Two phases** (§5): Phase 1 moves junk-free partial allocations by Pareto improvements and provably terminates. Phase 2 places the remaining goods as junk. TARGET follows from one statement, the *placement conjecture* TP (Theorem B). §5 reduces TP to a per-good condition on source bundles (Lemmas 5–7). TP holds for every connected core with n ≤ 6 (exhaustive; C, cross-checked in Python for n ≤ 4). With only single-agent and champion-path moves it fails at n = 6, again on core 687; augmented envy cycles repair it.
- Open: TP for general n. §6 lists where the three-goods restriction enters, and §7 lists the exact remaining gap.

Everything in §1–§3 and the lemmas of §5 are proved here and were re-read. Computations are evidence for the conjectures and are listed with their logs; they are not part of any proof (PROMPT.md §5 rule 3).

## 0. Notation

A core as in PROMPT.md §3: every agent i values exactly three goods R_i = {a_i, b_i, c_i}, v_i(a_i) > v_i(b_i) > v_i(c_i) > 0 (ties are handled as in L5 (iv)), and is balanced: v_i(a_i) < v_i(b_i) + v_i(c_i). Every good is valued by someone. L4 gives m ≤ 2n.

A *partial allocation* X gives each good to at most one agent; X_i is agent i's bundle and P, the *pool*, is the set of unallocated goods. Agent i is *safe* if v_i(X_i) ≥ v_i(X_j ∖ {g}) for every j ≠ i and every g ∈ X_j. X is EFX₀ if every agent is safe. The pool imposes no constraint, so the empty allocation is EFX₀. A good is *alone* if it is the only good in its bundle, and *free* if it is alone or in the pool. S_i := X_i ∩ R_i is the set of i's own goods it holds. A good g ∈ X_i ∖ R_i is *junk* (for its holder). X is *junk-free* if it has no junk.

Agent i *envies* a good x if x ∈ R_i and v_i(x) > v_i(X_i), and envies agent j if v_i(X_j) > v_i(X_i). The *envy graph* has an edge i → j when i envies j. A *source* is an agent nobody envies. An agent is *rich* if |S_i| ≥ 2 and an *a-holder* if S_i = {a_i}.

By L5 (i) the eight subset sums of R_i are ordered 0 < c < b < a < b+c < a+c < a+b < a+b+c. The *level* ℓ_i(X) ∈ {0, …, 7} is the position of v_i(S_i) in this chain. Levels are ordinal: they depend only on i's ranking. Rich means ℓ_i ≥ 4.

θ_i(B) := v_i(B) − min_{g ∈ B} v_i(g) for a nonempty bundle B, the *threat* of B to i (F1 in `proofs/lemmas.md`). Agent i is safe iff v_i(X_i) ≥ θ_i(X_j) for all j ≠ i with X_j ≠ ∅. θ_i(B) = 0 if |B| = 1.

## 1. Partial EFX₀ in a core is ordinal and local

**Lemma 1.** In a partial allocation of a core, agent i is safe iff
- (F) every good that i envies is free, and
- (Q) if S_i = {a_i}, then b_i and c_i are not together in a bundle of at least three goods.

Concretely, (F) says: if S_i = ∅, then a_i, b_i and c_i are free; if S_i = {c_i}, then a_i and b_i are free; if S_i = {b_i}, then a_i is free. It says nothing if S_i = {a_i} or i is rich. So safety depends only on i's ranking, on S_i, and, for each other bundle, on which of i's goods it contains and on its size. EFX₀ of a partial allocation of a core is therefore ordinal.

*Proof.* Write a, b, c for i's goods and values. The goods of R_i ∖ S_i lie in other bundles or in the pool; pool goods threaten nothing. Take j ≠ i and U = X_j ∩ R_i ≠ ∅. By F1, θ_i(X_j) = v(U) if X_j contains a good outside R_i. If X_j = U, then θ_i(X_j) = 0 for |U| = 1, and v(U) minus its smallest element for |U| ≥ 2. Go through S_i.
- |S_i| ≥ 2: v(S_i) ≥ b + c, and every other bundle meets R_i in at most one good, worth at most a < b + c. Safe, and i envies no good.
- S_i = {a}: i envies no good. If b and c lie in different bundles, every threat is at most b < a. If both lie in X_j: X_j = {b, c} gives θ = b < a; |X_j| ≥ 3 gives a good outside R_i, so θ = b + c > a. This is (Q).
- S_i = {b}: i envies exactly a. If a is free, the threats are at most c < b (only c can sit in a bundle of ≥ 2 goods, contributing at most c). If a is in a bundle X_j of ≥ 2 goods, then X_j = {a, c} (θ = a) or X_j contains a good outside R_i (θ ≥ a), and a > b. So i is safe iff a is free.
- S_i = {c}: i envies a and b. If both are free, no bundle of ≥ 2 goods other than X_i contains a good of R_i (c is i's), so every threat is 0. If a or b lies in a bundle X_j of ≥ 2 goods, then X_j = {a, b} (θ = a) or X_j contains a good outside R_i (θ ≥ b); either way θ > c. So i is safe iff a and b are free.
- S_i = ∅: v(S_i) = 0, and any bundle with ≥ 2 goods containing a good of R_i has positive threat. So i is safe iff a, b, c are free. ∎

This is L5 (iii) with "alone" replaced by "free". Unallocated goods behave exactly like alone goods. The rule was checked against the raw definition with three balanced realizations on 281,250 local configurations: agent 0 values goods 0, 1, 2 under each of the 6 rankings, goods 3, 4, 5 are worthless to it, and every good is in the pool or with one of four agents. There were 0 mismatches (`python src/local_search.py lemma1`, log `results/ls_lemma1.log`).

**Lemma 2 (envy in an EFX₀ partial allocation).** Let X be EFX₀ and let k envy j. Then either X_j = {x} is a singleton and k envies x, or X_j = {b_k, c_k} exactly and S_k = {a_k}. In particular:
- (a) a rich agent envies no agent and no good;
- (b) an agent with a bundle of ≥ 2 goods that is envied holds exactly the bottom pair {b_k, c_k} of an a-holder k.

*Proof.* If k envies a good x ∈ X_j, then x is free by (F), so X_j = {x}. Otherwise every good of X_j ∩ R_k is worth at most v_k(X_k), and v_k(X_j) > v_k(X_k) forces |X_j ∩ R_k| ≥ 2. If k is rich, X_j meets R_k in at most one good. If S_k = {b_k} or {c_k}, at most one good of R_k outside S_k is worth at most v_k(X_k) (c_k, or none). If S_k = ∅, no good of R_k is worth at most 0. So S_k = {a_k} and X_j ∩ R_k = {b_k, c_k}. By (Q), X_j has exactly two goods. ∎

**Lemma 3 (threat bound; all moves below are instances).** Let X be EFX₀ and let X′ be a partial allocation such that
- (i) v_h(X′_h) ≥ v_h(X_h) for every agent h, and
- (ii) every nonempty bundle of X′ is contained in a bundle of X, or is a set Z with θ_h(Z) ≤ v_h(X_h) for every agent h.

Then X′ is EFX₀. (Condition (ii) holds for Z if |Z| ≤ 1, or if Z = {g, y} where no agent envies g or y in X.)

*Proof.* θ is monotone: if ∅ ≠ B′ ⊆ B, then θ_h(B′) ≤ θ_h(B). Write B = B′ ∪ D with D disjoint from B′. Then θ_h(B) − θ_h(B′) = v_h(D) − min_B v_h + min_{B′} v_h ≥ 0, because min_B ≤ min_{B′}. Now fix h and a bundle B′ of X′ held by someone else. If B′ ⊆ B for a bundle B of X, then θ_h(B′) ≤ θ_h(B) ≤ v_h(X_h). This holds when B is another agent's bundle, since X is EFX₀, and when B = X_h, since θ_h(X_h) ≤ v_h(X_h) by F1. Otherwise θ_h(B′) ≤ v_h(X_h) by (ii). Either way θ_h(B′) ≤ v_h(X_h) ≤ v_h(X′_h). For Z = {g, y}, θ_h(Z) = max(v_h(g), v_h(y)) if both are in R_h, and at most that otherwise; a good h does not envy is worth at most v_h(X_h). ∎

## 2. Moves and the potential

The potential is Φ(X) = (Σ_i ℓ_i(X), number of allocated goods), compared lexicographically. It takes finitely many values, so any sequence of Φ-raising moves is finite. It is ordinal (it uses levels only), so every statement below holds for every additive valuation consistent with the ranking profile. Every move below is used only when its result is EFX₀; the lemmas give conditions under which that is automatic.
- **E (fill).** X_j = ∅ and g ∈ P: set X_j := {g}.
- **S (swap).** i envies g ∈ P: the goods of X_i go to the pool and X_i := {g}.
- **R (rotate).** On an envy cycle, each agent takes the bundle of the agent it envies.
- **A (add).** g ∈ P goes into a nonempty bundle X_j.
- **U (rebundle).** One agent i takes a new bundle Y ⊆ X_i ∪ P ∪ J_i, where J_i is the set of goods other agents hold as junk. The goods of X_i ∖ Y go to the pool. The move requires ℓ_i not to drop and Φ to rise. This includes E, S and A.
- **C (champion path).** On an envy path s = t_0 → t_1 → … → t_r = k with r ≥ 1, each t_q (q < r) takes X_{t_{q+1}}, and k takes a set Z ⊆ X_s ∪ P with v_k(Z) > v_k(X_k). The goods of X_s ∖ Z go to the pool.
- **X (augmented envy cycle).** On agents i_0, …, i_{L−1} (L ≥ 2), each i_t takes a set Z_t of its own goods that meets X_{i_{t+1}} (indices mod L), drawn from X_{i_{t+1}}, the pool and junk held by anyone. The Z_t are disjoint and v_{i_t}(Z_t) > v_{i_t}(X_{i_t}). Every other good of these agents' bundles goes to the pool. R is the case Z_t = X_{i_{t+1}}. C is essentially the case where only the last Z_t is not a whole bundle.

U, C and X are Pareto improvements (some agent strictly better), so they raise Σℓ. E and A raise the number of allocated goods and lower no level. S and R raise Σℓ.

**Lemma 4 (validity).** Let X be EFX₀.
- (a) E, S and R always give EFX₀ allocations.
- (b) If nobody envies a pool good and s is a source with |X_s| ≤ 1, then adding any g ∈ P to X_s gives an EFX₀ allocation.
- (c) If nobody envies a pool good and s is a source, adding g ∈ P to X_s gives an EFX₀ allocation unless some a-holder i ≠ s has {b_i, c_i} = {g, y} with y ∈ X_s and |X_s| ≥ 2. Such an i is a *blocker* of (s, g).
- (d) Moving junk to the pool keeps EFX₀ and every level.
- (e) Suppose nobody envies a pool good. Let i be a blocker of (s, g), with s a source, and let there be an envy path from s to i. Then the champion move C with Z = {g, y} gives an EFX₀ allocation.
- (f) Suppose nobody envies a pool good. Let i be a blocker of (s, g) with y ∉ R_s. Then i taking {g, y}, with X_i going to the pool, gives an EFX₀ allocation.

*Proof.* (a) E: the new bundle {g} is a singleton, so Lemma 3 applies. S: {g} is a singleton, every other bundle is a subset of an old one, and only i's level changes, upward. R: F2 in `proofs/lemmas.md`, or Lemma 3.
(b) The new bundle X_s ∪ {g} has ≤ 2 goods. By Lemma 1 only (F) matters, since (Q) needs 3 goods. The goods that become non-free are g, which nobody envies, and the old good x of X_s = {x}, which nobody envies because s is a source. Agent s holds more own goods than before and was safe; each case of Lemma 1 for s is monotone under adding goods. For S_s = ∅ → {g}, i.e. g = a_s, (Q) holds because b_s and c_s were free.
(c) As in (b), (F) is unaffected. g and the goods of X_s are unenvied: X_s's goods are either in a bundle of ≥ 2 goods, hence unenvied by (F), or form an unenvied singleton. Only (Q) can fail, for an a-holder i ≠ s with {b_i, c_i} ⊆ X_s ∪ {g} and |X_s ∪ {g}| ≥ 3. Now {b_i, c_i} ⊄ X_s: otherwise i would envy s (b + c > a), or would already violate (Q). So g ∈ {b_i, c_i}, the other good y is in X_s, and |X_s| ≥ 2.
(d) Freeness only increases, bundles only shrink, and holders' own goods are unchanged.
(e) This is Lemma 3. Path agents strictly improve; the bundles of X′ are old bundles except Z. Nobody envies g, a pool good. Nobody envies y: it lies in X_s, which has ≥ 2 goods, so y is not free and (F) forbids envy of it.
(f) i becomes rich. s loses only junk, so its level is unchanged. The new bundles are X_s ∖ {y} ⊆ X_s and {g, y}, and neither g nor y is envied. Lemma 3 applies. ∎

## 3. Theorem A: without junk, the elementary moves never get stuck

**Theorem A.** Let X be a junk-free EFX₀ partial allocation of a core with P ≠ ∅. Then one of the following applies, each giving an EFX₀ allocation with larger Φ:
- S: some agent envies a pool good;
- R: the envy graph has a cycle;
- E: some bundle is empty;
- A: some source s has |X_s| = 1; add any pool good to it.

*Proof.* Suppose that no agent envies a pool good, that the envy graph is acyclic and that no bundle is empty. Suppose, for contradiction, that every source has at least two goods. X is junk-free, so every source holds at least two of its own goods, is rich, and by Lemma 2 (a) envies nobody. Let v be any agent that is not a source. It has an in-neighbour u, and u envies someone, so u is not a source either. Repeating, we get an infinite backward walk through non-sources. The graph is finite, so the walk repeats a vertex, and the envy graph has a cycle, which is a contradiction. So every agent is a source with at least two goods, and at least 2n ≥ m goods are allocated (L4). This contradicts P ≠ ∅. Hence some source s has |X_s| ≤ 1. X_s ≠ ∅ by assumption, so |X_s| = 1, and Lemma 4 (b) applies. Lemma 4 (a) covers S, R and E. ∎

E and A can create junk: the good may be worthless to the agent receiving it. Theorem A is where the three-goods restriction enters most directly (§6). The corresponding statement fails for general additive valuations, where a source with two goods can still envy.

`src/ls_check.c -P` classifies every partial EFX₀ state by the first case that applies: E, S, R, A (at a source), (f) or (e). For n ≤ 5 every *junk-free* state is settled by E, S, R or A, as Theorem A says (column "junkless-uncovered" = 0 in `results/ls_allstates_2_5.log`).

## 4. One phase: junk inside the state

**Result 4.1 (exhaustive, one implementation).** Take every connected core with n ≤ 5 (all m), every ranking profile, and every EFX₀ partial allocation with P ≠ ∅. Then one of the moves E, S, R, A, U, C raises Φ and gives an EFX₀ allocation. For n ≤ 4 every such state was examined (64,183,056 states for n = 4). For n = 5 the checker examined every state whose bundles are all nonempty and in which no agent envies a pool good: 243,021,230 (state, profile) pairs. The remaining states are settled by E and S (Lemma 4 (a)). Log: `results/ls_allstates_2_5.log`.

The cases of Lemma 4 settle all but a few states. For n = 4, 24 states need a *junk grab*, where an agent takes a good that its holder does not value. For n = 5, 1,296 states need a single-agent rebundle U in one of three patterns (`results/ls_allstates_2_5.log`):
- a source holding one own good and junk takes a pool good it values and drops the junk;
- an a-holder takes its b and c, both held as junk by others, and drops a;
- a source takes a good it values from another agent's junk and drops its own junk.
Every one of these states contains junk.

**Refutation 4.2 (the one-phase search can get stuck at n = 6).** Core 687 of genbg's list for (n, m) = (6, 9), under the profile with rankings (a, b, c)
  (1,6,7) (4,5,8) (1,5,0) (6,0,3) (5,2,3) (4,6,2):
The moves E (goods 1, 4, 0, 6, 5, 2 to agents 0, …, 5 in turn), then A (good 8 to agent 2), then A (good 7 to agent 5) each raise Φ and keep EFX₀. They reach the EFX₀ state
  {1} {4} {0,8} {6} {5} {2,7}, pool {3},
from which no move E, S, R, A, U, C or X gives an EFX₀ allocation with larger Φ. Replay: `python src/local_search.py stuck6` (independent Python implementation, raw definition; log `results/ls_stuck6.log`).
- Same core, all profiles: 192 stuck states under E, S, R, A, U, C. X removes 64 of them; the champion move with junk (K in `ls_check.c`) removes none (`results/ls_allstates_core687.log`).
- All 128 stuck states are reachable from the empty allocation. Each has the form of the state above: every bundle holds exactly one of its holder's goods, and agents 2 and 5 also hold the junk goods 7 and 8, in one of the two ways.
  - Fill each agent's own good (moves E). A partial allocation whose bundles have at most one good is EFX₀, since every good is free.
  - Then add the two junk goods (moves A). Each intermediate state is the stuck state minus some junk, so it is EFX₀ by Lemma 4 (d), and each move raises the number of allocated goods.
  - A breadth-first closure of all seven move types from the empty allocation confirms this for 4 of the 64 profiles (`results/ls_reach_core687.log`).
- A complete EFX₀ allocation with the same levels exists: {1} {4} {0,3} {6} {5} {2,7,8}. It is reached by moving the junk good 8 from agent 2 to agent 5 and placing 3 with agent 2. This raises the number of allocated goods, but no move above does it: it needs junk to be *relocated*.
- n ≤ 5 has no stuck state, so n = 6 is the smallest n where this move set fails. The other n = 6 cores were not searched in this mode.

So this move set with this potential does not prove TARGET. The failure is entirely about where junk sits, which leads to the two-phase version: drop all junk, improve the valued part, and place the junk afresh.

## 5. Two phases: Pareto moves on junk-free states, then junk placement

Dropping all junk from any EFX₀ partial allocation keeps it EFX₀ and keeps every level (Lemma 4 (d)). So every state has a junk-free *valued part* with the same Σℓ.

**Phase 1** works on junk-free EFX₀ partial allocations Y, writing U for the set of unallocated goods. It applies the following moves while one gives an EFX₀ allocation. After each move, goods whose new holder does not value them are returned to U; this keeps EFX₀ by Lemma 4 (d).
- (M1) *valued rebundle*: one agent i replaces Y_i by a set Z ⊆ R_i ∩ (Y_i ∪ U) with v_i(Z) > v_i(Y_i). This includes swaps S and adds of valued goods.
- (M2) *champion path*: C, with Z ⊆ R_k ∩ (Y_s ∪ U) and path agents keeping only their own goods of the bundles they take.
- (M3) *augmented envy cycle*: X with every Z_t ⊆ R_{i_t} ∩ (Y_{i_{t+1}} ∪ U). This includes rotations R.

Every move is a Pareto improvement with some agent strictly better, so Σℓ strictly increases and Phase 1 terminates. Y is *stable* when no move applies. By Lemma 4 (a), a stable Y has (s2) no agent envying a good of U, and (s3) an acyclic envy graph.

**Phase 2** places U as junk: each u ∈ U goes to an agent that does not value it.

**Placement conjecture TP.** For every connected core, every ranking profile and every stable junk-free EFX₀ partial allocation Y with U ≠ ∅, U can be placed as junk so that the complete allocation is EFX₀.

**Theorem B.** If TP holds for all connected cores with at most N agents, then every instance with at most N agents and |R_i| ≤ 3 for all i has an EFX₀ allocation. In particular TP implies TARGET.

*Proof.* By the CORE reduction and L6 (`proofs/lemmas.md`), it suffices to find an EFX₀ allocation of every connected core with at most N agents. By L5 (iv), strict profiles suffice. Start Phase 1 from the empty allocation, which is EFX₀ and junk-free. Phase 1 terminates at a stable Y. If U = ∅, Y is complete. Otherwise TP completes Y. ∎

The next three lemmas describe stable states and reduce TP to a condition on single goods. Let Y be stable with U ≠ ∅.

**Lemma 5 (what stability gives).**
- (a) No agent envies a good of U.
- (b) No a-holder i has both b_i and c_i in U.
- (c) If an a-holder i has one of b_i, c_i in U, then some agent envies a_i.
- (d) An agent valuing a good u ∈ U is one of the following: an a-holder as in (c), with u ∈ {b_i, c_i}; an agent holding exactly {b_i} with u = c_i, where some agent envies b_i; or an agent holding exactly {a_i, b_i} with u = c_i, where R_i contains the bottom pair of another a-holder.

*Proof.* (a) is (s2). (b) Otherwise i can swap {a_i} for {b_i, c_i}, an M1 move. It is valid by Lemma 3: {b_i, c_i} consists of two pool goods nobody envies, and the other bundles are unchanged. (c) Otherwise M1 adding the pool good to {a_i} is valid: the new bundle has 2 goods, a_i is unenvied and the pool good is unenvied (Lemma 1). (d) If S_i = ∅ or {c_i}, the goods i envies are free, and by (a) not in U; the goods it does not envy are already held. If S_i = {b_i}, then a_i is envied and not in U, so u = c_i; adding it is valid unless b_i is envied. If S_i = {a_i}, see (c). If i is rich with two goods and the third is u, then i holds {a_i, b_i}: otherwise swapping its worse good for u is a valid M1 (two goods, u unenvied). Adding u gives R_i with 3 goods, which fails only through (Q) of another agent. That agent is an a-holder whose bottom pair lies in R_i. Y_i could also be exactly its bottom pair, which is a special case. If i holds all three goods, none is in U. ∎

**Lemma 6 (junk can only go to sources).** Let X be a complete EFX₀ allocation obtained from Y by placing U as junk. Then every good of U lies in the bundle of an agent that is a source in Y's envy graph.

*Proof.* Levels do not change in Phase 2, so the goods each agent envies are the same in X as in Y. Suppose k envies j in Y. By Lemma 2, either Y_j = {x} with k envying x, and x must stay free, so X_j = Y_j; or Y_j = {b_k, c_k} with S_k = {a_k}, and adding anything breaks (Q) for k. ∎

**Lemma 7 (the placement condition is per good).** For u ∈ U and a source s, say that s is *dirty* for u if some a-holder i has {b_i, c_i} = {u, y} with y ∈ Y_s (then i ≠ s, because an a-holder holds neither of its b, c), and *clean* otherwise. A placement of U into source bundles, each u to an agent not valuing it, is EFX₀ if and only if every u placed at a source that is dirty for u is the only good placed there and Y_s = {y}, so that the final bundle is exactly {y, u}.

*Proof.* Check Lemma 1 on the final allocation X. (F): the goods agents envy are unchanged. They are alone in non-source bundles, which receive nothing by Lemma 6. No good of U is envied, by Lemma 5 (a). (Q) for an a-holder i:
- If b_i and c_i are both in U: impossible by Lemma 5 (b).
- If both are in Y and share a bundle: that bundle is exactly {b_i, c_i} by (Q) in Y. Then i envies it, it is not a source, and it receives nothing.
- If one, u, is in U and the other, y, is in Y_s: they share a bundle only if u is placed at s, and then (Q) requires that bundle to have 2 goods.

The agent receiving u is safe as before: its own goods and the goods it envies are unchanged. ∎

**Corollary 8.**
- (a) If Y has an empty bundle, placing all of U there works.
- (b) If at least |U| sources have a bundle of at most one good, give each good of U to a different one of them.
- (c) In particular TP holds whenever |U| = 1: by the proof of Theorem A, a stable Y without empty bundles has a source with exactly one good.

*Proof.* (a) The empty agent's own goods are all free (Lemma 1, S = ∅) and not in U (Lemma 5 (a)), so they are alone. Every bundle except the dump has at most its Y-goods. Pairs {u, u′} ⊆ U are never bottom pairs, by Lemma 5 (b). So Lemma 7 holds with no dirty placement, and the dump is a source because nobody envies an empty bundle. Also, no good of U is valued by the empty agent (Lemma 5 (a)), so all placements are junk. (b) Every final bundle has at most 2 goods, so (Q) cannot fail and Lemma 7 holds. A good u valued by the receiving agent does not occur: such a source would have a valid M1 adding u, by Lemma 4 (b). ∎

**What TP needs.** By Lemma 7, TP asks for an assignment of the goods of U to sources in which a good whose chosen source is dirty sits alone next to that source's single good. Corollary 8 covers the easy cases. The hard case has more goods in U than one-good sources, with some good dirty at every source; the n = 6 example below is of that kind.

**Evidence 5.1.** The C checker `src/ls_twophase.c` (`-x` adds M3) enumerates every junk-free partial allocation of every connected core, every profile, and every stable state, and searches all placements of U into source bundles. The independent Python implementation (`python src/local_search.py py n`) decides EFX₀, envy and every move from the raw definition with two numeric realizations, and searches placements over all agents, not just sources.
- n ≤ 5, with M1 and M2 only: 5,751,498 stable states over 293 + 41 + 7 + 2 cores, 0 failures (`results/ls_twophase_2_5.log`).
- n = 6, with M1 and M2 only: 707,475,902 stable states over 3,093 cores. It fails in exactly one core, core 687 (the core of Refutation 4.2), in 64 profiles (`results/ls_twophase_6_m1m2.log`; attempt file `attempts/local-search-twophase-m1m2.md`).
- n = 6, with M1–M3: SEE_N6_RESULT (`results/ls_twophase_6.log`).
- Python and C agree on n ≤ 4 (with M1–M3): the same number of stable states per core and 0 failures (`results/ls_twophase_py_2_4.log`).

**The n = 6 failure without M3.** Core 687 under the profile (1,6,7) (4,5,8) (0,1,5) (0,3,6) (2,3,5) (2,4,6).
- Y = {1} {4} {5} {0} {2} {6}, U = {3, 7, 8}; the sources are agents 2 ({5}) and 5 ({6}).
- Good 7 is dirty at agent 5 (bottom pair {6, 7} of agent 0), and good 8 is dirty at agent 2 (bottom pair {5, 8} of agent 1). Good 3 is dirty at both sources (bottom pairs {3, 6} of agent 3 and {3, 5} of agent 4), so it must sit alone at one of them, and then 7 or 8 has nowhere to go.
- Y is stable under M1 and M2. The augmented envy cycle 0 → 5 → 1 → 2 → 0 improves it: agent 0 takes {6, 7}, agent 5 takes {4}, agent 1 takes {5, 8}, agent 2 takes {1}. Afterwards good 3 fits with agent 2: {6,7} {5,8} {1,3} {0} {2} {4} is EFX₀.

## 6. Where the three-goods restriction is used

1. **Lemma 1.** Safety is local: envied goods must be free, plus one pair condition (Q). This uses the total order of the 8 subset sums, which holds for three goods with a < b + c (L5 (i)). With more relevant goods, envy toward multi-good bundles appears, and threats are not decided by single goods.
2. **Lemma 2.** An agent envies only singletons and, if it is an a-holder, the exact bundle {b, c}. Rich agents envy nobody. This is what makes sources rigid in Theorem A (a source with ≥ 2 own goods is a sink) and what closes envied bundles to junk (Lemma 6).
3. **Theorem A** also uses m ≤ 2n (L4: three goods per agent, at most one private good), to rule out "every agent is a source with two goods".
4. **Lemma 5 (b).** A top holder with both lower goods unallocated takes them, which uses b + c > a, i.e. balance. So (Q) never involves two unallocated goods, and the placement condition is per good (Lemma 7). For general additive valuations the junk-placement constraints involve arbitrary subsets. This is exactly where "EFX with charity" arguments stop: a pool nobody envies, which cannot be handed out.

## 7. Status and the remaining gap

- PROVED: Lemma 1; Lemmas 2–4; Theorem A; Theorem B (TP ⟹ TARGET); Lemmas 5–7 and Corollary 8.
- EVIDENCE (exhaustive, one implementation): Result 4.1, the one-phase search never stuck for n ≤ 5. TP for n ≤ 6 (M1–M3), with C and Python agreeing for n ≤ 4.
- REFUTED: "the one-phase local search with moves E, S, R, A, U, C, X and potential (Σℓ, allocated goods) never gets stuck", at n = 6 (Refutation 4.2). And "TP with Phase 1 moves M1, M2 only", at n = 6 (core 687).
- CONJECTURE: TP for all n (with M1–M3). It implies TARGET.
- **Gap.** TP beyond Corollary 8: a stable Y whose unallocated goods outnumber the one-good sources and include a good that is dirty at every source. A proof would take a Hall violator of the placement problem (Lemma 7) and build an augmented envy cycle (M3) from it, as in the n = 6 example: dirty edges from a-holders to sources, closed by envy edges from sources to the holders of the a-holders' tops. The difficulty is that the cycle must use distinct unallocated goods on its dirty edges, and the n = 6 example shows that the good dirty everywhere (good 3) need not be one of them.
