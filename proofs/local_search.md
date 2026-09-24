# EFX₀ in cores by local search (Theorem C: a written proof of conjecture D and TARGET)

Workstream `proof/local-search`. This route to TARGET does not go through conjecture D. It keeps a partial EFX₀ allocation of a core and applies moves that raise a potential, like the existence proofs for identical valuations, three agents, multigraphs and hypergraphs of girth ≥ 4 listed in `proofs/citations.md`. None of those papers was read for this work; their methods are known here only from the summaries in `proofs/citations.md`, and nothing below depends on them.

**Main result.** Status: a written proof, independent of the one in `proofs/lb_last_step.md`. It is not claimed in the ledger until it has been reviewed and formalized (owner's policy; ledger rows LS3, D, T).
- **Theorem C (§4).** For every core and every balanced valuation (ties broken first into a strict ranking profile), Algorithm LS2 computes a complete EFX₀ allocation within 7n Phase-1 steps. In it, at most one bundle has more than two goods.
- If correct, this proves **conjecture D** for every core, connected or not.
- With the reduction to cores (`proofs/lemmas.md`, CORE), it then also proves **TARGET**: every additive instance in which each agent values at most three goods positively has an EFX₀ allocation.

Algorithm LS2 has two phases.
- **Phase 1** keeps a *junk-free* partial EFX₀ allocation: every allocated good is valued by its holder. It applies seven kinds of Pareto improvement, and the sum of levels (a potential ≤ 7n) rises at every step.
- **Phase 2** places the unallocated goods as *junk*, that is, with agents that do not value them. The placement is read off a maximum matching between one-good source bundles and the goods that are "dirty" for them (Hall's theorem).
- The key step (step 7) is an *augmented envy cycle*. Whenever the matching saturates every one-good source, such a cycle exists.

**Structure and status.**
- §1–§3 are lemmas: partial EFX₀ in a core is ordinal and local (Lemma 1), envy has a rigid form (Lemma 2), one threat bound covers every move (Lemma 3), plus move validity (Lemma 4) and Theorem A, which shows that junk-free states never block the elementary moves.
- §4 is the algorithm and the proof of Theorem C. Everything in §1–§4 is proved here and was re-read; the proof of Theorem C uses only Lemmas 1–3, F1, L4 and L5 (iv) of `proofs/lemmas.md`.
- §5 is computational corroboration, which is not part of the proof (PROMPT.md §5 rule 3):
  - Algorithm LS2 was run on every ranking profile of every connected core with n ≤ 6: 146,640,096 runs, each checked. The distinct outputs were saved as certificates, which the SAT-free checker `tools/check_certs.py` accepts.
  - An independent Python implementation that works from numeric valuations was run exhaustively for n ≤ 5, and on random cores with random real balanced values up to n = 100.
- §6 records how the moves were found. It includes two refutations: a one-phase local search, where junk is part of the state, can get stuck at n = 6; and Phase 1 without augmented envy cycles can end in a state that no junk placement completes, again at n = 6.
- §7 says where the three-goods restriction is used.

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

E and A can create junk: the good may be worthless to the agent receiving it. Theorem A is where the three-goods restriction enters most directly (§7). The corresponding statement fails for general additive valuations, where a source with two goods can still envy.

`src/ls_check.c -P` classifies every partial EFX₀ state by the first case that applies: E, S, R, A (at a source), (f) or (e). For n ≤ 5 every *junk-free* state is settled by E, S, R or A, as Theorem A says (column "junkless-uncovered" = 0 in `results/ls_allstates_2_5.log`).

## 4. Algorithm LS2 and Theorem C

Fix a core with a strict ranking profile (a_i, b_i, c_i) and balanced additive valuations consistent with it. LS2 runs on the strict profile: if values are tied, break the ties first (L5 (iv)). Deciding directly on tied numbers can fail. The smallest case is n = 3, m = 5, sets {0,2,4}, {1,3,4}, {2,3,4}, each with values (2, 2, 1): the swaps 0→2, 1→3, 2→4 and then Phase 2 (b) give {2} {3} {0,1,4}, where agent 0 has 2 while {0, 4} is worth 3 to it. Y denotes a junk-free partial allocation and U its set of unallocated goods.
- A *one-good source* is a source s with |Y_s| = 1.
- A *dirty triple* (i, u, s) consists of a one-good source s with Y_s = {y}, an a-holder i and a good u ∈ U with {b_i, c_i} = {u, y}.
- For a one-good source s, D(s) is the set of goods u such that some dirty triple (i, u, s) exists. For a set T of one-good sources, D(T) is the union of the D(s), s ∈ T.

**Algorithm LS2.**

*Phase 1.* Start with Y_i = ∅ for all i and U = M. While U ≠ ∅, apply the first of the following steps that applies:
1. *(swap)* Some agent i envies a good u ∈ U. The goods of Y_i go to U, and Y_i := {u}.
2. *(rotation)* The envy graph has a cycle i_0 → i_1 → … → i_{L−1} → i_0. Each i_t takes Y_{i_{t+1}} ∩ R_{i_t}; the other goods of these bundles go to U.
3. *(bottom pair)* Some a-holder i has b_i, c_i ∈ U. Then Y_i := {b_i, c_i}, and a_i goes to U.
4. *(add a bottom good)* Some a-holder i has exactly one of b_i, c_i in U, say u, and nobody envies i. Then Y_i := {a_i, u}.
5. *(source adds)* Some one-good source s values a good u ∈ U. Then Y_s := Y_s ∪ {u}.

   If steps 1–5 do not apply and some bundle is empty, Phase 1 stops here. This test comes only after steps 1–5 fail; at the top of the loop it would stop at the empty start.
6. *(champion)* There are a dirty triple (i, u, s), with Y_s = {y}, and an envy path s = t_0 → t_1 → … → t_r = i. Each t_q (q < r) takes Y_{t_{q+1}} ∩ R_{t_q}, and i takes {u, y}. The other goods of these agents' bundles go to U.
7. *(augmented envy cycle)* The family (D(s))_s, over the one-good sources s, has a system of distinct representatives. Apply the move constructed in Claim 3 below.

If none applies, Phase 1 stops.

*Choice points.* Any choice works at every one of them; the proof below holds for each.
- The order of steps 1–7 matters only through the preconditions the proof uses: steps 3–7 are applied only when step 1 does not apply, and steps 6–7 only when steps 1–5 do not apply and no bundle is empty.
- Within a step, any applicable instance may be taken: the agent and the good in steps 1, 3, 4 and 5, the cycle in step 2, and the triple and the path in step 6.
- In step 7: any system of distinct representatives, any dirty triple (i_s, ℓ(s), s) for each s (that is, any a-holder i_s), any f(s) and path P_s, any cycle of f and any starting source s_1 on it, and any shortest closed sub-walk C of W. W may be read linearly, from s_1 to s_1, or cyclically; both work.
- In Phase 2: any empty bundle in (a); any maximum matching M and any unmatched s* in (b).

`src/ls_alg.c` takes the first instance in index order. `src/local_search.py` (`ls2_numeric`) makes its own choices and decides everything from numeric values. Both check every output against the raw EFX₀ definition.

*Phase 2.* If U ≠ ∅ when Phase 1 stops, do one of the following.
- (a) If some bundle Y_e is empty, add all of U to it.
- (b) Otherwise:
  - Take a maximum matching M between the one-good sources and the goods, where s may be matched to u iff u ∈ D(s).
  - Take a one-good source s* that M leaves unmatched, and let T consist of s* and the one-good sources reachable from s* by M-alternating paths s → u → M(u) with u ∈ D(s).
  - Add each u ∈ D(T) to Y_{M(u)}, and add every other good of U to Y_{s*}.

**Theorem C.** Algorithm LS2 terminates after at most 7n steps of Phase 1. It outputs a complete allocation that is EFX₀ for every balanced additive valuation consistent with the profile, and in which at most one bundle has more than two goods. Hence every core has such an allocation, including cores with ties (by L5 (iv)).

*Proof.* Throughout, Y is junk-free and EFX₀. This holds at the start (the empty allocation). Its decisions use only the ranking profile (Lemma 1, levels), so it suffices to argue for one valuation.

**Claim 1 (steps 1–6).** If one of steps 1–6 applies, the result is junk-free and EFX₀, and Σℓ strictly increases.

Every taker receives only goods it values, so Y stays junk-free. We apply Lemma 3 with X = Y. Condition (i) holds because every agent that receives a new bundle strictly improves (below), and the others keep their bundles.
- Step 1: the new bundle is the singleton {u}.
- Step 2: every agent on the cycle strictly improves, since it envied the bundle it takes. The new bundles are subsets of old bundles.
- Step 3: i gets value v_i(b_i) + v_i(c_i) > v_i(a_i) by balance. The new bundle {b_i, c_i} consists of two goods of U. Step 1 does not apply, so nobody envies them, and (ii) of Lemma 3 holds.
- Step 4: i improves. The new bundle {a_i, u} consists of u, which nobody envies (step 1 does not apply), and a_i, which nobody envies because nobody envies i and Y_i = {a_i}.
- Step 5: s improves. The new bundle {y, u} consists of u, envied by nobody, and s's good y, envied by nobody because s is a source.
- Step 6: every t_q improves (envy), and i improves by balance. The new bundles are subsets of old bundles, plus {u, y}, whose goods nobody envies (u ∈ U; y is the single good of the source s).

In each case Lemma 3 gives EFX₀. Since the value of a set of own goods determines its level, Σℓ strictly increases. ∎

**Claim 2.** Suppose U ≠ ∅, steps 1–6 do not apply and no bundle is empty. Then:
- (a) nobody envies a good of U;
- (b) the envy graph is acyclic;
- (c) no a-holder has both b_i and c_i in U;
- (d) if an a-holder i has one of b_i, c_i in U, some agent envies i;
- (e) no one-good source values a good of U;
- (f) every source that envies somebody is a one-good source;
- (g) there is a one-good source;
- (h) for every dirty triple (i, u, s), some one-good source s′ ≠ s has an envy path to i.

*Proof.* (a)–(e) say that steps 1–5 do not apply.
- (f) A source is nonempty. If it has ≥ 2 goods, it holds ≥ 2 of its own goods (Y is junk-free), so by Lemma 2 (a) it envies nobody.
- (g) If some agent is not a source, walk backwards along envy edges from it. By (b) the walk ends, at a source that envies somebody, which is a one-good source by (f). If every agent is a source and none has exactly one good, then every bundle has ≥ 2 goods and ≥ 2n goods are allocated. But at most m − 1 ≤ 2n − 1 are (L4). So some source has one good.
- (h) By (d), i is not a source, and walking backwards from i as in (g) reaches a one-good source with an envy path to i. If s were the only such source, step 6 would apply to (i, u, s). ∎

**Claim 3 (step 7).** Suppose U ≠ ∅, steps 1–6 do not apply, no bundle is empty, and the family (D(s))_s over the one-good sources has a system of distinct representatives ℓ(s) ∈ D(s). Then there is a move that keeps Y junk-free and EFX₀ and strictly raises Σℓ.

*Proof.* The construction goes in four parts.

*Choosing a successor for each source.* For each one-good source s, fix a dirty triple (i_s, ℓ(s), s). By Claim 2 (h), fix a one-good source f(s) ≠ s and an envy path P_s from f(s) to i_s. The map f has no fixed point, so it has a cycle s_1, …, s_k with k ≥ 2 and f(s_j) = s_{j+1} (indices mod k).

*The closed walk.* Consider the closed walk W that starts at s_1 and, for j = k, k − 1, …, 1 in turn, follows P_{s_j} (from s_{j+1} to i_{s_j}) and then the *dirty edge* i_{s_j} → s_j. Every vertex of W has its successor on W. Two facts about the vertices of W:
- A one-good source has no in-coming envy edge, so it occurs on W only as the target of a dirty edge and as the start of an envy path.
- An a-holder i_s envies nobody: its bottom pair contains a good of U, so no bundle equals {b_i, c_i} (Lemma 2). So it occurs only as the end of an envy path and the tail of a dirty edge.

*A simple cycle with distinct goods.* Let C be a shortest closed sub-walk of W between two occurrences of the same agent. C is a simple cycle. It contains a dirty edge, because otherwise it would be an envy cycle, contradicting Claim 2 (b). Its dirty edges enter distinct sources s, so they carry distinct goods ℓ(s).

*The move.* Every agent t of C whose successor on C is t′ via an envy edge takes Y_{t′} ∩ R_t. Every agent i_s whose successor is s via a dirty edge takes {ℓ(s)} ∪ Y_s. All other goods of the bundles of C's agents go to U.
- The taken sets are disjoint: they lie in the bundles of distinct successors, plus distinct goods of U.
- Every agent of C strictly improves. For envy edges this holds by definition. For dirty edges, i_s's value rises from v(a) to v(b) + v(c) > v(a) by balance, since {ℓ(s)} ∪ Y_s = {b_{i_s}, c_{i_s}}.
- The new bundles are subsets of old bundles, or sets {ℓ(s), y_s}. Nobody envies ℓ(s) ∈ U (Claim 2 (a)), and nobody envies y_s, the single good of a source. So Lemma 3 gives EFX₀.

Y stays junk-free, and Σℓ strictly increases. ∎

*Termination.* Claims 1 and 3 show that every Phase-1 step is well defined, keeps Y junk-free and EFX₀, and raises Σℓ by at least 1. Since Σℓ ≤ 7n, Phase 1 stops after at most 7n steps. When it stops with U ≠ ∅, either some bundle is empty (after step 5), or steps 1–6 do not apply and no SDR exists (so step 7 does not apply).

**Claim 4 (Phase 2).** The output X is complete and EFX₀.

*Proof.* Every good of U is added somewhere, so X is complete. In both cases every receiver is an agent that values no good of U: in case (a) because an empty agent would envy any good of U it valued, contradicting (a) of Claim 2 (which holds as soon as step 1 does not apply); in case (b) by Claim 2 (e). So levels, and the goods each agent envies, are the same in X as in Y. We check Lemma 1 for every agent h.

*(F).* The goods h envies are free in Y and not in U (step 1 does not apply), so each is alone in Y, in a bundle whose holder is envied by h. That holder is not a source. In case (a) the receiver's bundle was empty, and in case (b) receivers are sources. So these bundles receive nothing and the goods stay alone.

*(Q)* for an a-holder h, with lower goods b_h, c_h. Step 3 does not apply, so they are not both in U. Two cases remain.
- *Both in Y.* If they lie in different Y-bundles they stay apart, since Phase 2 only adds goods of U to bundles. If they lie in one Y-bundle B, then B = {b_h, c_h} by (Q) in Y. Then h envies B's holder (v(b) + v(c) > v(a)), so that holder is not a source and B receives nothing.
- *One in U, say u, and the other, y, in a bundle Y_j.* They share a bundle in X only if u is added to Y_j. In case (a), Y_j = ∅ cannot contain y. In case (b), j is a receiver, hence a one-good source with Y_j = {y}, and (h, u, j) is a dirty triple, so u ∈ D(j).
  - If j = s*, then u ∈ D(T) and u was sent to M(u) ≠ s* instead.
  - Otherwise j = M(u′) for some u′ ∈ D(T), and M(u′) receives only u′. The matching map is injective on D(T), and the goods outside D(T) go to s*. So u = u′ and X_j = {y, u} has two goods, and (Q) holds.

It remains to check that case (b) is well defined.
- One-good sources exist by Claim 2 (g). M leaves some one-good source unmatched; otherwise M would be a system of distinct representatives and step 7 would apply.
- Every u ∈ D(T) is matched: otherwise the alternating path to u would augment M.
- M(u) ∈ T, since the alternating path continues through M(u).
- s* is unmatched, so M(u) ≠ s*. ∎

**Claim 5 (shape).** Every bundle of Y has at most two goods throughout Phase 1, and the output has at most one bundle of more than two goods.

*Proof.* Every Phase-1 step creates only bundles of the following kinds:
- singletons (step 1);
- sets of two goods (steps 3, 4, 5, and the sets {u, y} of steps 6 and 7);
- subsets of existing bundles (steps 2, 6, 7).

So by induction every bundle of Y has at most two goods. Phase 2 (a) adds goods to one bundle only. Phase 2 (b) adds exactly one good to each of the sources M(u), u ∈ D(T), which had one good each, and all remaining goods to Y_{s*}. So every bundle other than X_e (case (a)) or X_{s*} (case (b)) has at most two goods. ∎

Claims 1–5 prove Theorem C. ∎

**Corollary 1 (conjecture D).** Every core, connected or not, has an EFX₀ allocation in which at most one bundle has more than two goods.

*Proof.* Theorem C, with L5 (iv) for cores whose values have ties. ∎

**Corollary 2 (TARGET).** Every additive instance in which every agent values at most three goods positively has an EFX₀ allocation.

*Proof.* By the CORE reduction (`proofs/lemmas.md`, "CORE: reduction of TARGET to cores"), it suffices that every core has an EFX₀ allocation. That is Theorem C. Connectivity is not needed, so L6 is not used. ∎

*Remarks.*
1. LS2 runs in polynomial time. There are at most 7n Phase-1 steps. Each step needs the envy graph, its reachability relation, the dirty triples (O(n²m)) and one bipartite matching. The reduction to cores is polynomial as well.
2. The large bundle is X_{s*}, consisting of s*'s single good plus junk, or in case (a) the formerly empty agent's bundle, which is junk only. Either way, every good of U in it is worthless to its holder (Claim 2 (e); Claim 4 for case (a)).
3. D for disconnected cores was open beyond n ≤ 6 (ledger R3; `proofs/lemmas.md`, note after L6). Theorem C does not use connectivity, so it settles that case too.
4. The CORE reduction peels agents (L2) and gives junk to a source (L3). So for a general instance with |R_i| ≤ 3 the final allocation can have further large bundles: the junk bundle of L3, and the peeled bundles P of rule R2. D is a statement about cores only.

## 5. Computational corroboration of Theorem C (not part of the proof)

- **C implementation, exhaustive.** `src/ls_alg.c` runs LS2 exactly as in §4 on every ranking profile of every connected core with n ≤ 6 (all m; nauty genbg via `src/cores_nauty.py`).
  - After every Phase-1 step it asserts that Y is EFX₀ (Lemma 1), that Σℓ increased, and that there is no junk.
  - It aborts if Claim 2 (h) or the Hall step ever fails.
  - It checks the output against the RAW definition with two balanced realizations.
  - It also asserts that every Phase-1 bundle has at most two goods, and that every output has at most one bundle of more than two goods (Claim 5).
  - Result: 146,640,096 runs (n = 2, …, 6), with no failure (`results/ls_alg_2_6.log`). Step 7, the augmented envy cycle, is used: 24 times at n = 4, 1,160 at n = 5, and 59,700 at n = 6; the champion step 6 is used 14,384,250 times at n = 6, and no run needs more than 22 Phase-1 steps (the bound is 7n = 42).
- **Certificates.** The distinct outputs per core are saved as `results/certs_ls2_2_5.json.gz` and `results/certs_ls2_6.json.gz`: 372,378 allocations over 3,436 cores. The SAT-free checker `tools/check_certs.py`, written independently of this work, confirms from the raw EFX₀ definition that they cover every profile of every core. With `--require-d` it also confirms that every stored allocation has at most one bundle of more than two goods (`results/check_certs_ls2.log`). The largest bundle has 5 goods for n ≤ 5 and 6 goods for n = 6.
- **Independent Python implementation.** `python src/local_search.py pyalg n` and `pyrandom` (function `ls2_numeric`) implement LS2 again from numeric valuations. Every decision (envy, steps, matching) uses the numbers, not the ordinal rule, and every step is checked by the raw definition and for being a Pareto improvement.
  - Exhaustive: every profile of every connected core with n ≤ 5 (realization (4, 3, 2)); 0 failures (`results/ls_alg_py.log`).
  - Random: 39,150 random cores, not necessarily connected (1,000 for each n = 2, …, 40, 100 for n = 50, 50 for n = 100), with independent random real balanced values; 0 failures, at most 124 Phase-1 steps (`results/ls_alg_py.log`).

## 6. How the moves were found

This section keeps the development that led to Theorem C. It explains why LS2 has two phases and why step 7 is needed. Its conjecture TP is now a consequence of the proof of Theorem C: a junk-free state that no M1–M3 move improves is in particular stable under steps 1–7, which are instances of M1–M3. So Phase 2 applies to it, by Claims 2 and 4.

### 6.1 One phase: junk inside the state

**Result 6.1 (exhaustive, one implementation).** Take every connected core with n ≤ 5 (all m), every ranking profile, and every EFX₀ partial allocation with P ≠ ∅. Then one of the moves E, S, R, A, U, C raises Φ and gives an EFX₀ allocation. For n ≤ 4 every such state was examined (64,183,056 states for n = 4). For n = 5 the checker examined every state whose bundles are all nonempty and in which no agent envies a pool good: 243,021,230 (state, profile) pairs. The remaining states are settled by E and S (Lemma 4 (a)). Log: `results/ls_allstates_2_5.log`.

The cases of Lemma 4 settle all but a few states. For n = 4, 24 states need a *junk grab*, where an agent takes a good that its holder does not value. For n = 5, 1,296 states need a single-agent rebundle U in one of three patterns (`results/ls_allstates_2_5.log`):
- a source holding one own good and junk takes a pool good it values and drops the junk;
- an a-holder takes its b and c, both held as junk by others, and drops a;
- a source takes a good it values from another agent's junk and drops its own junk.
Every one of these states contains junk.

**Refutation 6.2 (the one-phase search can get stuck at n = 6).** Take the core K with n = 6, m = 9 and agent sets {1,6,7}, {4,5,8}, {0,1,5}, {0,3,6}, {2,3,5}, {2,4,6} (goods 7, 8 private). File names call it core687; it is entry 562 of the 670 cores that `cores_nauty.py` lists for (6, 9), and it is identified by its sets, not by an index. Take the profile with rankings (a, b, c)
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

### 6.2 Two phases with general Pareto moves (before Theorem C)

Dropping all junk from any EFX₀ partial allocation keeps it EFX₀ and keeps every level (Lemma 4 (d)). So every state has a junk-free *valued part* with the same Σℓ.

**Phase 1** works on junk-free EFX₀ partial allocations Y, writing U for the set of unallocated goods. It applies the following moves while one gives an EFX₀ allocation. After each move, goods whose new holder does not value them are returned to U; this keeps EFX₀ by Lemma 4 (d).
- (M1) *valued rebundle*: one agent i replaces Y_i by a set Z ⊆ R_i ∩ (Y_i ∪ U) with v_i(Z) > v_i(Y_i). This includes swaps S and adds of valued goods.
- (M2) *champion path*: C, with Z ⊆ R_k ∩ (Y_s ∪ U) and path agents keeping only their own goods of the bundles they take.
- (M3) *augmented envy cycle*: X with every Z_t ⊆ R_{i_t} ∩ (Y_{i_{t+1}} ∪ U). This includes rotations R.

Every move is a Pareto improvement with some agent strictly better, so Σℓ strictly increases and Phase 1 terminates. Y is *stable* when no move applies. By Lemma 4 (a), a stable Y has (s2) no agent envying a good of U, and (s3) an acyclic envy graph.

**Phase 2** places U as junk: each u ∈ U goes to an agent that does not value it.

**Placement statement TP** (formerly a conjecture; it follows from Claims 2–4 of §4, see the introduction of §6). For every connected core, every ranking profile and every stable junk-free EFX₀ partial allocation Y with U ≠ ∅, U can be placed as junk so that the complete allocation is EFX₀.

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

**What TP needs.** By Lemma 7, TP asks for an assignment of the goods of U to sources in which a good whose chosen source is dirty sits alone next to that source's single good. Corollary 8 covers the easy cases. The hard case has more goods in U than one-good sources, with some good dirty at every source; the n = 6 example below is of that kind. Claims 3 and 4 of §4 settle this case: if the dirty sets of the one-good sources have a system of distinct representatives, an augmented envy cycle improves Y (step 7); otherwise Hall's theorem gives the placement.

**Evidence 6.3.** The C checker `src/ls_twophase.c` (`-x` adds M3) enumerates every junk-free partial allocation of every connected core, every profile, and every stable state, and searches all placements of U into source bundles. The independent Python implementation (`python src/local_search.py py n`) decides EFX₀, envy and every move from the raw definition with two numeric realizations, and searches placements over all agents, not just sources.
- n ≤ 5, with M1 and M2 only: 5,814,204 stable states (8, 640, 62,058 and 5,751,498 for n = 2, 3, 4, 5) over 2 + 7 + 41 + 293 cores, 0 failures. With M1–M3: 5,810,840 stable states, 0 failures (`results/ls_twophase_2_5.log`).
- n = 6, with M1 and M2 only: 707,475,902 stable states over 3,093 cores. It fails in exactly one core, core K (the core of Refutation 6.2), in 64 profiles (`results/ls_twophase_6_m1m2.log`; attempt file `attempts/local-search-twophase-m1m2.md`).
- n = 6, with M1–M3: 707,008,494 stable states over 3,093 cores, 0 failures (`results/ls_twophase_6.log`).
- Python and C agree for n ≤ 4 (with M1–M3): the same numbers of stable states (8, 640 and 62,034 for n = 2, 3, 4) and 0 failures (`results/ls_twophase_py_2_4.log`).

**The n = 6 failure without M3.** Core K under the profile (1,6,7) (4,5,8) (0,1,5) (0,3,6) (2,3,5) (2,4,6).
- Y = {1} {4} {5} {0} {2} {6}, U = {3, 7, 8}; the sources are agents 2 ({5}) and 5 ({6}).
- Good 7 is dirty at agent 5 (bottom pair {6, 7} of agent 0), and good 8 is dirty at agent 2 (bottom pair {5, 8} of agent 1). Good 3 is dirty at both sources (bottom pairs {3, 6} of agent 3 and {3, 5} of agent 4), so it must sit alone at one of them, and then 7 or 8 has nowhere to go.
- Y is stable under M1 and M2. The augmented envy cycle 0 → 5 → 1 → 2 → 0 improves it: agent 0 takes {6, 7}, agent 5 takes {4}, agent 1 takes {5, 8}, agent 2 takes {1}. Afterwards good 3 fits with agent 2: {6,7} {5,8} {1,3} {0} {2} {4} is EFX₀.


## 7. Where the three-goods restriction is used

1. **Lemma 1.** Safety is local: envied goods must be free, plus the single pair condition (Q). This rests on the total order of the eight subset sums, which holds for three goods with a < b + c (L5 (i)). With more relevant goods, threats of multi-good bundles are not decided by single goods.
2. **Lemma 2.** An agent envies only singletons and, as an a-holder, the exact bundle {b, c}. A rich agent envies nobody. Hence:
   - sources with two own goods are isolated (Claim 2 (f)), so backward envy walks end at one-good sources (Claim 2 (g), (h));
   - envied bundles never receive junk (Claim 4);
   - a-holders whose bottom pair touches U are sinks, which fixes the shape of the closed walk in Claim 3.
3. **Balance** (b + c > a) makes the dirty edge i → s an improvement for i (Claims 1 and 3), and forbids an a-holder from having both lower goods unallocated in a stable state (step 3). So the pair condition (Q) never involves two unallocated goods, and the Phase-2 constraints are per good: a dirty good must sit alone next to the source's single good. This is what reduces junk placement to a bipartite matching.
4. **m ≤ 2n** (L4: three goods per agent, at most one private good) guarantees a one-good source (Claim 2 (g)).

For general additive valuations, junk placement faces constraints on arbitrary sets of unallocated goods. That is where "EFX with charity" arguments stop: a pool nobody envies, which cannot be handed out.

## 8. Status

- **Proved in writing:**
  - Lemmas 1–4 and Theorem A (§1–§3).
  - Theorem C (§4) and Corollaries 1 (D) and 2 (TARGET) have a complete written proof here, re-read by its author. In the ledger they are **CONJECTURE** (LS3, D) and **OPEN** (T) until independently reviewed and formalized in Lean.
  - The lemmas of §6.2 (Lemmas 5–7, Corollary 8, Theorem B).
  - In the ledger, Lemmas 1–3 (LS1) and Theorem A (LS2) are PROVED, pending review.
- **Corroborated computationally** (§5), exhaustively for n ≤ 6 and randomly up to n = 100, with certificates accepted by `tools/check_certs.py`.
- **REFUTED** (§6):
  - The one-phase local search with moves E, S, R, A, U, C, X and potential (Σℓ, number of allocated goods) never gets stuck: false at n = 6 (Refutation 6.2).
  - Phase 1 with moves M1 and M2 only always ends in a state that junk placement completes: false at n = 6 (core K).
- **Conjecture D:** Corollary 1 gives it for every core, connected or not, subject to the same review.
