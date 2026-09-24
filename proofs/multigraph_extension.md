# The multigraph EFX theorem for cores, and goods with three or more valuers

Workstream `proof/multigraph-extension`. Source: Afshinmehr, Ashuri, Mahmoudkhan, Mehlhorn, Shahrezaei, "EFX Allocations Exist on Multi-Graphs", arXiv 2606.18665v1, read in full; digest in `proofs/multigraph_digest.md` (cited below as "the paper" and "digest §k"). Notation as in PROMPT.md and `proofs/lemmas.md`: a core agent i values exactly its three goods, ranked a_i > b_i > c_i, and is balanced (a_i < b_i + c_i). The *valuers* of a good are the agents that value it.

## Summary

**Proved here.**
- **Theorem M.** Every core in which each good has at most two valuers (a *multigraph core*) has an EFX₀ allocation. This is a short, self-contained proof of the part of the paper's theorem that TARGET uses (ledger T3), for every n. It needs none of the paper's machinery beyond the move U1.
- **Theorem X (extension).** Let a core have a strict ranking profile with a *popular matching* (§1), and suppose every good with three or more valuers is the top of each of its valuers (class 𝒰). Then the core has an EFX₀ allocation. Multigraph cores are in 𝒰 and always have a popular matching (Lemma 1.2), so Theorem M is a special case. The construction is explicit: popular matching, then the moves Up, U1 and R1, then one dump step.
- **Lemma 1.1 (dictionary).** In a core, the paper's simple height-one allocations are exactly the popular matchings of the ranking profile (in the sense of Abraham, Irving, Kavitha and Mehlhorn [unverified: not read in this session; everything used below is proved here]).
- **Obstructions (§5).**
  - **O1**, core H3 (n = 3, two goods with three valuers): no popular matching exists, and every EFX₀ allocation has an agent that envies someone and is envied.
  - **O2** (n = 3, m = 4, a single good with three valuers): a popular matching exists, but again every EFX₀ allocation has an agent that envies and is envied.

  The paper's allocations never have such an agent (children are envied only by their root and envy nobody; everybody else is unenvied, digest §2). So no argument whose output keeps the paper's final shape can reach O2, with or without a popular matching. Theorem X gets past this because its dump lemma (Lemma 2.1) allows the harmless envy of an agent toward a two-good bundle made of its own b and c.

**Checked by computer** (`src/mgx.py`, logs `results/mgx_mg.log`, `results/mgx_U.log`, `results/mgx_T.log`, `results/mgx_obstructions.log`). The construction was run on every profile of the classes below, for every connected core with the given n, all m. Every step asserts the invariants of Lemmas 3.1 and 3.2, and every output is checked against the raw EFX₀ definition (three balanced realizations, no use of L5). Theorems M and X are proofs; the runs cross-check them.
- Multigraph cores, n ≤ 7, and class 𝒰, n ≤ 6: every profile succeeds (every 𝒰 profile with a popular matching).
- Class 𝒯 (no good with three or more valuers is anyone's top), n ≤ 6: the moves keep every invariant, and every profile with a popular matching ends in a state with an admissible assignment, so an EFX₀ output (conjecture MX-C below). The case analysis of the dump lemma, whose proof needs class 𝒰, fails on 194 profiles with n = 6; an admissible assignment exists there too (search).

**Open.**
- Profiles with no popular matching (O1).
- Profiles in which a good with three or more valuers is the top of some valuers but not of others: the move U1 can then break the invariant I3; the smallest such profile has n = 4, m = 5 (`attempts/multigraph_u1_mixed_top.md`).
- The dump in class 𝒯: proved only in class 𝒰; conjecture MX-C (the case analysis first fails at n = 6, `attempts/multigraph_dump_class_T.md`).

What this leaves for TARGET: Theorem X adds, to ledger T3, every core whose components have a profile in 𝒰 with a popular matching.

## 0. The criterion used throughout

For an allocation X and an agent i, let S_i = X_i ∩ R_i. When |S_i| ≤ 1, let Better_i(X) be the goods of R_i that i ranks above its good in S_i (all of R_i if S_i = ∅).

**Lemma 0.** X is EFX₀ iff for every agent i with |S_i| ≤ 1:
- (α) every good of Better_i(X) is alone (the only good of its bundle), and
- (β) if S_i = {a_i}, then b_i and c_i are not together in a bundle of three or more goods.

*Proof.* This is L5(iii) (`proofs/lemmas.md`) case by case. If |S_i| ≥ 2, then i holds a with b or c (case T), or b and c (case P), and is safe. If S_i = {a_i}, i is safe iff (β) holds (case T), and Better_i = ∅. If S_i = {b_i}, i is safe iff a_i is alone (case B). If S_i = {c_i}, iff a_i and b_i are alone (case C). If S_i = ∅, iff all three are alone (case E). ∎

Ties need no separate treatment. A core with tied values has a strict profile consistent with them, and an allocation that is EFX₀ for that profile is EFX₀ for the tied values (L5(iv), consequence (2)). Below, profiles are strict, and a class condition on a tied core means that some consistent strict profile satisfies it.

## 1. The paper's objects in a core; popular matchings

**Dictionary (inference, from digest §4).**
- In a core, a class of goods valued by exactly two agents has at most two goods, and its only EFX₀-feasible 2-partition is the singleton split, so both cuts coincide and every unit bundle is one good.
- An orientation in which every agent holds at most one unit bundle (the paper's *simple*, Def. 2.10, p. 9) is then a partial allocation in which every agent holds at most one of its own goods. Call this a *singleton state*.
- *Unitary* (Def. 2.4(2), p. 8) says that no agent prefers a free good to its holding.
- A resented agent holds a good that its resenter prefers to its own holding (Remark 2.7, Lemma 2.8), so resent is envy of a held good.
- *Height-one* (every resent tree is a star) says that no agent both envies someone and is envied.

The lemma below is stated and proved in core terms; nothing later depends on the dictionary.

**Definitions.**
- The *f-goods* are the tops, F = {a_i : i an agent}. The *claimants* of an f-good g are the agents whose top it is.
- For an agent i, s(i) is its best good that is not an f-good; it is undefined if all three of its goods are f-goods.
- A *popular matching* is a singleton state Y in which every f-good is held by one of its claimants (the *winners* hold their tops), and every other agent i (a *loser*) holds s(i), or nothing when s(i) is undefined.

The name is from Abraham, Irving, Kavitha and Mehlhorn [unverified], whose characterization of popular matchings in house allocation has exactly this form.

**Lemma 1.1.** A singleton state is unitary and has height one iff it is a popular matching.

*Proof.* (⇐) Let Y be a popular matching.
- *Unitary.* Every f-good is held, so a free good g ∈ R_i is not an f-good. A winner ranks its top above g. A loser holding s(i) ranks s(i), its best good that is not an f-good, above g (g ≠ s(i), which is held). A loser with s(i) undefined values only f-goods, and none of them is free.
- *Height one.* Winners hold their tops and envy nobody. Suppose j envies a loser i. Then Y_i = s(i) ∈ R_j, and j ranks it above Y_j. So j is a loser. s(i) is not an f-good, so s(j) is defined, j holds s(j), and j ranks s(i) above s(j). That contradicts s(j) being j's best good outside F. So only winners are envied, and they envy nobody.

(⇒) Let Y be unitary with height one.
1. *Every envied agent holds its top.* It envies nobody. By unitarity, every good it ranks above its holding is held by another agent, whom it would envy. So nothing is ranked above its holding, which is therefore its top (it holds something: an agent holding nothing envies the holders of its three goods, which unitarity forces to be held).
2. *Every f-good g is held by a claimant.* Let i be a claimant. If i does not hold g, then g is held (unitarity) by some j whom i envies, so j holds its top by step 1, and g = a_j.
3. *Every other agent holds s(i), or nothing when s(i) is undefined.* Let i not hold a_i. Then a_i is held by another agent, whom i envies, so i is not envied (height one).
   - Suppose i holds an f-good g. Then g is not i's top, so g = a_j for a claimant j that does not hold it. j envies i, which contradicts the previous sentence.
   - A good x ∉ F that i ranks above Y_i is not free (unitarity), and it is not held by another agent: that agent would be envied by i, so by step 1 it would hold its top, and x would be an f-good.
   - So Y_i ranks at least as high as every good of i outside F. If Y_i is a good, it is not in F, so Y_i = s(i). If i holds nothing, no good of R_i lies outside F, so s(i) is undefined. ∎

**Lemma 1.2.** Let G′ be the bipartite graph on agents and goods with an edge i–a_i and an edge i–s(i) for every agent i. When s(i) is undefined, the second edge goes to a private vertex ℓ_i instead.
- (a) If G′ has a matching covering every agent, the profile has a popular matching.
- (b) If every good is the top or the s-good of at most two agents, G′ has such a matching. In particular every multigraph core (every good with at most two valuers) has a popular matching, under every profile.

*Proof.* (a) Let M cover every agent. While some f-good g is unmatched, take a claimant i of g. It is matched to s(i) or ℓ_i, since it is not matched to g; rematch it to g. The number of matched f-goods grows, and s(i) and ℓ_i are not f-goods, so this ends with every f-good matched. An f-good is adjacent only to its claimants, because s(·) is never an f-good. Let Y_i be i's matched good (nothing for ℓ_i). The agents matched to their tops are the winners, and every other agent holds s(i) or nothing. This is a popular matching.

(b) Every agent has degree exactly 2 in G′, because a_i ≠ s(i) and ℓ_i is private. By hypothesis every good has degree ≤ 2, and each ℓ_i has degree 1. So every component is a path or a cycle, and a path ends at vertices of degree ≤ 1, which are not agents. On a path h_0 i_1 h_1 … i_r h_r, match i_t with h_t; on a cycle, match each agent with the next vertex. Every agent is covered. ∎

In the paper the height-one allocation is reached from a greedy allocation by repeated BreakTree steps with a potential argument (§4 and Appendix B, pp. 12–14 and 35–39). Lemma 1.2 replaces that for cores. With a good of three valuers a popular matching may not exist (O1, §5).

## 2. States and the dump lemma (any core)

A *state* consists of the following:
- a set D of *doubled* agents, each d ∈ D holding a set Z_d ⊆ R_d of two of its goods;
- for every other agent i, a *pick* Y_i ∈ R_i ∪ {∅};
- all held goods are distinct, and the other goods are *free*.

For i ∉ D, Better(i) is the set of goods of R_i that i ranks above Y_i (all of R_i if Y_i = ∅); Better(d) = ∅ for d ∈ D. Agent i *envies* j if j holds a good of Better(i). A *top-holder* is an agent i ∉ D with Y_i = a_i.

The invariants:
- **I1** (unitary): Better(i) consists of held goods, for every i.
- **I2**: no good of a doubled agent lies in any Better(j).
- **I3**: every envied agent is a top-holder.

A popular matching, with D = ∅, satisfies I1–I3 (Lemma 1.1).

**Lemma 2.1 (dump).** Take a state satisfying I1 and I2, and let E be the set of envied agents. Let X be the complete allocation obtained as follows:
- every envied agent gets exactly its pick;
- every doubled agent d gets Z_d ∪ A_d;
- every other agent i gets {Y_i} ∪ A_i;
- the sets A_i partition the free goods, with A_j = ∅ for j ∈ E.

Suppose that (β\*) for every non-doubled i with Y_i = a_i and A_i ∩ R_i = ∅, b_i and c_i do not lie together in a bundle of X with three or more goods. Then X is EFX₀.

*Proof.* Lemma 0. Let |S_i| ≤ 1 in X; then i ∉ D. If A_i contained a good of R_i, then Y_i ≠ ∅ (by I1, an agent without a pick has all three goods held), so |S_i| ≥ 2. Hence A_i ∩ R_i = ∅, S_i = {Y_i} or ∅, and Better_i(X) = Better(i).
- (α): a good g ∈ Better(i) is held (I1) by some j ≠ i. Then j ∉ D (I2), so g = Y_j and i envies j. So j ∈ E and X_j = {g}: g is alone.
- (β) is (β\*). ∎

Lemma 2.1 does not ask the dump recipients to be unenvied. A top-holder t may hold only a_t while its b_t and c_t form a two-good bundle of another agent: t envies that bundle (b + c > a), but EFX₀ allows it. The paper's dumping keeps recipients literally unenvied (digest §2, and digest §4 item 11), and O2 shows that this cannot be kept once a good has three valuers.

## 3. The construction and its invariants

**Classes of profiles.**
- 𝒰: every good with three or more valuers is the top of each of its valuers. Equivalently (F4): every good that is someone's b or c has at most two valuers. Multigraph cores are in 𝒰 under every profile.
- 𝒯: no good with three or more valuers is anyone's top.

**Moves** on a state:
- **Up.** Agent k ∉ D is not envied, Y_k = b_k, and c_k is free. Then k becomes doubled with Z_k = {b_k, c_k}.
- **U1.** Agent w is envied, w is a top-holder, and k is an envier of w such that each of b_w, c_w is free or equal to Y_k. Then w becomes doubled with Z_w = {b_w, c_w}, and Y_k := a_w (k's old pick is released unless it went to w). This is the paper's U1 (Def. 5.5, p. 17) in core form, inference: the resenter takes the child's piece, and the child takes its leftover with its free goods.
- **R1.** Agent u is a top-holder that is not envied and has a free good g of its own. Then u becomes doubled with Z_u = {a_u, g}.

**Potential.** By L5(i) each agent's eight subsets are strictly ordered: ∅ < {c} < {b} < {a} < {b, c} < {a, c} < {a, b} < R_i. Let pos_i(S) ∈ {0, …, 7} be the position of S, and let Φ be the sum over all agents of pos_i(held goods of i).

**Lemma 3.1.** In class 𝒰 or 𝒯, each move keeps I1, I2 and I3 and increases Φ. Hence Up and U1 can be applied only finitely often.

*Proof.* **Up.**
- I1: Better sets do not change, except that k's becomes empty, and the set of held goods grows.
- I2: b_k is in no Better set because k is not envied; c_k is in none because it was free (I1).
- I3: no Better set grows, and the newly held c_k is in none, so the envied agents are among those envied before, all top-holders with unchanged picks (k itself is not envied).
- Φ: k moves from {b} to {b, c}.

**U1.** First, k envies w, so k ranks a_w above Y_k. Hence Y_k ≠ a_k, k is not a top-holder, and by I3 k is not envied: Y_k lies in no Better set. Each of b_w, c_w is free, so in no Better set (I1), or equals Y_k.
- *I1.* After the move, Better(k) is the set of goods k ranks above a_w, a subset of the old Better(k). Its goods were held by agents other than w (w held only a_w), and those holders are unchanged. For j ≠ k, Better(j) is unchanged, and the only good that may leave the held set is Y_k, which is in no Better set.
- *I2.* For Z_w = {b_w, c_w}: by the above, and because k ranks both below a_w. The good equal to Y_k was below a_w; a free one was not above Y_k (I1), hence below a_w.
- *I3.* Holdings changed only for k (now a_w) and w (Z_w, in no Better set), and no Better set grew. So a newly envied agent can only be k, envied by some i ∉ {w, k} with a_w ∈ Better(i). Then a_w has a third valuer i.
  - In 𝒯 that is impossible, because a_w is a top.
  - In 𝒰 it forces every valuer of a_w to rank it first, so a_w = a_k and k is a top-holder.

  Every other envied agent was envied before, and its pick is unchanged.
- *Φ.* w moves from {a} to {b, c}, and k moves from its pick to a_w, which it ranks higher.

**R1.** u is not envied, so a_u is in no Better set; g was free, so it is in none either. I1 holds because the held set grows, and I2 and I3 hold because nobody becomes newly envied. Φ increases (u moves from {a} to {a, b} or {a, c}).

Φ ≤ 7n, so there are finitely many moves. ∎

**The construction.** Start from a popular matching. Apply Up and U1, in any order, until neither applies; then apply R1 until it no longer applies. R1 only makes free goods held, so Up and U1 stay inapplicable. Call the result the *terminal state*.

**Lemma 3.2.** In class 𝒰 or 𝒯, the terminal state satisfies I1–I3 and:
- **(F1)** every free good is valued only by envied agents and by doubled agents;
- **(F2)** an envied agent w has at most one free good among b_w, c_w. If f is one, its *partner* p (the other of b_w, c_w) is held, by an agent h that is not envied and does not envy w;
- **(F3)** no non-doubled top-holder t has both b_t and c_t free.

*Proof.* (F1) Let i ∉ D value a free good f and not be envied. If i is a top-holder, R1 applies. Otherwise f is below Y_i (I1), and Y_i is not i's top, so Y_i = b_i and f = c_i, and Up applies. An envied agent that is not doubled is a top-holder (I3).

(F2) If b_w and c_w were both free, U1 would apply with any envier of w. Suppose f is free and p is held by h.
- *h does not envy w.* If it did, h ∉ D and p = Y_h, and U1 would apply with k = h.
- *h is not envied.* If it were, h ∉ D (I3), and h would be a top-holder with Y_h = p = a_h, envied by some i with p ∈ Better(i). Here i ≠ h, and i ≠ w because w is a top-holder (Better(w) = ∅). So p would have the three valuers w, h and i. That contradicts 𝒰, since p is w's b or c (F4), and 𝒯, since p is h's top.

(F3) For envied t this is (F2). A non-envied non-doubled top-holder has no free good of its own, since R1 no longer applies. ∎

## 4. The dump

In the terminal state, let E be the envied agents. Let O be the agents that are neither doubled nor top-holders; they are not envied (I3), and each envies the holder of its top. Define:
- **Closed** agents: the doubled d with Z_d = {b_t, c_t} for some non-doubled top-holder t.
- **Open** agents: those neither envied nor closed.
- For a free good f: W_f = {w ∈ E : f ∈ {b_w, c_w}}, and H_f = the set of holders of the partners of f with respect to the w ∈ W_f. By (F2), these holders are not envied.
- An assignment φ of the free goods to open agents is **admissible** if every open agent s either lies in no H_f with φ(f) = s, or receives exactly one good and holds exactly one good.

**Lemma 4.1.** In class 𝒰 or 𝒯, an admissible assignment turns the terminal state into an EFX₀ allocation.

*Proof.* Lemma 2.1 with A_s = φ⁻¹(s). Envied agents receive nothing, so we check (β\*). Let t be non-doubled with Y_t = a_t and no own good received. Consider where b_t and c_t are:
- Both free: excluded by (F3).
- One free (f), the other (p) held by h: t values the free good f and is not doubled, so t ∈ E (F1). Hence t ∈ W_f and h ∈ H_f. The two share a bundle only if φ(f) = h, and then admissibility makes that bundle {p, f}.
- Both held by one agent: that agent holds two goods, so it is doubled with Z = {b_t, c_t}. It is closed, receives nothing, and its bundle has two goods.
- Otherwise they lie in different bundles. ∎

**Lemma 4.2.** In class 𝒰, the terminal state has an admissible assignment.

*Proof.* Two consequences of (F4), that every b or c good has at most two valuers:
- (i) |H_f| ≤ |W_f| ≤ 2 for every free f: f is the b or c of every w ∈ W_f, so W_f ⊆ valuers of f.
- (ii) An open agent k ∈ O holds at most one good, and lies in H_f for at most one free good f. If k ∈ H_f, then k's good p is the partner of f with respect to some w ∈ W_f. So p ∈ {b_w, c_w} has valuers {k, w} (F4), which determines w, and w has at most one free good (F2).

If there is no free good, there is nothing to assign. Otherwise consider three cases.
- (b) *Some open agent s lies in no H_f.* Give it every free good; this is admissible.
- (a) *At least three open agents.* By (i), every free good f has an open agent outside H_f; send it there. This is admissible, because no open agent receives a good f with it in H_f.
- (c) *Otherwise:* at most two open agents, each lying in some H_f.
  - O ⊆ open, since agents of O are neither doubled nor envied.
  - If O = ∅, then E = ∅ (an envied agent's enviers lie in O), so every H_f is empty and case (b) applies. Here open agents exist: a closed agent needs a non-doubled top-holder t, which is itself open.
  - If O = {k}, then k envies every envied agent, so by (F2) k lies in no H_f, and case (b) applies.
  - So O = {k₁, k₂} = the open agents. Each k_i lies in some H_f, hence holds exactly one good, and by (ii) lies in exactly one H_f, for the free good β(k_i).
  - If β(k₁) = β(k₂) = f: send f to k₁ (it receives one good and holds one), and every other free good to k₂, which lies in no other H_g.
  - Otherwise send β(k₁) to k₂ and every other free good to k₁. ∎

**Theorem X.** Let a core have a strict profile in class 𝒰 with a popular matching. The construction of §3, followed by the assignment of Lemma 4.2, gives an EFX₀ allocation.

*Proof.* Lemmas 3.1, 3.2, 4.2 and 4.1. ∎

**Theorem M.** Every core in which each good has at most two valuers has an EFX₀ allocation.

*Proof.* Take a strict profile consistent with the values (§0). It is in 𝒰, because no good has three valuers. It has a popular matching by Lemma 1.2(b), so Theorem X applies. ∎

**Consequence for TARGET.** Take an instance with |R_i| ≤ 3, and reduce it to its core by L2 and L3 (`proofs/lemmas.md`, CORE). If every connected component of the core has a strict profile in 𝒰 with a popular matching, then an EFX₀ allocation exists: combine L6 with Theorem X. Theorem M re-proves the multigraph part of ledger T3 without the paper. Theorem X adds components in which goods valued by three or more agents occur, provided each of them is the top of all its valuers (and a popular matching exists). An example is agents that all rank a common good first.

**Remarks.**
1. *Which parts of the paper survive, in core form (inference).* U1 does. Greedy and Reduce Trees are replaced by the popular matching of Lemma 1.2. The support pairs, the budgets, the main cases A–H and their dumping rules are replaced by Lemma 4.2's admissible assignment. The part of the dumping that the paper needs budgets for is here the single condition (β\*), because in a core EFX₀ is ordinal (L5) and every unit bundle is one good.
2. *Bundle sizes.* In case (b) all free goods go to one agent, and every other bundle has at most two goods: the output has at most one bundle of more than two goods (conjecture D's shape). Cases (a) and (c) can spread the free goods over several agents. In the runs, case (b) applied to every multigraph profile with n ≤ 7, and to all but 102 class-𝒰 profiles with n ≤ 6. Every output of every run, in all three classes, had at most one bundle of more than two goods. Neither observation is proved.

## 5. Obstructions: where the multigraph structure stops

Brute force over all allocations, with the raw EFX₀ definition: `src/mgx_obstructions.py`, log `results/mgx_obstructions.log`. "Height one" means that no agent both envies someone and is envied, the shape of the paper's allocations (digest §2).

**O1 (no popular matching; core H3).** Three agents rank goods 0 > 1 > their own private good (goods 2, 3, 4).
- *No popular matching.* The only f-good is 0 and s(i) = 1 for all three agents, so two losers would both have to hold good 1. Equivalently, G′ has three agents and the two goods {0, 1}. By Lemma 1.1 no unitary singleton state has height one.
- *No EFX₀ allocation of height one.* Suppose 0 is not alone. At most one agent holds 0, and each of the two agents not holding 0 must hold its b = 1 and its c together (case P, since B, C and E all need 0 alone): impossible. So 0 is alone, held by some X. If 1 were not alone, an agent holding neither 0 nor 1 would need C or E, which need 1 alone: impossible. So 1 is alone, held by some Y, and the third agent Z holds the three private goods.
- In every such allocation (six in all), Y (holding its b) envies X, and Z (holding its c) envies X and Y. So Y envies and is envied.

**O2 (a single good with three valuers, with a popular matching).** Core [[0, 1, 3], [0, 2, 3], [1, 2, 3]] (n = 3, m = 4), rankings A0: 0 > 1 > 3, A1: 0 > 2 > 3, A2: 3 > 1 > 2. Good 3 is A2's top and A0's and A1's bottom. The profile is in neither 𝒰 nor 𝒯.
- *Popular matching:* A1 holds 0, A0 holds s(A0) = 1, A2 holds 3.
- *Good 0 is alone in every EFX₀ allocation.* Suppose not. A2 holds 0 in a bundle: then A0 and A1 both need case P, {1, 3} and {2, 3}, which conflict. A0 or A1 holds 0 in a larger bundle: then the other of the two needs P, and A2 is left without a safe case.
- *So 0 is alone,* held by A0 or A1: if A2 held {0}, it would hold none of its goods and would need 1, 2 and 3 alone as well, four singletons for three agents.
- *A case check* over the placements of 1, 2, 3 gives exactly four EFX₀ allocations. Listed as the owner of goods 0, 1, 2, 3: (A0, A1, A1, A2), (A0, A2, A1, A2), (A1, A0, A0, A2), (A1, A0, A2, A2).
- *In each of them some agent envies and is envied.*
  - In (A0, A1, A1, A2), A2 holds {3} and envies A1's {1, 2} (b + c > a), while A1 envies A0.
  - In (A0, A2, A1, A2), A1 envies A0, and A0 envies A2's {1, 3} (its b and c).
  - The other two are the same with A0 and A1 exchanged.

  The brute force confirms both the list and the claim.

So the paper's final shape (unenvied recipients; children envied only by their parent and envying nobody) cannot survive a single good with three valuers, even when a popular matching exists. The envy that is unavoidable here, toward a two-good bundle consisting of the envier's own b and c, is harmless for EFX₀, and Lemma 2.1 allows it.

**Where each step of the proof uses the class, and what breaks** (the paper-level list is digest §4):
- *Lemma 1.2* needs every good to be the top or s-good of at most two agents. H3 has no popular matching. At n = 3 every profile without one has at least two goods with three valuers; with one such good a popular matching always exists at n = 3 (`results/mgx_obstructions.log`, the per-core table).
- *Lemma 3.1 (U1 keeps I3)* needs the receiver k of a_w to rank a_w first whenever a_w has a third valuer. This fails when such a good is the top of some valuers but not others: after U1 a third valuer envies k, which does not hold its top. This is the core form of "moving a good drags a third agent's envy along" (digest §4 item 5). Smallest case: n = 4, m = 5, `attempts/multigraph_u1_mixed_top.md`.
- *Lemma 4.2* needs (F4): |W_f| ≤ 2, so that three open agents suffice, and at most one bad good per open agent. In class 𝒯 both can fail, since a b or c good may have three or more valuers. `attempts/multigraph_dump_class_T.md` shows the first failures of these facts (n = 5, where case (b) still applies) and the first failures of the case analysis itself (n = 6, 194 profiles). There, one free good is the b or c of three envied agents whose partners are held by all three open agents. An admissible assignment exists in all of them: the good goes alone to an open agent holding one good.
- *Not needed here:* the paper's per-pair dumping accounting and "give j all of A_j" (digest §4 items 7, 8 and 10). U1 hands w exactly its own b and c, and Lemma 2.1 replaces the accounting.

## 6. Computations and the conjecture for class 𝒯

`src/mgx.py n MODE` runs the construction on every profile of the class for every connected core with n agents (all m; cores from `src/cores_nauty.py`). It reports how many profiles have no popular matching and which dump case was used. It asserts I1–I3 after every move, and (F1), (F2) and the class-𝒰 facts at the terminal state. Every output is checked with `efx0_raw`, the raw definition under the realizations (4, 3, 2), (10, 9, 2) and (10, 6, 5). The exit status is 1 if any output is not EFX₀, or if a multigraph or 𝒰 profile with a popular matching falls outside Lemma 4.2's cases.

Results (full counts in the logs):
- Multigraph cores, n = 2, …, 7, every profile (19,354,968 profiles): every output is EFX₀; case (b) every time.
- Class 𝒰, n = 2, …, 6: every profile with a popular matching gives an EFX₀ output (2,681 of the 1,681,672 class-𝒰 profiles have no popular matching).
- Class 𝒯, n = 3, …, 6: every profile with a popular matching goes through the moves with I1–I3 and (F1)–(F2) intact. The cases (b), (a), (c) of Lemma 4.2 apply to all of them except 194 profiles with n = 6 (none with n ≤ 5); in each of those, a search finds an admissible assignment. Every output is EFX₀.

(The per-n counts are in `results/mgx_mg.log`, `results/mgx_U.log`, `results/mgx_T.log`, `results/mgx_obstructions.log`.)

**Conjecture MX-C.** In class 𝒯, the terminal state of every profile with a popular matching has an admissible assignment. With Lemmas 3.1, 3.2 and 4.1 this would extend Theorem X to 𝒰 ∪ 𝒯 (profiles with a popular matching).

What a proof must handle: in 𝒯 a free good can have three or more envied valuers, so |H_f| can exceed 2 and even cover every open agent (the n = 6 profiles above). An open agent can also be bad for several free goods (its pick is then the partner of each). Evidence: the runs above, which are exhaustive over the class for n ≤ 6, with a search for an admissible assignment wherever the case analysis fails. For n ≤ 7 EFX₀ existence itself is already certified (R1, R5); the runs test the construction, not existence.
