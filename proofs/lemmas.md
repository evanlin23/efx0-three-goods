# Lemmas L1–L11: complete proofs

Step 0 (`proof/step0-lemmas`). Every lemma of PROMPT.md §3 re-derived from the definitions and proved in full; each proof was re-read. The statements are those of PROMPT.md, made precise where needed. **Verdict: L1–L11 and the CORE reduction are all correct as stated.** No lemma is false and no proof has a gap. The imprecisions found are marked **Note**; the one with consequences for the ledger concerns conjecture D (Note after L6), not the lemmas.

`src/step0_checks.py` (log `results/step0_checks.log`) corroborates the lemmas by computer, with the raw EFX₀ definition on exact integers. That is evidence, not part of the proofs (PROMPT.md §5 rule 3). The last section assembles R1, which no longer depends on Mahara.

## 0. Definitions and two basic facts

An *instance* has agents A, goods G and additive valuations v_i ≥ 0; R_i = {g ∈ G : v_i(g) > 0}. An *allocation* X = (X_i)_{i ∈ A} partitions G (bundles may be empty). Agent i is *safe* in X if v_i(X_i) ≥ v_i(X_j ∖ {g}) for all j ≠ i and g ∈ X_j; X is *EFX₀* if every agent is safe. *EFX* asks this only for goods g with v_i(g) > 0. A good is *alone* if its bundle is exactly {g}.

**F1 (threat).** For j ≠ i and X_j ≠ ∅, agent i's constraints toward X_j say v_i(X_i) ≥ θ_i(X_j) := v_i(X_j) − min_{g ∈ X_j} v_i(g). Hence:
- θ_i(X_j) = 0 if |X_j| = 1 (a singleton is never strongly envied);
- θ_i(X_j) = v_i(X_j) if X_j contains a good outside R_i (full envy-freeness toward X_j);
- θ_i(X_j) ≤ v_i(X_j), and θ_i(X_j) depends only on the values v_i(g), g ∈ X_j.

*Proof.* v_i(X_j ∖ {g}) = v_i(X_j) − v_i(g) is largest when v_i(g) is smallest. ∎

**F2 (rotation).** Let X be EFX₀, and i_1 → i_2 → … → i_k → i_1 a cycle of its envy graph (i → j iff v_i(X_j) > v_i(X_i)). Give each i_t the bundle X_{i_{t+1}} (indices mod k) and leave the other bundles in place. The result X′ is EFX₀; no agent's value decreases, and the cycle agents' values increase strictly.

*Proof.* X′ has the same bundles as X, and v_i(X′_i) ≥ v_i(X_i) for every i (strictly on the cycle, by the envy edges). Fix i and a bundle X′_j, j ≠ i. It is some bundle X_k of X. If k ≠ i, θ_i(X_k) ≤ v_i(X_i) because X is EFX₀. If k = i, θ_i(X_i) ≤ v_i(X_i) by F1. Either way θ_i(X′_j) ≤ v_i(X_i) ≤ v_i(X′_i). ∎

## L1 Perturbation

**Lemma.** Fix n and m.
(a) If every additive instance with n agents, m goods and all values strictly positive has an EFX allocation, then every additive instance with n agents and m goods has an EFX₀ allocation.
(b) Conversely, EFX₀ for all additive (n, m)-instances gives EFX for all strictly positive ones.
(c) If an additive (n, m)-instance v has no EFX₀ allocation, there is ε₀ > 0 such that for every 0 < ε < ε₀ the strictly positive instance v^ε_i(g) := v_i(g) + ε has no EFX allocation.

*Proof.* With strictly positive values EFX and EFX₀ are the same condition, which gives (b).

(a) Let v be additive. For ε > 0, v^ε is strictly positive, so it has an EFX (equivalently EFX₀) allocation X^ε. There are only n^m allocations, so some X equals X^{1/k} for infinitely many k. For those k, all i ≠ j and all g ∈ X_j: v_i(X_i) + |X_i|/k ≥ v_i(X_j ∖ {g}) + (|X_j| − 1)/k. Letting k → ∞ gives v_i(X_i) ≥ v_i(X_j ∖ {g}). So X is EFX₀ for v.

(c) Otherwise there are ε_k → 0 for which v^{ε_k} has EFX allocations, and the argument of (a) along that sequence yields an EFX₀ allocation for v. ∎

*Consequences.* A theorem "every additive instance with (n, m) in a set S (strictly positive values suffice) has an EFX allocation" gives EFX₀ for every additive instance with (n, m) ∈ S. Examples are n ≤ 3 (Chaudhury–Garg–Mehlhorn) and m ≤ n + 3 (Mahara); both are [unverified] here, see `proofs/citations.md`. A counterexample to TARGET with n agents and m goods would give, for all small ε, a strictly positive additive instance with no EFX allocation, refuting the additive EFX conjecture.

**Note (scope).** The perturbation makes every good relevant to every agent. It therefore destroys |R_i| ≤ 3 and any graph or multigraph structure. L1 transfers only results whose hypothesis is about (n, m), or about some other class closed under the perturbation. It does *not* turn Viswanathan–Mehta-type EFX results for agents with few relevant goods, or EFX results on (multi)graphs, into EFX₀ results. This is why TARGET is not a corollary of those papers.

**Note (R1).** R1 used L1 plus Mahara for cores with m ≤ n + 3. Step 0 certified those cores directly for n ≤ 6 (last section), so R1 no longer uses L1 or Mahara.

## L2 Peeling

Current instance (A, G) with |A| ≥ 2; for i ∈ A write R_i for its relevant goods *among G*.

**Lemma.** Let i ∈ A and P ⊆ G satisfy
(i) v_i(P) ≥ v_i(R_i ∖ P), and
(ii) |P| ≤ 1, or every good of P is worthless to every agent of A ∖ {i}.
If Y is an EFX₀ allocation of the sub-instance (A ∖ {i}, G ∖ P), then X := Y together with X_i := P is EFX₀ for (A, G).

The rules of PROMPT.md are the two special cases:
- **R1**, P = {g*} with g* a most valuable remaining good of i (P = ∅, or any single good, if R_i = ∅). Condition (i) holds iff v_i(g*) ≥ v_i(R_i ∖ {g*}). For |R_i| ≤ 3 that means |R_i| ≤ 2, or R_i = {a, b, c} with v_i(a) ≥ v_i(b) + v_i(c) ("top-heavy", ties included).
- **R2**, P = the goods of R_i relevant to no other agent of A, |P| ≥ 2, v_i(P) ≥ v_i(R_i ∖ P).

*Proof.* Agent i: every other bundle Y_j lies in G ∖ P, so by F1 θ_i(Y_j) ≤ v_i(Y_j) = v_i(Y_j ∩ R_i) ≤ v_i(R_i ∖ P) ≤ v_i(P). Agent j ≠ i toward P: if |P| ≤ 1, θ_j(P) = 0 by F1; otherwise v_j(P) = 0, so θ_j(P) = 0. Agent j toward Y_k (k ≠ i, j): unchanged, and fine because Y is EFX₀ and j still holds Y_j. ∎

Agents peeled earlier do not appear here: in the recursion (CORE below) each agent is checked at the step where it is peeled, against the whole allocation of its residual instance. This is the brief's "earlier-peeled agents only see bundles from their own residual."

**Corollary L2c.** If |R_i| ≤ 2 for all i, serial dictatorship in any order is EFX₀: each agent in turn takes a most valuable remaining good, and the last agent takes all remaining goods.
*Proof.* Induction on the number of agents. With one agent there is no constraint. Otherwise the first agent i has at most 2 remaining relevant goods, so R1 applies to its pick. The rest of the procedure is serial dictatorship on (A ∖ {i}, G ∖ {pick}), EFX₀ by induction, and L2 finishes. ∎

**Remark (when serial dictatorship breaks at three goods; stated in the brief).** Let |R_i| ≤ 3 for all i and run serial dictatorship. Every agent except the last holds a singleton. Agent i is unsafe iff all three of its goods a, b, c were still there at its turn, it is balanced (v_i(a) < v_i(b) + v_i(c), a its pick), and b and c both end in the last agent's bundle, which has at least 3 goods.
*Proof.* Bundles taken before i's turn are singletons (θ = 0). If at its turn R1's condition held for the remaining goods, i is safe by the "agent i" part of the proof of L2, which uses nothing about the other agents. Otherwise its three goods remained and it is balanced. It takes a; b and c lie in singletons (θ = 0) or in the last bundle L. If only one of them is in L, θ_i(L) ≤ max(v_i(b), v_i(c)) ≤ v_i(a). If both are and L = {b, c}, θ_i(L) = max(v_i(b), v_i(c)) ≤ v_i(a). If both are and |L| ≥ 3, then L ⊄ R_i and θ_i(L) = v_i(b) + v_i(c) > v_i(a). The last agent sees only singletons and is safe. ∎

## L3 Junk

**Lemma.** Let J ≠ ∅ be the set of goods relevant to no agent of A. If (A, G ∖ J) has an EFX₀ allocation, so does (A, G).
*Proof.* Let Y be EFX₀ for (A, G ∖ J). While Y's envy graph has a cycle, rotate it (F2). EFX₀ is preserved and Σ_i v_i(Y_i) strictly increases. Only the n! assignments of the same bundles can occur, so this stops with an EFX₀ allocation Y whose envy graph is acyclic. A finite acyclic digraph has a source s (no incoming edge): v_i(Y_s) ≤ v_i(Y_i) for all i ≠ s. Let X_s := Y_s ∪ J and X_i := Y_i otherwise. For i ≠ s: θ_i(X_s) ≤ v_i(X_s) = v_i(Y_s) ≤ v_i(Y_i), since v_i(J) = 0; i's other constraints are unchanged. For s: v_s(X_s) = v_s(Y_s) and the other bundles are unchanged. ∎

## CORE: reduction of TARGET to cores

**Definition.** A *core* is an instance (A, G) with |A| ≥ 2 such that:
- (K1) |R_i| = 3 for every agent;
- (K2) every agent is *balanced*: v_i(a) < v_i(b) + v_i(c), where a is a most valuable good of R_i and b, c are the other two; equivalently, each good of R_i is worth less than the other two together. Ties between values are allowed.
- (K3) every agent has at most one *private* good (a good of R_i in no other R_j);
- (K4) every good lies in some R_i.

**Theorem.** Let N ≥ 1. If every core with at most N agents has an EFX₀ allocation, then so does every instance with at most N agents and |R_i| ≤ 3 for all i. In particular, "every core has an EFX₀ allocation" implies TARGET.

*Proof.* Induction on |A| + |G|, over instances with |R_i| ≤ 3 and 1 ≤ |A| ≤ N. With one agent, it takes everything. Let |A| ≥ 2; each case below passes to a smaller instance of the same kind (restriction only shrinks R_i):
1. Some good is relevant to no agent: L3.
2. Else some agent i has |R_i| ≤ 2, or R_i = {a, b, c} with v_i(a) ≥ v_i(b) + v_i(c): R1 and L2.
3. Else some agent i has at least two private goods; let P be all of them (|P| ∈ {2, 3}). Then v_i(P) ≥ v_i(R_i ∖ P): trivially if |P| = 3; if P = {x, y} and R_i ∖ P = {z}, then v_i(x) + v_i(y) ≥ v_i(b) + v_i(c) > v_i(a) ≥ v_i(z) by balance. So R2 and L2 apply.
4. Else (K1) holds (by 2 and |R_i| ≤ 3), and so do (K2) by 2, (K3) by 3 and (K4) by 1: (A, G) is a core with at most N agents, and has an EFX₀ allocation by hypothesis. ∎

The order in which the rules are applied does not matter for correctness.

## L4 Counting

**Lemma.** Let a core have n agents, m goods and π private goods, and let deg g = #{i : g ∈ R_i}. Then 3n = 2m − π + Σ_{g shared} (deg g − 2), π ≤ n, and m ≤ 2n, with equality iff π = n and every shared good has degree 2.
*Proof.* Count incidences: Σ_g deg g = Σ_i |R_i| = 3n. Every good has degree ≥ 1 (K4): private goods have degree 1, shared goods degree ≥ 2. So 3n = π + 2(m − π) + Σ_shared (deg g − 2). π ≤ n by (K3). Then 2m = 3n + π − Σ_shared (deg g − 2) ≤ 4n, with equality iff π = n and the sum is 0. ∎

Also m ≥ 3, since any agent has three goods. Cores with m ≤ n + 3 were covered in R1 by Mahara via L1; for n ≤ 6 they are now certified directly (last section).

## L5 The core is ordinal: cases T, P, B, C, E

Write x for v_i(x).

**Lemma.** Let agent i have R_i = {a, b, c} with a > b > c > 0 and a < b + c.
- (i) The eight subset sums are ordered 0 < c < b < a < b + c < a + c < a + b < a + b + c.
- (ii) Whether i is safe in an allocation X depends only on i's ranking and on the *local configuration* of X around i: S := X_i ∩ R_i, and for each other bundle X_j meeting R_i, the set X_j ∩ R_i together with whether X_j contains a good outside R_i.
- (iii) i is safe iff one of the following holds:
  - T: i holds a, and either i holds b or c, or b and c are not together in a bundle of ≥ 3 goods;
  - P: i holds b and c;
  - B: i holds b, and a is alone;
  - C: i holds c, and a and b are alone;
  - E: a, b and c are all alone.
- (iv) With ties (a ≥ b ≥ c > 0 and a < b + c, the labels a, b, c chosen consistently with the values), T ∨ P ∨ B ∨ C ∨ E still implies that i is safe.

*Proof.* (i) c < b < a is given; a < b + c is balance; b + c < a + c since b < a; a + c < a + b since c < b; a + b < a + b + c since c > 0.

(ii) By F1, i is safe iff v_i(S) ≥ θ_i(X_j) for every j ≠ i. Let U := X_j ∩ R_i. If U = ∅, θ = 0. If X_j contains a good outside R_i, θ = v(U). Otherwise X_j = U and θ = v(U) − min_U, which is the sum of U minus its least element, again a subset sum. Every comparison is therefore between two subset sums, which (i) decides from the ranking alone.

(iii) Threat table for j ≠ i with U = X_j ∩ R_i ≠ ∅:
- if X_j has a good outside R_i (so |X_j| ≥ |U| + 1), θ = v(U);
- if X_j = U: θ = 0 when |U| = 1; θ = the larger of the two when |U| = 2; θ = a + b when U = {a, b, c}.

Cases on S (all 8 subsets):
- S ⊇ {a, b} or S ⊇ {a, c}: v(S) ≥ a + c. Every other bundle meets R_i in at most one good, so θ ≤ b < a + c. Safe.
- S = {b, c}: v(S) = b + c > a ≥ θ for every other bundle (only a is outside). Safe.
- S = {a}: if b and c lie in different bundles, each θ ≤ b < a. If both lie in X_j: with X_j = {b, c}, θ = b < a; with X_j ⊋ {b, c}, X_j has a good outside R_i (a is i's), |X_j| ≥ 3 and θ = b + c > a. So i is safe iff b and c are not together in a bundle of ≥ 3 goods.
- S = {b}: if a is not alone, its bundle X_j is {a, c} (θ = a) or contains a good outside R_i (θ ≥ a); either way θ ≥ a > b, unsafe. If a is alone, its θ is 0, and c's bundle has θ ≤ c < b. So i is safe iff a is alone.
- S = {c}: if a is not alone, θ ≥ a > c as before. If b is not alone, its bundle is {a, b} (θ = a), or contains a good outside R_i (θ ≥ b); either way θ > c. If both are alone, all θ = 0. So i is safe iff a and b are alone.
- S = ∅: v(S) = 0. A bundle with a good of R_i and ≥ 2 goods has θ > 0 (it is v(U) > 0, or v(U) − min_U > 0 when |U| ≥ 2). So i is safe iff a, b, c are all alone.

The disjunction T ∨ P ∨ B ∨ C ∨ E describes exactly these safe configurations. T restricted to S ∋ a is the first and third bullets. P is S = {b, c} or S = {a, b, c}, both safe. B forces a ∉ S (a is alone and not i's), so S = {b} (safe iff a alone) or S = {b, c} (safe). C forces S = {c} (a, b alone and not i's), safe iff a, b alone. E is S = ∅, or S a single alone good, which is T, B or C. Conversely every safe case above is one of T, P, B, C, E.

(iv) The "safe" directions above use only a ≥ b ≥ c > 0 and a < b + c:
- T: if i also holds b or c, then v(S) ≥ a + c while every other bundle meets R_i in at most one good, so θ ≤ b ≤ a + c. If i holds only a, then b and c are in separate bundles or form exactly {b, c}, so θ ≤ b ≤ a;
- P: θ ≤ a < b + c;
- B: θ ≤ c ≤ b;
- C and E: θ = 0. ∎

*Consequences for cores.* (1) If all rankings are strict, EFX₀ of X depends only on the ranking profile (one of 6 rankings per agent, 6^n profiles). For each agent, safety is a function of its ranking and X; `tools/check_certs.py` uses this. (2) Ties are harmless. Take a core with ties and a strict profile π consistent with its values (break the ties arbitrarily). Let X be EFX₀ for π, i.e. for one strict balanced realization of π, e.g. (4, 3, 2) per agent. By (iii) every agent satisfies T/P/B/C/E for π, and by (iv) X is EFX₀ for the tied values. (The brief's closedness argument works too, but is not needed.) (3) Core agents are strictly balanced: a = b + c is top-heavy and peeled by R1.

`src/step0_checks.py` checks (i) for all 95 strict balanced integer triples with a ≤ 12. It checks (iii) against the raw definition on all 4⁶ allocations of i's 3 goods plus 3 worthless goods among 4 agents: that realizes all 47 local configurations per ranking, under 6 rankings × 95 realizations, with 0 mismatches. It checks (iv) under 48 tied realizations: 0 violations of sufficiency, and 93,672 safe-but-no-case allocations, as expected.

## L6 Components

Let Γ be the bipartite *incidence graph* on agents and goods, with an edge i–g iff g ∈ R_i.

**Lemma.** Let a core (A, G) have connected components (A_1, G_1), …, (A_r, G_r) in Γ. Each (A_k, G_k) is a connected core with |A_k| ≥ 2. If each has an EFX₀ allocation X^k, their union X is EFX₀ for (A, G). Hence a core without an EFX₀ allocation has a connected component, a connected core with no more agents, without one: minimal counterexamples are connected.
*Proof.* Goods are not isolated (K4), so every component contains an agent. For i ∈ A_k, R_i ⊆ G_k, so (K1) and (K2) hold. A good of G_k is relevant only to agents of A_k, so private goods are the same in both instances: (K3). (K4) holds by construction. If |A_k| = 1, its agent's three goods would all be private, contradicting (K3). For i ∈ A_k and j ∈ A_l with l ≠ k: X_j ⊆ G_l is disjoint from R_i, so θ_i(X_j) = 0. Inside A_k, X^k is EFX₀. ∎

**Note (conjecture D and components).** L6 composes EFX₀ allocations, but the union of allocations with one large bundle each (bundles of more than two goods) can have several. So D for disconnected cores does *not* follow from D for connected cores, and "D certified for n ≤ 6" had covered connected cores only. For TARGET this is irrelevant: L6 and connected cores suffice. D for all cores with n ≤ 6 follows from the certificates (last section):
- every component has ≥ 2 agents, so a disconnected core with n ≤ 6 has at most two components with ≥ 3 agents, and then exactly two with 3 agents each;
- every 2-agent core admits bundles ≤ 2 under every profile;
- the only 3-agent connected core that does not is H3 (`proofs/counterexamples.md`);
- H3 ⊔ H3 has, under every profile, an EFX₀ allocation with at most one large bundle (`results/certs_disconnected_6_10.json.gz`).

Mixing across components is what makes this work. Two disjoint copies of the X2 example also have such an allocation, with one bundle holding goods of both copies (`results/c2_small.log`). Whether D holds for all disconnected cores is open. It is implied by D for connected cores plus a merging argument that nobody has found yet.

## L7 Slack

**Lemma.**
- (a) For a connected core, Γ has n + m vertices and 3n edges, so its cyclomatic number is β = 3n − (n + m) + 1 = 2n − m + 1 ≥ 1 (by L4).
- (b) This part needs neither connectivity nor a core. In an allocation of m goods to n agents with e empty bundles and all bundles of ≤ 2 goods, exactly 2n − m − 2e goods are alone. If instead exactly one bundle has D ≥ 3 goods and the others ≤ 2, exactly 2n − 2 − m + D − 2e goods are alone.

*Proof.* (a) The cyclomatic number of a connected graph is |E| − |V| + 1.
(b) Let s and d count the bundles with 1 and 2 goods. In the first case s + d + e = n and s + 2d = m, so s = 2(n − e) − m. In the second, s + d + e + 1 = n and s + 2d + D = m, so s = 2(n − 1 − e) − (m − D). ∎

*Reading* (informal, used only as intuition). By L5, case B uses one alone good (a), C uses two and E three, and each alone good is someone's entire bundle. With bundles ≤ 2 the supply is 2n − m − 2e ≤ 2n − m = β − 1; a large bundle of D goods adds D − 2.

## L8 Two own goods; β = 1

**Lemma.**
- (a) In a core (ties allowed), an agent holding at least two of its three goods is safe, whatever the rest of the allocation.
- (b) A connected core has β = 1 iff m = 2n. Then every agent has exactly one private good and every shared good has degree 2. Deleting the private goods leaves a single cycle i_1, g_1, i_2, g_2, …, i_n, g_n, back to i_1. Giving each i_k its private good and g_k is EFX₀, and every bundle has 2 goods.

*Proof.* (a) Let i hold x, y ∈ R_i and let z be the third good. Every other bundle meets R_i in at most {z}, so θ ≤ v_i(z) by F1. If z is i's most valuable good, v_i(z) < v_i(x) + v_i(y) by balance. Otherwise v_i(z) ≤ max(v_i(x), v_i(y)) < v_i(x) + v_i(y).
(b) β = 2n − m + 1 = 1 iff m = 2n. By L4, equality m = 2n forces π = n, so each agent has exactly one private good (K3), and all shared goods have degree 2. Private goods are leaves; deleting them keeps Γ connected with β = 1. In the resulting graph every agent and every shared good has degree 2, and a connected graph with all degrees 2 is a cycle, alternating agents and goods since Γ is bipartite. Name it i_1, g_1, …, i_n, g_n. Agent i_k's goods are its private good p_k, g_{k−1} and g_k. The bundles {p_k, g_k} partition G, and each agent holds two of its own goods, so it is safe by (a). ∎

## L9 Size-2 criterion

**Lemma (any additive valuations).** If every bundle of X has at most 2 goods, X is EFX₀ iff v_i(g) ≤ v_i(X_i) for every agent i and every good g in a 2-good bundle X_j with j ≠ i.
*Proof.* By F1, only bundles X_j = {g, h} with j ≠ i constrain i, and X_j ∖ {g} = {h}, X_j ∖ {h} = {g}. The constraints are v_i(X_i) ≥ v_i(h) and v_i(X_i) ≥ v_i(g). ∎

## L10 Insertion

**Lemma (any additive valuations).** Let i ∈ A and a_i ∈ argmax_g v_i(g). If Y is an EFX₀ allocation of (A ∖ {i}, G ∖ {a_i}) with all bundles of ≤ 2 goods, then Y with X_i := {a_i} added is EFX₀, and all its bundles still have ≤ 2 goods.
*Proof.* Others toward {a_i}: θ = 0 (singleton). Others among themselves: unchanged. Agent i toward Y_j: |Y_j| ≤ 2 gives θ_i(Y_j) ≤ max_{g ∈ Y_j} v_i(g) ≤ v_i(a_i). ∎

*Caveats (from the brief, checked).* The residual has slack 2(n − 1) − (m − 1) = 2n − m − 1: one unit less. Its goods can be worthless to every remaining agent (i's private good, for instance), so it need not be a core. X3 in `proofs/counterexamples.md` shows that size-≤ 2 allocations can then fail.

## L11 Shapes

**Lemma.** Let Γ be the incidence graph of a connected core, β = 2n − m + 1, and Γ′ = Γ minus the private goods. Then:
- Γ′ is connected, has minimum degree ≥ 2 and cyclomatic number β.
- If β = 1, Γ′ is a cycle.
- If β ≥ 2, Γ′ is a subdivision of a connected multigraph K (loops and parallel edges allowed) with minimum degree ≥ 3 and cyclomatic number β. Such K have |V(K)| ≤ 2β − 2 and |E(K)| = |V(K)| + β − 1 ≤ 3β − 3, so for each β there are finitely many.
- For β = 2, K is the theta (2 vertices, 3 parallel edges), the dumbbell (2 vertices, a loop at each, one edge between them) or the figure-eight (1 vertex, 2 loops).
- Agents have degree ≤ 3, so a vertex of K of degree ≥ 4 (e.g. the figure-eight's) is a good. Agents with a private good have degree 2 in Γ′, so they are subdivision vertices, never branch vertices.

*Proof.* Private goods are leaves of Γ. Deleting a leaf keeps a graph connected and lowers |V| and |E| by one each, so β is unchanged. In Γ′ an agent has degree 3 minus its number of private goods, i.e. 2 or 3 by (K3), and a shared good has degree ≥ 2.
- *β = 1.* 2|E| = 2|V| with all degrees ≥ 2 forces all degrees to be 2, and a connected 2-regular graph is a cycle.
- *β ≥ 2.* Some vertex has degree ≥ 3, since otherwise β = 1 as just shown. Let B be the set of such branch vertices. The degree-2 vertices form paths and cycles. A cycle of degree-2 vertices would be a whole component of Γ′, impossible since Γ′ is connected and contains branch vertices. So each maximal path of degree-2 vertices has both outside neighbours in B. Replace each such path, with its two end edges, by one edge between those branch vertices (a loop if they coincide), and keep the edges between branch vertices. The result K has V(K) = B and deg_K = deg_{Γ′} ≥ 3 on B. Each replacement removes k vertices and k edges, so K is connected with cyclomatic number β.
- *Bounds.* From 2|E(K)| ≥ 3|V(K)| and |E(K)| = |V(K)| + β − 1 we get |V(K)| ≤ 2β − 2 and |E(K)| ≤ 3β − 3.
- *β = 2.* |V(K)| ∈ {1, 2} and |E(K)| = |V(K)| + 1. With one vertex, K has two loops: the figure-eight. With two vertices, 3 edges and degrees ≥ 3 summing to 6, both degrees are 3. Let ℓ₁, ℓ₂ be the loops and p the edges between the vertices; then 2ℓ₁ + p = 2ℓ₂ + p = 3 and p ≥ 1 by connectivity. So p = 3 (theta) or p = 1 with ℓ₁ = ℓ₂ = 1 (dumbbell). ∎

`src/step0_checks.py` checks L4, L7(a) and L11 on all 7,118 connected cores that genbg enumerates for n ≤ 6 (all m) and for n = 7, m = 11–14. It checks the counting identity, β, the minimum degree after deleting private goods, the kernel's degrees and sizes, and the β = 2 shapes. For example the 15, 25 and 37 cores with n = 5, 6, 7 and m = 2n − 1 split into theta/dumbbell/figure-eight as 8/6/1, 11/12/2 and 15/20/2.

## R1 assembled (no longer conditional on Mahara)

**Theorem (R1).** Every additive instance with at most 6 agents and |R_i| ≤ 3 for all i has an EFX₀ allocation.
*Proof.*
1. By CORE with N = 6, it suffices that every core with ≤ 6 agents has one; by L6, every connected core with 2 ≤ n ≤ 6 agents.
2. By L5, consequence (2), strict ranking profiles suffice; then EFX₀ depends only on the hypergraph (R_i)_i up to isomorphism, and on the profile.
3. By L4, 3 ≤ m ≤ 2n, which splits into three ranges:
   - m = 2n: L8.
   - 3 ≤ m ≤ n + 3: `results/certs_small_m.json.gz`, 3,182 hypergraphs.
   - n + 4 ≤ m ≤ 2n − 1, i.e. (n, m) ∈ {(5, 9), (6, 10), (6, 11)}: `results/certs_5_6.json.gz`, 251 hypergraphs.
4. Each certificate gives, per hypergraph, allocations covering all 6^n profiles. `tools/check_certs.py` re-checks the coverage from the raw EFX₀ definition, and it checks that every hypergraph is a valid connected core.
5. The hypergraph lists are complete: two independent implementations, nauty's genbg and `frontier.gen_cores`, produce them with a bijection up to isomorphism (`results/enum_crosscheck.log`, `results/enum_crosscheck_small_m.log`). ∎

The same certificates give conjecture D for every core with n ≤ 6. For connected cores, every stored allocation has at most one bundle with more than two goods (`src/step0_checks.py`, "D shape"), and β = 1 cores use bundles of 2. For disconnected cores, see the Note after L6.
