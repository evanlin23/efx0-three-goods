# Digest: "EFX Allocations Exist on Multi-Graphs"

Afshinmehr, Ashuri, Mahmoudkhan, Mehlhorn, Shahrezaei, arXiv 2606.18665v1 (17 Jun 2026), 68 pages. Read in full (reference list skipped). "p. N" is the printed page number, which matches the extraction's `[page N]` markers; the appendix is pp. 29–68. The text is paraphrased, except short quoted statements. Suspected typos of the paper are flagged. My own inferences are marked **(inference)**.

**Index convention (it matters everywhere):** for a pair {x, y}, **a_{x,y} is x's pick from y's cut, and b_{x,y} is what x leaves in y's cut (it goes to y).** "y's cut" means a 2-partition of the x–y goods that y finds EFX-feasible.

---

## 1. Setting and definitions

**Valuations (pp. 6–7).** v_i: 2^M → R≥0, monotone. *Cancelable* (Berger et al. 2022): if v(S ∪ g) > v(T ∪ g) for a good g outside S and T, then v(S) > v(T). Equivalently, a common disjoint set can be added to or removed from both sides of a comparison. Additive valuations are cancelable. **Obs. 2.1 (p. 7):** if S ⪯_i T, Q ⪯_i R, and S ∪ T is disjoint from Q ∪ R, then S ∪ Q ⪯_i T ∪ R. This is the workhorse: bundles are compared piece by piece and the pieces are united.

**Multigraph instances (p. 7).** Agents are vertices and goods are edges of a multigraph. The only condition is v_i(S) = v_i(S ∩ E_i), where E_i is the set of edges at i; incident edges may be worth 0. E_{i,j} is the set of i–j edges. E_A is the set of edges at some agent of A, and E_{A,B} the set of edges between A and B. Conclusion (p. 23): "each good is valued by at most two agents".

**Allocations (p. 7).** Partial allocations have disjoint bundles; complete means every good is allocated. An *orientation* has X_i ⊆ E_i for all i. The final allocations are complete but **not** orientations: goods get "dumped" on agents who do not value them.

**Envy, EFX (p. 7).** i *strongly envies* T with respect to S "if there exists a good g ∈ T such that v_i(T \ g) > v_i(S)". EFX means no strong envy. A part Y_ℓ of a partition is *EFX-feasible* for i if i, holding Y_ℓ, strongly envies no other part. **This is EFX₀**: g ranges over all of T, including goods worthless to i. The proofs depend on it. Any agent holding dumped goods is shown to be literally unenvied (Lemma 5.4(4) and the per-case checks). The paper never discusses EFX versus EFX₀.

**Unit bundles (Def. 2.2, pp. 7–8).** Each pair i, j gets two partitions of E_{i,j}:
- **j's cut** (a_{i,j}, b_{i,j}): both parts are EFX-feasible for j, and a_{i,j} ⪰_i b_{i,j};
- **i's cut** (a_{j,i}, b_{j,i}), symmetrically.

They must be cross-balanced:
v_i(a_{i,j}) ≥ max(v_i(a_{j,i}), v_i(b_{j,i})) ≥ min(v_i(a_{j,i}), v_i(b_{j,i})) ≥ v_i(b_{i,j}), and symmetrically for j.

So each agent's own cut is at least as balanced in her eyes as the other's cut. Useful consequences: a_{y,x} ⪰_y a_{x,y}, and b_{y,x} ⪯_y b_{x,y} (the b-bundle with first index y is y's worst piece).
- Remark 2.3: for additive valuations, j's cut is any partition maximizing j's smaller part; exponential time.
- Appendix A computes the cuts in polynomial time.
- The idea comes from Afshinmehr et al. 2025a, "defined somewhat differently".

**Unitary (Def. 2.4, p. 8).** (1) X_i ∩ E_{i,j} ∈ {a_{i,j}, b_{j,i}, ∅}: i picked from j's cut, or i holds her own cut's leftover after j picked, or i holds nothing from the pair. (2) v_i(X_i) ≥ v_i(B) for every unallocated unit bundle B (one with all of its goods unallocated).

**Resent (Def. 2.6, p. 9).** u *resents* v (u → v) if a_{u,v} ≻_u X_u. u *most-resents* v if, in addition, a_{u,v} ⪰_u a_{u,j} for all j. The resent graph G_r(X) is Def. 2.9.

**Basic / height-one / simple (Def. 2.10).**
- *Basic*: an orientation, unitary, with G_r a forest, and i → j implies X_j = a_{j,i} exactly.
- *Height-one*: basic, with every resent tree of height ≤ 1 (stars).
- *Simple*: basic, with every agent holding ≤ 1 unit bundle.

**Choose(i)** (Def. 2.13) returns i's most valuable unallocated unit bundle.

**Sets (Def. 3.1, pp. 10–11).**
- R(X): the resented agents; R_i: the agents i resents.
- A_i(X): i's best still-available share of each pair where i holds nothing. It is a_{i,j} if E_{i,j} is untouched, and E_{i,j} \ X_j if j holds a piece.
- B_i = ∪_j b_{j,i}.
- C_i = ∪_{j∈R} a_{i,j}.
- D_i = ∪_{j∈R} b_{j,i}.

**Critical path (Def. 4.1).** In a tree of height ≥ 2 with root r, the path first goes to the non-leaf child i maximizing v_r(a_{r,i}), then always to the currently most-resented child.

**Dumping vocabulary (pp. 14–15).**
- *Global dumping properties* (Def. 5.1): X is height-one, and every p → q has X_q = a_{q,p} ⪰_q b_{q,p} ∪ A_q(X).
- *Support pair* (Def. 5.2): (s, t), both non-resented, with X_s ⊆ E_{s,t}.
- "s ← U" adds U to X_s. "s ←* a_{i,j}" means s drops her piece of E_{i,j}, then takes a_{i,j}.

**Main cases (Def. 3.3, p. 11)** for a simple height-one X; the first case that applies is used.
- **A:** distinct k → i and ℓ → j with D_j ∪ a_{j,k} ≻_j X_j **and** D_i ∪ a_{i,ℓ} ≻_i X_i.
- **B:** some j → i with A_j ∪ X_j ⪰_j a_{j,i}.
- **C:** as A, first inequality only.
- **D:** at most one nontrivial resent tree.
- **E:** some j → i with A_i ∪ b_{j,i} ≻_i X_i.
- **F:** some j → i and a root k not holding a_{k,j} with a_{k,j} ∪ D_k ≻_k X_k.
- **G:** k → i and ℓ → j with [C_j ∩ E_{j,R_k}] ∪ [D_j \ E_{j,R_k}] ∪ a_{j,k} ≻_j X_j, and symmetrically for i.
- **H:** none of the above.

---

## 2. Proof architecture

**Theorem 3.4 (p. 11):** "For any multigraph instance, there exists a complete EFX allocation under cancelable valuations. Moreover, such allocations can be computed in polynomial time."

**Pipeline.**
1. Compute both cuts of every pair (Appendix A).
2. Greedy: in a fixed order, each agent takes Choose. This gives a *simple* allocation (Lemma 2.14).
3. While some resent tree has height ≥ 2, run *Reduce Trees* on it. Reduce Trees repeatedly applies *BreakTree* along critical paths: each path agent except the last takes the unit bundle she resents from her successor, and the last takes Choose. The result is **simple height-one**: resent stars, each child holding exactly a_{q,p} for her unique root p.
4. Classify into the first applicable case A–H.
5. Apply local update rules: swaps that give agents the bundles they resent, or large unions, followed by Reduce Trees to restore height-one. These rules either create one or two *support pairs* or establish the inequalities that the next step needs.
6. **Dumping:** give out every remaining unit bundle by fixed rules, many to agents who do not value it. The sinks are: a support-pair agent s; a root chosen by R(·,·) or U(·,·); agent k in case F; p* in Lemma D.1.

**Invariants.** Before dumping, X is basic, hence EFX (Obs. 2.11), and every agent has ≤ 1 resenter (Obs. 2.12). From height-one on, children resent nobody. Roots may hold several unit bundles after the updates.

**Final shape** (all cases except the explicit ones in Appendix E):
- Children keep exactly a_{q,p}. Only their parent p can envy them, and p holds the complement b_{q,p}, which p finds EFX-feasible.
- **Every other agent is unenvied.** EFX₀ forces this, because roots hold goods their viewers do not value.

**Why dumping works (design principle).** What q sees in p's bundle is decomposed by pair, X'_p ∩ E_q = ∪_j (X'_p ∩ E_{q,j}). Each piece is bounded by the matching piece of a budget that q already weakly beats (A_q, D_q ∪ a_{q,p}, or the C/D union of case G), and the bounds are combined with Obs. 2.1. **Each case's negation supplies a budget inequality that a later dumping step uses:**
- not-E gives global dumping property 2;
- not-A (not-G) makes R(i, j) (U(i, j)) well defined: which of two roots can absorb a leftover piece between two children of different trees;
- not-C and not-F bound what roots may receive;
- not-D supplies a second nontrivial tree to dump on.

**Termination.**
- Algorithm 4: the potential φ = Σ max(depth − 1, 0) ≤ n² strictly drops per call of Reduce Trees (Lemma 4.5). Each call runs ≤ n BreakTree rounds, because a frozen set U grows (Lemmas 4.3 and 4.4).
- U1 removes a resent arc.
- U2, C2 and F1 raise the value of a fixed agent, and the new bundle depends only on a pair, so at most n of them run in a row.
- C1 and C3 shrink |R_s|; F2 shrinks the resented set.

**Minor gap.** Case D ("at most one" nontrivial tree) includes the no-resent situation, but Appendix E treats exactly one tree. The no-resent case is covered only by the overview's remark (p. 4): split each pair between its endpoints, which works by unitary property (2).

---

## 3. Every lemma, in order

### §2 Preliminaries
- **Lemma 2.5 (p. 8).** In a unitary orientation, X_j ⪰_j b_{i,j} ⪰_j b_{j,i}. *Proof:* If j holds a piece of the pair, it is a_{j,i} or b_{i,j}, and a_{j,i} ⪰_j b_{i,j}. If j holds nothing, i holds ≤ 1 piece, so by orientation one of b_{i,j} and a_{j,i} is unallocated, and unitary property (2) gives X_j ⪰_j the smaller of them, b_{i,j}.
- **Remark 2.7.** In a unitary orientation, u → v forces X_v ∩ E_{u,v} = a_{v,u}: a_{u,v} is not u's (monotonicity) and not free (unitary), so v holds part of it.
- **Lemma 2.8 (p. 9).** In a unitary orientation, envy implies resent. *Proof:* X_i ∩ E_j = X_i ∩ E_{i,j} (orientation). If j envies i, i's piece beats b_{i,j} ⪰_j b_{j,i} in j's eyes, so it is a_{i,j}, and a_{j,i} ⪰_j a_{i,j} ≻_j X_j.
- **Obs. 2.11.** Basic implies EFX: an envied X_j equals a_{j,i}, and X_i ⪰_i b_{j,i} completes i's own EFX-feasible cut.
- **Obs. 2.12.** Basic implies ≤ 1 resenter per agent, since a_{j,i} ⊆ E_{i,j}.
- **Lemma 2.14 (p. 10).** Greedy gives a simple allocation. Earlier agents picked while their a-piece was still free, so they do not envy later ones. A later i sees only a_{j,i} in an earlier j, and b_{j,i} was free when i chose. Unitary: three cases. Acyclic: in any subset of agents, the earliest resents none of the others.

### §3
- **Obs. 3.2.** A_i is unallocated, and for a resented i so are C_i and D_i: pairs between two children are untouched.
- **Theorem 3.4.** A: Cor. 6.2; B: L. 7.6; C: Cor. D.3; D: Cor. E.14; E: L. F.1; F: L. G.10; G: L. H.3; H: L. 8.2.

### §4 and Appendix B: shortening trees
- **Algorithm 2, BreakTree:** on the critical path i_1 → … → i_k, X_{i_ℓ} := a_{i_ℓ,i_{ℓ+1}} (ℓ < k) and X_{i_k} := Choose. **Algorithm 3, Reduce Trees(X, i):** while the tree at the current root has height > 1, apply BreakTree and move to the returned i_k. **Algorithm 4:** while some tree is tall, apply Reduce Trees to its root.
- **Lemma 4.2 (pp. 12–13).** After BreakTree: (1) still a unitary orientation; (2) i_2..i_{k−1} resent nobody; (3) every path agent except i_{k−1} is non-resented; (4) only i_k can gain new resent arcs; (5) still a forest.
  *Key points:*
  - a_{i_ℓ,i_{ℓ+1}} is free once i_{ℓ+1} drops a_{i_{ℓ+1},i_ℓ}.
  - For the middle agents it is the most-resented bundle, hence their best overall.
  - Only i_k loses value.
  - Freed pieces lie in the path pairs or in the root's old pair. Their only other viewer either improved or did not resent the root.
  - i_{ℓ+1} does not resent i_ℓ, because a_{i_{ℓ+1},i_ℓ} ⪰ a_{i_ℓ,i_{ℓ+1}} for her.
  - i_k's pick is free, so nobody wants it. A new cycle would need i_k, who is unresented.
- **Lemma 4.3 (p. 13, pp. 35–36).** Setup: X basic, N = H ⊔ G ⊔ {h_0}, p ∈ H. Hypotheses:
  1. for r ∉ H, r's favorite i in H \ p (by v_r(a_{r,i})) does not hold a_{i,r};
  2. p holds one unit bundle in E_{p,h_0} and resents nobody;
  3. h_0 is unresented;
  4. outsiders of H hold one unit bundle each.

  Then Reduce Trees(X, h_0) stops within n rounds, H keeps its bundles, outsiders keep one unit bundle each, and h_0 stays unresented. *Proof:* a frozen set U (H plus all non-final path vertices) grows each round. Critical paths never enter U: by hypothesis 1 path agents resent nobody in U \ p, and p is a leaf, so she cannot be a non-leaf second vertex.
- **Lemma 4.4.** For simple X, Reduce Trees(X, r(T)) keeps X simple and stops in ≤ n rounds. After the first BreakTree, apply 4.3 with H = {i_1..i_{k−1}}, p = i_{k−1}, h_0 = i_k.
- **Lemma 4.5 (pp. 36–38).** Algorithm 4 reaches simple height-one in polynomial time. D_i = the length of the longest path into i, and φ = Σ max(D_i − 1, 0). Per BreakTree, φ changes by at most (#depth-≥2 agents in the next tree) − (# in the current tree). New arcs leave only the unresented new root; depth-≥2 agents of the current tree drop by 1, because the old root took her best non-leaf option. Telescoping gives a drop of ≥ 1 per Reduce Trees call.
- **Lemma 4.6 (p. 14, pp. 38–39).** As 4.3, but with X_p = a_{p,h_0}, and every resent path avoiding h_0 of length ≤ 1. Then Reduce Trees(X, h_0) gives a height-one X; H keeps its bundles and its unresented members stay unresented; no allocated unit bundle of E_{h,t} (h ∈ H, t ∉ {h, h_0}) is released; h_0 stays unresented. *Proof:* enlarge H by agents whose bundle lies in some E_{t,h}, then use 4.3. Each processed tree has height exactly 2. This is the "repair after a swap" tool for U2, C3, D.2, F1, H.2 and H.3.

### §5 and Appendix C: dumping
- **Def. 5.3, the general dumping structure:**
  1. two roots split one cut of their pair;
  2. for a support pair (s, t) that is used: t gets the rest of E_{s,t}; every other root p takes a_{p,s} (replacing b_{p,s}) and s gets b_{p,s}; s gains nothing incident to t;
  3. a root keeps a_{p,q} if she had it; if she had b_{q,p}, she ends with a_{p,q} or b_{q,p}; for a child q, p → q gives p ← b_{q,p}, and r → q with r ≠ p gives p ←* a_{p,q};
  4. every pair uses one cut and gives its pieces to distinct agents (**≤ 1 piece per pair per recipient**);
  5. children are unchanged.

  (3(c)i says "q already owns a_{p,q}"; a_{q,p} is meant. Some later rules write "p ← b_{p,u}" for p's own child u, where the complement b_{u,p} is meant.)
- **Lemma 5.4 (p. 15, pp. 39–40).** Under Defs. 5.1 and 5.3: (1) nobody loses value; (2) children are not strongly envied; (3) p → q implies q does not envy p; (4) for a support pair (s, t) that is used, nobody envies s and s strongly envies nobody.
  *Proof:*
  - (3): q sees b_{q,p}, plus ≤ 1 piece of each E_{q,j}, and each piece is ⪯_q A_q ∩ E_{q,j}. Either a_{q,j} was free, or the root j held a_{j,q} and keeps it, so only b_{j,q} = A_q ∩ E_{q,j} can be dumped. Then use Obs. 2.1 and Def. 5.1(2).
  - (4): X_s ⪰_s a_{s,p} for roots p, and s gets a_{s,q} wherever p gets b_{s,q}. Every viewer sees in s either unchanged goods (t) or ≤ 1 piece per pair, bounded by A_q or by the a-pieces the viewer receives.
- **Def. 5.5, U1:** for i → j with b_{j,i} ∪ A_j ≻_j X_j = a_{j,i}, set X'_j := b_{i,j} ∪ A_j and X'_i := a_{i,j}. The pair switches cuts, and j also takes everything free. **Lemma 5.6 (pp. 40–41):** afterwards (i, j) is a support pair, j resents nobody, no new resent arises, the allocation is still height-one, and iterating terminates. j's new goods were free (unwanted, by unitary) or b_{i,j} (unwanted by i). i's new piece is seen only by j.
- **Lemma 5.7 (pp. 41–42).** Two disjoint support pairs imply complete EFX. Apply U1 exhaustively (support pairs persist), then dump:
  - s_1 and s_2 split E_{s_1,s_2};
  - roots p take a_{p,s_i} and s_i gets b;
  - a root takes the complements from its own children;
  - a root p and another root's child u: p ←* a_{p,u}, and some s_i with p ∉ {s_i, t_i} gets b;
  - two children u, v of one root p: p gets a_{u,v} and some s_i ≠ p gets b;
  - children of different roots: s_1 gets a_{u,v} and s_2 gets b.

  Any other root is seen by anyone as one piece they did not want.

### §6–§8
- **Lemma 6.1 (pp. 16–17)** (case A). Set X'_i = a_{i,ℓ} ∪ D_i, X'_k = a_{k,i}, X'_j = a_{j,k} ∪ (D_j \ E_{i,j}) ∪ a_{j,i}, X'_ℓ = a_{ℓ,j}. The children swap partners crosswise; feasibility uses D_i ∩ E_{i,j} = b_{j,i}. All four agents become unresented (others see b_{q,i} ⪯ X_q by Lemma 2.5). This gives support pairs (k, i) and (ℓ, j); apply Lemma 5.7. **Cor. 6.2.**
- **Def. 6.3.** Not in case A, for k → i and ℓ → j: R(i, j) = k if D_j ∪ a_{j,k} ⪯_j X_j, and ℓ otherwise. R(u, v) absorbs the leftover of E_{u,v}.
- **Def. 7.1.** p *weak most-resents* q: p is unresented, q resents nobody, X_q = a_{q,p}, and a_{p,q} is p's best a-piece (p need not actually resent q).
- **Def. 7.2, U2.** Given a support pair (s, t), only t holding several unit bundles, p weak most-resenting q, and a_{t,p} ∪ (B_t \ E_{t,p}) ≻_t X_t:
  - t takes that union;
  - p takes a_{p,q};
  - every j with X_j ⊆ E_{j,t} takes a_{j,t};
  - q takes Choose;
  - then Reduce Trees(q).

  **Lemma 7.3:** the result is height-one, (s, t) persists, only t is multi-bundle, s and t gain no resent, and q weak most-resents p. By Lemma 4.6 with H = {s, t, p}; an outsider r sees X'_t ∩ E_r = b_{r,t}.
- **Lemma 7.4 (pp. 18–20).** A support pair (s, t), s resenting nobody, and X_t ⪰_t D_t ∪ a_{t,p} for all p → q with p ≠ t, give complete EFX. Apply U1 exhaustively, then dump:
  - (i) t gets the rest of E_{s,t}; roots p ←* a_{p,s} and s ← b_{p,s};
  - (ii) roots other than s: split;
  - (iii) a root takes the complements from its children;
  - (iv) a root p and a child u of r: p ←* a_{p,u}, and b goes to r if p ∈ {s, t}, else to s;
  - (v) two children of one root p: p ← a_{u,v}, s ← b;
  - (vi) children of different roots: s ← a_{u,v}, R(u, v) ← b.

  *Checks:* t sees in a root p only E_{t,p} ∪ b_{t,q} (p's children), so the hypothesis applies. A child v sees in p only a_{p,v}, plus (if R(u, v) = p) pieces bounded by a_{v,p} ∪ D_v.
- **Lemma 7.5.** A support pair (s, t), with only t multi-bundle and s resenting nobody, gives complete EFX. Apply U2 while possible (≤ n times, v_t rising), then use 7.4 (D_t ⊆ B_t \ E_{t,p}).
- **Lemma 7.6** (case B). Give j the bundle X_j ∪ A_j; then (i, j) is a support pair; apply Lemma 7.5.
- **Def. 8.1.** U(i, j) is defined like R, using the case-G inequality. (The second clause prints ∩ where \ is meant.)
- **Lemma 8.2 (pp. 21–23)** (case H; no support pair). Dump:
  - (i) roots take the complements from their children;
  - (ii) two children of root p: p ← a, and the root of another nontrivial tree ← b (not D);
  - (iii) children u ∈ R_p, v ∈ R_r: U(u, v) ← a, the other root ← b;
  - (iv) a root p and another root's child v: p ←* a_{p,v}, v's root ← b;
  - (v) roots: split.

  *Checks:* root versus root via not-F (r holds a_{r,p}, or a_{r,p} ∪ D_r ⪯ X_r). Child q versus a root p that resents someone: not-C gives a_{q,p} ∪ D_q ⪯ X_q; if some child i of p has U(q, i) = p, the not-G inequality applies.

### Appendix A: unit bundles
- Modified PR (Ashuri et al. 2025): move the good maximizing v(Y_i \ g) (for cancelable valuations, the least good) from a strongly envied bundle to the poorest. The minimum never drops (Obs. A.1).
- **Claim A.2 / Lemma A.3:** after the least good x moves, only goods worse than x move later, so there are O(m²) moves for two bundles.
- **Lemma A.4:** for two 2-partitions of one set, a larger minimum implies a no-larger maximum, and smaller imbalance implies a larger minimum and a smaller maximum. **Lemma A.5:** PR does not increase the maximum or the imbalance.
- **Algorithm 5:** Z := PR((E_{i,j}, ∅), v_i); Y := PR(Z, v_j). While Y is more balanced than Z for i: Z := PR(Y, v_i); stop (keeping Y) if the old Y is at least as balanced as the new Z for j; else Y := PR(Z, v_j). Y gives j's cut and Z gives i's cut.
- **Obs. A.6 / Cor. A.7:** both cuts are EFX-feasible and cross-balanced.
- **Lemmas A.8–A.10:** i's least good of the larger Z-part strictly decreases per round. **Cor. A.11:** ≤ m + 1 rounds.

### Appendix D: case C
- **Lemma D.1 (pp. 42–45).** Hypotheses: height-one; a support pair (s, t) with only t multi-bundle; t resents nobody; a_{t,s} is t's best unit bundle; some p*, q* ∉ {s, t} with p* weak most-resenting q*. Conclusion: complete EFX. Update rules, repeated while possible:
  - **C0:** U1 at a child of a root ≠ s gives a second support pair, then Lemma 5.7.
  - **C1:** U1-like at a child q of s (X'_q = A_q ∪ b_{s,q}, X'_s = a_{s,q}, X'_t = a_{t,s}); q becomes the new t, and |R_s| drops.
  - **C2:** U2.
  - **C3:** for s → r and a weak most-resenting p with a_{r,p} ∪ (B_r \ b_{p,r}) ⪰_r X_r: rotate t ← a_{t,s}, s ← a_{s,r}, r ← that union, p ← a_{p,q}, q ← Choose, then Reduce Trees; |R_s| drops.

  Dumping as in 7.4, with **p\*** as the extra sink (b_{u,v} for two children of s, b_{t,v} for children v of s). *Checks:* t versus roots by not-C2; s's children versus roots by not-C3.
- **Lemma D.2.** Given ℓ → j, k weak most-resenting i, only ℓ multi-bundle, and D_j ∪ a_{j,k} ≻_j X_j: set ℓ ← a_{ℓ,j}, j ← a_{j,k} ∪ D_j, k ← a_{k,i}, i ← Choose, then Reduce Trees(i). Then (ℓ, j) meets D.1. **Cor. D.3.**

### Appendix E: case D (one nontrivial star)
Root p resents q_1..q_k (sorted by v_p(a_{p,q_i})), q := q_k, the others are r_1..r_ℓ, and d := k − 1.
- **Lemma E.1.** Either complete, or a_{q_i,p} ⪰ b_{p,q_i} ∪ A_{q_i} for all i > 1. Otherwise U1 at q_i makes (q_1, p) a support pair; use 7.4.
- **Def. E.2, Update D:** p ← a_{p,q_k}, q_k ← Choose. **Obs. E.3:** the result is simple height-one, only q_k resents, and she weak most-resents p.
- **Lemma E.4.** The case ℓ = 0: two explicit complete allocations, selected by a comparison for q_1.
- **Lemma E.5.** Either complete (a support pair appears; use 7.5), or every r_i holds a_{r_i,q} and after Update D, q resents all r_i and p. This gives a **duality** X ↔ X̂: p ↔ q and the q_i ↔ the r_j. **Cor. E.6:** "non-top child ⪰ b ∪ A" inequalities for X and X̂.
- **Lemma E.7.** A dumping lemma for one tree rooted at t plus a root s, given three budget conditions; each other root's b-pieces go to t or s according to whether she holds a_{i,t} or a_{i,s}.
- **Lemmas E.8, E.9.** Either complete (a swap reaching E.7), or a specific three-piece inequality for r_1 (resp. q_1) holds.
- **Lemma E.10** (n > 4). By duality assume d ≥ 2; set p ← a_{p,q_d} and v := q_d ← Choose. The arcs are v → p → q, **not height-one**. An explicit dumping gives v most b-pieces; checks use not-B, E.6, E.8 and E.9.
- **Def. E.11 / Lemma E.12:** MinimalGreater_i(S, T) deletes goods from S while it stays ≻_i T. The result is ≻_i T and not strongly envied relative to T.
- **Lemma E.13** (n = 4). **The only place where unit bundles are broken**: Y := MinimalGreater_q(E_{v,q}, a_{q,p}); explicit allocations in five subcases. **Cor. E.14.**

### Appendices F–H
- **Lemma F.1** (case E). Apply U1 to s → t (the text prints A_s; A_t is meant). This gives a support pair; another tall tree exists (not D); apply D.1.
- **Lemma G.1.** Given a support pair (s, t), both resenting nobody, and a root k such that, if k holds a_{k,j}, then (A_j \ E_{j,k}) ∪ a_{k,j} ⪯_j X_j: complete EFX. Dump with **k as a second sink**; k is unenvied piece by piece. (Rule (vii) prints R(i, j); R(u, v) is meant.)
- **FP1–FP9 (p. 60)**, relative to (k, u, v):
  - FP1: height-one.
  - FP2: k is unresented and the only multi-bundle agent.
  - FP3: k holds no a_{k,p} with p ≠ u.
  - FP4: v weak most-resents u.
  - FP5: a budget inequality for u.
  - FP6: U1 is not applicable at k's children.
  - FP7: every j → i has a_{j,k} ∪ D_k ⪯ X_k or k holds a_{k,j}.
  - FP8: a_{j,r} ∪ D_r ⪯ X_r for k → r and j weak most-resenting.
  - FP9: U1 is not applicable anywhere.
- **F1 (Def. G.2):** k ← a_{k,j} ∪ (B_k \ E_{k,j}), agents inside E_{r,k} take a_{r,k}, j ← a_{j,i}, i ← Choose, then Reduce Trees. **Lemma G.3:** F1 gives FP1–FP5. **Lemmas G.4, G.5:** violations lead to G.1 or D.1. **Lemma G.6:** iterate F1 (≤ n times) to reach FP1–FP8. **F2 (Def. G.7) / Lemma G.8:** U1 with the root keeping its other pieces; it preserves FP1 and FP3–FP8 and removes a resented agent. **Lemma G.9:** FP1 and FP3–FP9 are reached.
- **Lemma G.10** (case F). Dumping with k as the sink; v takes b for two children of k; FP8 forces R(i, j) = r when p = k. The checks use FP5, FP7 and FP9.
- **Lemma H.1.** A simple height-one X with a support pair, past F, gives complete EFX. Dumping: a root takes a_{p,u} from others' children and u's root gets b; children of different trees: s ← a, p ← b. Checks use not-C and not-F.
- **Lemma H.2.** If a root k holds a_{k,j} while j is not the most-resented child of her root i: move i to her most-resented child, then Choose and Reduce Trees. This gives the support pair (k, j) (the text says "(p, j)"); use H.1.
- **Lemma H.3** (case G). Not-E forces X_k = a_{k,j} and X_ℓ = a_{ℓ,i}.
  - If a_{j,i} ⪰_j a_{j,k}: ℓ ← a_{ℓ,j}, j ← Choose, Reduce Trees; (k, j) is a support pair; use H.1.
  - Else also k ← a_{k,i} and i ← Y_i; (k, i) is a support pair; use 7.5.

---

## 4. Where "each good is valued by at most two agents" is used

*Follow-up:* `proofs/multigraph_extension.md` re-proves the theorem for cores (Theorem M), extends it to goods with three or more valuers when each of them is the top of all its valuers and a popular matching exists (Theorem X), and gives the smallest configurations where items 3 and 5 below break the argument (§5 there).

**What the objects become in our cores (inference).** Core agents value exactly 3 goods positively and are balanced (top < the sum of the other two).
- A pair class (the goods valued by exactly i and j) has ≤ 2 goods; 3 would isolate {i, j}, making them the whole core (n = 2, m = 3, where the cut of the 3-good class is ({a}, {b, c}), not a singleton split). For 2 goods, the only EFX₀-feasible 2-partition is the singleton split, so **both cuts coincide and every unit bundle is one good** (or ∅).
- A class of goods valued by exactly three agents has 1–2 goods (3 would isolate them) and also splits into singletons.

So unit bundles, Appendix A and cancelability are **not** the obstacle. Children always hold one unit bundle, which here is one good, so under EFX₀ they are never strongly envied. **The obstacle is keeping everyone else literally unenvied when a good has three viewers.**

The multigraph gives three facts for free:
- **(F1)** a held good is seen by ≤ 1 other agent;
- **(F2)** goods split into pair classes with a fixed two-way cut, so what y sees of x's bundle is one piece of one class;
- **(F3)** pre-dumping allocations are orientations, so envy is local to one pair.

1. **Pair notation (p. 7; Def. 3.1).** E = ⊔ E_{i,j}, and A_i, B_i, C_i, D_i are unions over partners. With hyperedges, goods split into classes E_S (S = the set of valuers). **One class piece enters the budgets of 2–3 agents at once**: z ∈ E_{j,r,w} lies in A_j, A_r and A_w. *Needs redesign.*

2. **Lemma 2.5 (p. 8), "one of b_{i,j}, a_{j,i} is unallocated".** This holds because only i and j can hold E_{i,j}. For a class {g, h} with S = {x, y, w}, x and w can hold both goods, leaving y nothing and nothing free, so the bound X_y ⪰ (the worse piece) fails. *Breaks.* Obs. 2.11 survives for single-good children, but the arguments "others see b_{q,i} ⪯ X_q" (Lemmas 6.1, 7.3) lose their justification.

3. **Lemma 2.8 and Obs. 2.12 (p. 9): envy is resent, with ≤ 1 resenter.** These use X_i ∩ E_j = X_i ∩ E_{i,j} and a_{j,i} ⊆ E_{i,j}. If x holds a good g valued by x, y and w, **both y and w can envy x**. *Breaks.* The resent graph is no longer a forest (in-degree up to deg(g) − 1); "height-one" stops meaning stars; basic property 4 has no single i. Everything keyed to *the* parent breaks: Def. 5.3 3(c), R(u, v) and U(u, v), the rule "the root takes b_{q,p}", and the checks "only r → v with r ≠ p matters". A two-parent singleton child is still EFX-safe, but her single budget must then keep **both** parents unenvied.

4. **Greedy (Lemma 2.14).** Here every greedy bundle is one good, so the result is EFX₀ and still acyclic. *Survives*, but in-degree 2 appears at once.

5. **BreakTree, Reduce Trees and the potential (Lemma 4.2, p. 13; pp. 35–38).** Three facts are used:
   - "the only unit bundle incident to i that may have become unallocated is a_{i,i_1}";
   - the piece moved to i_ℓ is seen only by i_{ℓ+1}, who improved;
   - "agent j may only resent agents who hold some incident unit bundle to her" (p. 37).

   With g ∈ E_{i_ℓ,i_{ℓ+1},w} moving from i_{ℓ+1} to i_ℓ, w's envy moves along: w → i_ℓ appears, **contradicting 4.2(3)**, and paths that φ does not count become possible. If w holds part of a 2-good class, "i_ℓ's pick from i_{ℓ+1}'s cut" is ill-defined. Freed goods can be wanted by w, violating unitary property (2). *Breaks; whether a modified potential works is unclear.* (Freeing goods from a holder whom nobody envied is harmless, by monotonicity; the damage comes from envied holders, which in-degree 2 makes common.)

6. **Lemmas 4.3 and 4.6** (hypothesis 1, and H′ built from "X_t ⊆ E_{t,h}"). These are pair-based, and the swap-repair tool behind U2, C3, D.2, F1 and H.2/H.3 inherits item 5. **Unclear.**

7. **U1 and every "give j all of A_j" step (Lemma 5.6; 7.6, C1, E.1, G.4, G.5, F2).** Non-resentment is argued as: "A_j(X) was unallocated, and the allocation was unitary", so r sees in j **one unit bundle of E_{j,r}**. *Breaks.* **Concrete failure:** r has goods x > y, z with x < y + z; y ∈ E_{j,r}, z ∈ E_{j,r,w}; r holds {x}. A class-wise A_j contains both y and z, so after U1, r sees {y, z} inside a bundle that also has goods worthless to her: strong envy (repo L5: case T fails). In a multigraph, y and z share one pair class, and A_j takes only one of them. A fix needs a per-(viewer, holder) cap ("j takes ≤ 1 good valued by r"), which conflicts with w's accounting for z. **Unclear.**

8. **U2, C3, F1: t ← a_{t,p} ∪ (B_t \ E_{t,p}), and "j with X_j ⊆ E_{j,t} gets a_{j,t}" (Lemma 7.3; D.1; G.3).** The check "an outsider r sees X'_t ∩ E_r = b_{r,t}" uses one class per viewer. With classes {t, r} and {t, r, w}, r sees two of her goods in t's bundle. *Breaks,* like item 7. The termination argument is fine.

9. **Support pairs (Def. 5.2; rule 2).** X_s ⊆ E_{s,t} makes t the only viewer of s's holding. If s holds a triple good of E_{s,t,w}, both t and w must be kept off s's dumps, which shrinks the sink. With a pure pair good the notion survives verbatim. *Needs redesign; unclear whether the cases can always produce one.*

10. **Dumping accounting (Def. 5.3 rule 4; Lemma 5.4(3)(4), pp. 39–40).** "≤ 1 piece per pair per recipient", with the dichotomy "a_{q,j} is free, or root j keeps a_{j,q} so only b_{j,q} can be dumped". This uses exactly two holders per class. A 3-member class can be spread over three agents, and the dichotomy has no analog. *Needs redesign.* Each viewer has ≤ 3 goods, so a per-good version of Lemma 5.4 is plausible, but it has not been checked.

11. **EFX₀ and dump recipients (5.4(4); every "no one envies p").** Recipients of goods they do not value must be **completely unenvied**. A dumped pair piece needs 2 checks, a triple good needs 3. Balanced agents value any two of their goods above their top (L5), so a recipient may never hold two goods of a viewer who holds < 2 of her own goods. In the multigraph proof this is enforced by per-pair budgets such as X_q ⪰ b_{q,p} ∪ A_q. For balanced single-good children, those budgets hold only when their other goods are already held by roots. *The sharpest form of the obstacle.*

12. **Case conditions A–H and all dumping rules.** These are indexed by pair configurations: root–root, root–own child, root–other child, two children of one root, children of two roots. A triple class brings new ones (three children of three trees, a child with two roots, a root plus two other children, and so on), which need new rules, new budgets and new "main cases". The order A → H, in which each case uses the earlier negations, would have to be re-derived. **Unclear; this is most of the work.**

13. **Case D (pp. 46–57).** It rests on the star structure and the X ↔ X̂ duality. E.10 uses "only p has a unit bundle from q_d" (p. 52). E.13 (n = 4) is explicit, and our certified n ≤ 6 (7) makes it unnecessary; E.10 would need redoing. **Unclear.**

14. **Goods valued by ≥ 4 agents** are allowed in our setting (the bound is on agent degree, not good degree). They make items 3, 5 and 11 worse.

**Survives:** orientations (X_i ⊆ E_i); Obs. 2.1; unit bundles (trivial here); singleton children safe; greedy EFX₀ and acyclic; the plan (structured partial allocation, then swaps, then dumping onto unenvied sinks); the termination measures, if no third-party resent is created.

**No reduction.** The paper gives none, and never mentions hypergraphs. Declaring a triple good an edge of two of its valuers violates v_w(S) = v_w(S ∩ E_w) for the third.

---

## 5. Multi-edges versus the simple-graph case

**What the paper says.** Christodoulou et al.'s proof "crucially relies on the restriction that the graph is simple" (p. 1). They raised the multigraph question (p. 2), and dumping was "necessary even in simple graph settings" (p. 4). There is no detailed comparison, and Christodoulou et al. was not read, so claims about their proof are [unverified].

**The multi-edge devices:**
1. **Two fixed, cross-balanced cuts per pair**, one by each endpoint (Def. 2.2); which cut a pair uses is decided dynamically. The picker (a_{i,j}) is envy-free toward the partner on the pair, and the partner, holding the leftover b_{i,j} of her own cut, is EFX toward her. **U1 switches a pair's cut**: the resenter picks from the child's cut, and the child keeps her leftover plus all free goods. **BreakTree also switches**: i_ℓ takes a_{i_ℓ,i_{ℓ+1}} after i_{ℓ+1} gives up a_{i_{ℓ+1},i_ℓ}. Cross-balancedness guarantees that after a switch the partner values what x now holds from the pair at most as much as her own former piece (a_{y,x} ⪰_y a_{x,y}), and that everyone beats the worst piece of both cuts (Lemma 2.5).
2. **Resent instead of envy** (Def. 2.6): a pair-local, value-based proxy that envy implies (Lemma 2.8). It makes the structure (forest, stars, critical paths) combinatorial.
3. **Unitary allocations:** ≤ 1 piece per pair per agent, and nobody wants a free unit bundle.
4. **Compensation:** the parent of a child holding a_{q,p} gets the complement b_{q,p} of the same cut.
5. Unit bundles are broken only in Lemma E.13 (n = 4).
6. The cuts are computed in polynomial time for cancelable valuations (Appendix A).

**Simple graphs (inference).** For one good g per pair, both cuts are ({g}, ∅); "unitary" means g goes to one endpoint or stays free; resent = envy of g; compensation is empty. The framework reduces to "orient, then dump".

**Our cores (inference).** When two core agents share two goods that nobody else values, both cuts are the singleton split: each agent holds at most one of the two goods, and the other good is the compensation. This is the only real work the multi-edge machinery does in multigraph cores. **But if either of the two goods also has a third valuer, the goods fall into different classes** (a 1-good pair class plus a triple class). So the common pattern "two agents share two goods whose other valuers differ" lands in the unhandled territory of §4.

---

## 6. Open problems and extensions the paper mentions

- **Broader valuation classes on multigraphs** (p. 23): monotone or subadditive. (p. 2 cites a 3-agent monotone counterexample to EFX, Akrami et al. 2026b; the paper does not say whether it is a multigraph instance.)
- **Efficiency** (p. 23): EFX together with social welfare or Nash social welfare.
- The paper hopes the work informs EFX "in structured valuation models" (p. 23). It does **not** mention hypergraphs, goods with ≥ 3 valuers, EFX orientations on multigraphs (it cites only NP-completeness for simple graphs, p. 2), bundle-size bounds, or EFX versus EFX₀.
- **Inference:** there is no bound on bundle sizes. The sinks (s, R/U roots, k, v in E.10) can accumulate many goods, so nothing like the repo's conjecture D follows. A support-pair agent s is a suggestive "single big bundle", but other roots also receive dumps.
