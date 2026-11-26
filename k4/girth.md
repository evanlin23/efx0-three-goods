# k = 4 and the girth-4 theorem of Lianeas–Sgouritsa–Sotiriou

Workstream `proof/k4-girth` (branch `claude/k4-girth`). Code in `k4/girth/`. Nothing here changes a ledger status;
the coordinator integrates.

**Status (end of burst 1).**
- §1: lemma-by-lemma digest of arXiv 2608.03171v1, read in full (PDF fetched from arxiv.org on 2026-11-26). Girth
  ≥ 3 (two agents share at most one good) is used five times (G1, G2, G3, G5, G6), girth ≥ 4 once (G4), and G4 only
  for triangles **through the special vertex 0**.
- §2: faithful implementation (`k4/girth/lss.py`), 0 failures on random girth-≥4 instances (sanity); on the k = 4
  screen and suite sets most runs still succeed; failures classified by girth use.
- §3: completion by a *sink* (Lemma SINK and Lemma PARK, proved): vertex 0 is not needed; any non-envied agent whose
  bundle no agent with leftover goods values can take the leftovers.
- §4: the linear case (girth ≥ 3, triangles allowed), which contains the hard family H_t.

---

## 1. Digest of LSS, "EFX Allocation In (Multi)Hypergraphs", arXiv 2608.03171v1 (4 Aug 2026)

Read in full from the arXiv PDF (16 pp. with references and Appendix A). Paraphrased; my inferences are marked
**(inference)**. Earlier repository entries (`proofs/citations.md`) were made from a pasted text; this reading agrees with
them.

### 1.1 Model (§2, pp. 3–4)
- Valuations v_i : 2^M → R≥0, **monotone and normalized** (not necessarily additive).
- EFX: v_i(X_i) ≥ v_i(X_j ∖ {g}) for all i, j and all g ∈ X_j. This is **EFX₀** (g ranges over all goods of X_j).
- Hypergraph G = (V, E): agents are vertices, goods are hyperedges; an edge is *irrelevant* to every vertex outside it:
  v_i(S ∪ {e}) = v_i(S) for i ∉ e. A vertex of e may still value e at 0. *Neighbours*: vertices sharing an edge.
- *Cycle* of length k (after Berge, their ref. [10]): (x₁, e₁, …, x_k, e_k, x_{k+1} = x₁) with x₁, …, x_k distinct,
  e₁, …, e_k distinct, x_t, x_{t+1} ∈ e_t. *Girth* = length of a shortest cycle (∞ if none).
- *Orientation*: every allocated edge goes to one of its endpoints. U(X): unallocated edges; U_i(X): those relevant to i.
- **Obs. 2.1** (girth ≥ 3): two vertices share at most one edge (else (i, e₁, j, e₂, i) is a 2-cycle).
- **Obs. 2.2** (girth ≥ 4): two vertices x, y of an edge e have no common neighbour outside e (else, with e_x ∋ x, v
  and e_y ∋ y, v, the cycle (x, e_x, v, e_y, y, e, x) has length 3; e_x ≠ e_y by Obs. 2.1).
- Multi-hypergraphs (§2, §4): E may repeat a vertex set; the *patch* P_e is the set of all copies of e; the girth is that
  of the underlying simple hypergraph.

**In our setting (inference).** Good g is the edge e_g = {i : v_i(g) > 0}. A good with one valuer is a size-1 edge,
a good nobody values a size-0 edge. Size-0 and size-1 edges lie on no cycle, and the proofs of §3 never use that
they are distinct: several private goods of one agent are harmless (every use of Obs. 2.1 is about two *different*
vertices). TARGET₄ says: every vertex has degree ≤ 4 (counting private goods). Girth ≥ 3 is "two agents share at most
one good": the hypergraph is *linear*.

### 1.2 Section 3: Theorem 1 (girth ≥ 4, monotone valuations, polynomial time)

Labels: an arbitrary vertex is **0**; its n₀ neighbours get labels 1..n₀; the rest n₀+1..n−1. "Vertices will be
prioritized based on their names-labels, in a decreasing order" (p. 4).

Target properties of a partial allocation X (p. 5):
1. X is a partial EFX orientation;
2. vertex 0 is non-envied, and a neighbour i of 0 may be envied only if it holds the edge it shares with 0;
3. for every i and e ∈ U_i(X): v_i(X_i) ≥ v_i(e);
4. for every **envied** i: v_i(X_i) ≥ v_i(U_i(X)).

**Algorithm 1 (FixProp3).** While some j and e ∈ U(X) have v_j(e) > v_j(X_j): j := the **maximum** such vertex;
X_j ← {argmax_{e ∈ U_j(X)} v_j(e)} (j's old bundle becomes unallocated).
**Algorithm 2.** X := empty; FixProp3; while some *envied* i has v_i(U_i(X)) > v_i(X_i): X_i ← U_i(X); FixProp3.
**Algorithm 3.** While some e ∈ U(X) contains a non-envied vertex j: X_j ← X_j ∪ {e}. Then X_0 ← X_0 ∪ U(X).

| Step | Statement | Proof idea | Girth use |
|---|---|---|---|
| Lemma 3.1 | FixProp3 maps an EFX orientation to an EFX orientation with (3) | terminates (values strictly increase); a single-edge bundle is never strongly envied; values only increase | none |
| Lemma 3.2 | after Algorithm 2: (1), (3), (4) | the loop condition is ¬(4). Line 4 keeps EFX: **"By Observation 2.1, for any other vertex j, U_i(X) contains at most one edge, say e, relevant to j"**, and (3) gives v_j(X_j) ≥ v_j(e) = v_j(U_i(X)) | **G1**: Obs. 2.1 |
| Lemma 3.3 | 0 is never envied in Algorithm 2 | 0 has the smallest label, so when FixProp3 gives 0 an edge nobody else prefers any unallocated edge; 0 is never considered in line 3 | none |
| Lemma 3.4 | after Algorithm 2, a neighbour i of 0 is envied only if it holds the edge it shares with 0 | three cases below | G2, G3 (Obs. 2.1), **G4 (Obs. 2.2)** |
| Lemma 3.5 | Algorithm 3 returns a complete EFX allocation | line 2: only endpoints of e may come to envy j, and e is the only edge they share with j, so v_k(X_j ∪ e) = v_k(e) ≤ v_k(X_k) by (3). Line 4: envied neighbours of 0 hold their shared edge (Property 2), so they value X_0 at 0; with (4), v_i(X_i) ≥ v_i(U_i) = v_i(X_0 ∪ U) | **G5** (line 2, Obs. 2.1), **G6** (line 4, Obs. 2.1: the shared edge is unique) |
| Lemma 3.6 | O(n⁶) for Algorithm 2, O(nm) for Algorithm 3 | counting | none |

Lemma 3.4 in detail (p. 6). Let i be a neighbour of 0 and X_i its final bundle.
- |X_i| > 1: any j shares at most one edge e with i (**G2**, Obs. 2.1); by EFX, v_j(X_j) ≥ v_j(X_i ∖ e′) ⊇ … = v_j(X_i)
  for e′ ≠ e in X_i, so j does not envy i.
- X_i = {e}, e not the edge f shared with 0. A neighbour j of 0 in f does not value e (**G3**, Obs. 2.1: i, j share f).
  A neighbour j of 0 outside f does not value e (**G4**, Obs. 2.2: i, j would have the common neighbour 0 outside e).
  A vertex with a label above n₀ (all non-neighbours of 0, and only those, since i ≤ n₀) did not envy i when i got
  {e}: in FixProp3 i was the maximum vertex preferring an unallocated edge; in line 4 Property (3) held. Values only
  increase afterwards.

**Where girth ≥ 4 is really used (inference).** G4 is the only use of Obs. 2.2, and it concerns two neighbours i, j
of 0 lying in different edges at 0 and sharing a third edge: a 3-cycle **through 0**. So the proof of Theorem 1 shows:
*a linear hypergraph (girth ≥ 3) in which some vertex lies on no 3-cycle has an EFX₀ allocation, for monotone
valuations* (choose that vertex as 0). Checked by the code (§2): on linear instances every failure of the algorithm
is of type G4.

### 1.3 Section 4: Theorem 2 (multi-hypergraphs)
- Theorem 2: if the underlying simple hypergraph has girth ≥ 4 and some vertex 0 has all incident edges of
  multiplicity ≤ (edge size) − 2, an EFX allocation exists (pseudo-polynomial time).
- Lemma 4.1: without that condition (one edge at 0 of multiplicity size − 1), EFX with one unallocated good reduces to
  it, so the condition is needed for this method.
- Properties (1)–(4) generalized: (3) compares with the whole unallocated part of a patch; (4) holds for **every**
  vertex i ≠ 0 (footnote 2: Algorithm 2 could be modified to give this too).
- Algorithm 4 (FixProp3Gen) uses Subroutine 7, the "minimal preferred subset" of Chaudhury et al. [their ref. 19] on one
  patch; the highest label among the vertices that prefer Z takes Z.
- Algorithm 6: if X_0 ⊆ P_e, two vertices j₁, j₂ ∈ e without goods of P_e exist (multiplicity ≤ |e| − 2); they are
  non-envied (Property 2) and park U_i(X) for i ∈ e (j₁) and U_{j₁}(X) (j₂); the rest goes to 0.
- Girth uses: Obs. 2.1 in Lemmas 4.5, 4.7 (patches instead of edges), Obs. 2.2 in Lemma 4.7 (as G4) and Lemma 4.8
  (j₁ and i ∈ e have no common neighbour outside e).
- For TARGET₄ (inference): parallel goods are goods with *equal* valuer sets. Two agents sharing two goods with
  different third valuers is a 2-cycle of the underlying simple hypergraph, so Theorem 2 does not help with the
  2-cycles of k = 4 cores. Size-1 edges at 0 violate the multiplicity condition as stated, although X_0 ⊆ private goods
  of 0 would be harmless.

### 1.4 Girth uses, named for the rest of this file

| Name | Where | What fails without it | Kind of short cycle |
|---|---|---|---|
| G1 | Lemma 3.2, Alg. 2 line 4 | j shares ≥ 2 goods with i and strongly envies U_i(X) | 2-cycle i–j |
| G2 | Lemma 3.4, \|X_i\| > 1 | a multi-good bundle of a neighbour of 0 is envied (not strongly) | 2-cycle i–j |
| G3 | Lemma 3.4, j ∈ f | j shares f (with 0) and e with i | 2-cycle i–j inside N(0) |
| G4 | Lemma 3.4, j ∉ f | i, j neighbours of 0 via different edges share e | 3-cycle through 0 |
| G5 | Lemma 3.5, Alg. 3 line 2 | k ∈ e values X_j ∪ e more than e alone | 2-cycle j–k |
| G6 | Lemma 3.5, Alg. 3 line 4 | an envied neighbour i holds one good shared with 0, X_0 holds another | 2-cycle 0–i |

A TARGET₄ counterexample must therefore contain a 2-cycle or a 3-cycle (else LSS), and a good with ≥ 3 valuers (else
Afshinmehr et al., ledger T3). By §1.2, if it has no 2-cycle, every agent lies on a 3-cycle.
