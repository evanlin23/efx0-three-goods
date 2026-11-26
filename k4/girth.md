# k = 4 and the girth-4 theorem of Lianeas–Sgouritsa–Sotiriou

Workstream `proof/k4-girth` (branch `claude/k4-girth`). Code in `k4/girth/`. Nothing here changes a ledger status;
the coordinator integrates.

**Status (end of burst 1).**
- §1 (done): lemma-by-lemma digest of arXiv 2608.03171v1, read in full (PDF fetched from arxiv.org on 2026-11-26).
  Girth ≥ 3 (two agents share at most one good) is used five times (G1, G2, G3, G5, G6), girth ≥ 4 once (G4), and G4
  only for 3-cycles **through the special vertex 0**.
- §2 (EVIDENCE): faithful instrumented implementation (`k4/girth/lss.py`): 0 failures and no invariant break on 2,000
  random girth-≥ 4 instances; on degree-≤ 4 instances with short cycles most runs still succeed, and every failure is
  one girth use (linear: only G4; with 2-cycles: mostly G5 and G6). Smallest failing configurations:
  `attempts/k4-girth-faithful.md`.
- §3 (PROVED): Lemma SINK (vertex 0 is not needed: any agent nobody envies after receiving the leftovers), Lemma PARK
  (CFKS's parking, for linear hypergraphs), Lemma SLACK (a non-envied one-good holder absorbs one leftover good).
- §4 (PROVED): **Theorem T1**: a linear instance with an agent on no 3-cycle has an EFX₀ allocation (monotone
  valuations; LSS's proof). **Proposition HT**: for t ≥ 2 this covers **every monotone profile** on the hypergraphs of
  H_t and HH_t, the families that defeat LB₄ʳ and rule F. Facts F1–F6 at Pareto-maximal partial EFX₀ orientations.
- §4 (REFUTED): Conjecture L / PL ("every Pareto-maximal partial EFX₀ orientation of a linear instance completes"):
  false on a strict linear **k = 4 core** (n = 5, m = 11; `attempts/k4-girth-linear-pl.md`), after surviving 476,158
  random Pareto-maxima. So, as with 2-cycles (P1), no value-monotone method works on linear cores; leximin maxima fail too.
- §4 (CONJECTURE LR, EVIDENCE): LSS-ROT (LSS's Algorithm 2 plus the Pareto-improving rotations F5/F6, then parking)
  never failed: 246,644 runs on random linear instances (n ≤ 16), 170,556 runs grown around the trap, every labeling
  of both counterexamples, H_t, HH_3. LR would give EFX₀ for **all linear additive instances** (any degree).
- §5: with 2-cycles the LSS architecture fails already at n = 2 (`attempts/k4-girth-sink-2cycles.md`): envied agents
  must be allowed two goods both valued by their enviers.
- Next: prove LR (what LSS's priority order guarantees that a Pareto-maximum does not: the rich sources of the
  counterexample cannot arise); classify the k = 4 cores without 2-cycles; a 2-cycle version of SLACK.

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

---

## 2. The faithful algorithm on degree-≤ 4 instances with short cycles (EVIDENCE)

`k4/girth/lss.py` implements Algorithms 1–3 literally, for additive values. The paper leaves open which envied vertex
Algorithm 2 serves (line 3), which pair (e, j) Algorithm 3 serves (line 1), and argmax ties; the code takes the largest
label / smallest good, or random choices. After every atomic step it tests the partial allocation for strong envy
(raw EFX₀) and records the first step that creates it; at the end of Algorithm 2 it evaluates Properties (1)–(4) and
why (2) fails. `classify` names the failure:
- `A2L4` (G1), `A3L2` (G5): the step that first created strong envy;
- `A3L4:G6`: the strong envier of X_0 at the last step is a neighbour i of 0 that holds a good shared with 0, while X_0
  holds another one;
- `A3L4:P2(G3)` / `A3L4:P2(G4)`: the envier holds no good shared with 0, so Property (2) failed for it, because a
  neighbour of 0 in the same edge (G3) or in another edge at 0 (G4) envies its single good.

Some runs break EFX₀ transiently and repair it later (an envier's value rises); only the final allocation counts.
An envier of X_0 at the last step is always an envied neighbour of 0: a non-neighbour values only U_i(X) there, and a
non-envied vertex has no unallocated good left after line 2 (its goods are oriented) and does not envy 0.

`python3 k4/girth/run_faithful.py` (log `results/k4_girth_faithful.log`, 279 s): per instance every vertex 0 with
three labelings (default order, two random); "some run" = some vertex 0 and labeling gives EFX₀.

| instances | runs | failures by girth use | some run EFX₀ |
|---|---|---|---|
| random girth ≥ 4, any degree (sanity), 2,000 | 33,111 | none; no invariant ever breaks | 2,000/2,000 |
| random linear, degree ≤ 4, with 3-cycles, 2,000 | 44,049 | 139, all G4 | 2,000/2,000 |
| Fano plane + private goods / AG(2,3) / PG(2,3) (degree 3, 4, 4), 300 each | 6,300 / 8,100 / 11,700 | 245 / 47 / 32, all G4 | all |
| random degree ≤ 4 with 2-cycles, 2,000 | 32,883 | 3,102: G5 2,610 (92 of them by an envied receiver), G1 336, G6 101, G4 42, G3 19 | 1,997/2,000 |
| screen set (`k4/de4/ss_screen.py`), 168 | 1,767 | 515: G6 189, G5 245, G3 50, G4 31, G1 14 | 163/168 |
| suite (`k4/suite/instances`), 164 | 1,911 | 444 | 159/164 |
| k = 4 cores n = 2, random strict profiles, 2,000 | 12,000 | 3,639: G5 3,639 | 1,849/2,000 |
| k = 4 cores n = 3, random strict profiles, 3,060 | 27,540 | 5,481: G5 4,697, G6 521, G1 229, G3 31, G4 3 | 2,999/3,060 |

So: on linear instances only G4 breaks, as §1.2 predicts; with 2-cycles the dominant failures are G5 (orienting a
leftover good to a non-envied vertex j whose bundle another valuer of that good also values) and G6 (vertex 0 and an
envied neighbour share two goods). Smallest failures found (`attempts/k4-girth-faithful.md`):
- G4: n = 3, m = 5, a triangle of agents with two private goods on one of them:
  0 = {g0: 1, g1: 7}, 1 = {g1: 1, g2: 8}, 2 = {g0: 6, g2: 7, g3: 4, g4: 1}, vertex 0 = agent 0. Agent 2 takes g2, 1 takes
  g1, 0 takes g0; agent 1 envies 2, agent 2's private goods g3, g4 go to X_0 = {g0}, and agent 2 values
  {g0, g3, g4} at 11 > 7.

## 3. Vertex 0 is not needed: completion by a sink (PROVED)

Write U for the unallocated goods of a partial allocation X, U_i = U ∩ R_i, E for the envied agents, N for the others.

**Lemma SINK** (any monotone valuations, any instance). If some agent s satisfies v_i(X_i) ≥ v_i(X_s ∪ U) for every
i ≠ s, then giving U to s turns an EFX₀ partial allocation X into a complete EFX₀ allocation.
*Proof.* Nobody envies X_s ∪ U, so nobody strongly envies it; s's value only rises; other bundles are unchanged. ∎

In LSS, s = 0 and the hypothesis is Lemma 3.5's argument. It holds whenever X has (3), (4) for the agents with
leftover goods, and s is non-envied with X_s ∩ R_i = ∅ for every i with U_i ≠ ∅: then v_i(X_s ∪ U) = v_i(U_i) ≤ v_i(X_i).
Call such an s a *clean sink*. Vertex 0 with Property (2) is a clean sink after Algorithm 3's line 2 in a girth-4
hypergraph; any other agent may serve.

The safe set of an envied agent i (after CFKS, §4.1) is S_i = {u ∈ N : v_i(X_u ∪ U_i) ≤ v_i(X_i)}.

**Lemma PARK** (linear hypergraphs, monotone valuations). Let X be a partial EFX₀ orientation with (3) for all agents
and (4) for the envied ones. Suppose every unallocated good whose valuers are all envied has a common safe vertex
u_e ∈ ∩_{i valuer of e} S_i. Orient every other unallocated good with a valuer to one of its non-envied valuers, give
each good of the first kind to u_e, and goods valued by nobody to any non-envied agent. The result Y is a complete EFX₀
allocation.
*Proof.* Bundles of envied agents are unchanged, and every agent's value weakly rises, so no new strong envy toward
them. Let u ∈ N and k ≠ u; Y_u ⊆ X_u ∪ U. If k is envied and u ∈ S_k: Y_u ∩ R_k ⊆ X_u ∪ U_k, so
v_k(Y_u) ≤ v_k(X_u ∪ U_k) ≤ v_k(X_k). Otherwise no good of the first kind valued by k went to u (k ∈ N values none
of them; k ∈ E with u ∉ S_k by the choice of u_e), so Y_u ∩ R_k consists of goods of X_u or oriented to u that k
values. All of them contain u and k, and by linearity there is at most one, f. If f ∈ X_u, v_k(f) ≤ v_k(X_u) ≤
v_k(X_k) since u is non-envied; if f ∈ U, v_k(f) ≤ v_k(X_k) by (3). So nobody envies Y_u, in particular nobody
strongly envies it, and goods valued by nobody can be added. ∎

CFKS's Lemma 13 is the case of graphs. The clean sink is the case u_e = s for all e.

**Lemma SLACK** (linear hypergraphs, monotone valuations). Let X be a partial EFX₀ orientation with (3) for all agents,
u a non-envied agent with X_u = {f}, and e an unallocated good not valued by u. Then X with X_u replaced by {f, e} is a
partial EFX₀ allocation.
*Proof.* Let k ≠ u. If k values both f and e, then (linear, f ≠ e) k is the only such agent; removing either good leaves
one good worth ≤ v_k(X_k) (f because u is non-envied, e by (3)), so k does not strongly envy {f, e}. If k values only
f, v_k({f, e}) = v_k(f) ≤ v_k(X_u) ≤ v_k(X_k); if only e, v_k({f, e}) = v_k(e) ≤ v_k(X_k) by (3). u's value rises. ∎

So a non-envied agent holding one good can absorb any one leftover good even when it is not safe for its valuers: the
EFX₀ slack of a two-good bundle replaces envy-freeness. Absorbers and Lemma PARK combine (`brute.py: park_slack`):
leftover goods go to common safe vertices or alone to distinct non-envied one-good holders that take nothing else.
In a state where every leftover good has only envied valuers (as at the Pareto-maxima of §4), the proof of Lemma PARK
goes through unchanged for the park sinks, and Lemma SLACK covers each absorber (its final bundle is {f, e}).

## 4. The linear case (girth ≥ 3; triangles allowed)

The hard family H_t of `k4/c4.md` §7 is linear (`results/pq_structure.log`), so this case is not a side issue.

**Theorem T1** (PROVED; LSS's proof, §1.2). If the hypergraph is linear and some agent lies on no 3-cycle, an EFX₀
allocation exists, for monotone valuations. *Proof.* Run LSS with that agent as 0. Obs. 2.1 holds everywhere. Obs. 2.2
is used only in Lemma 3.4 for neighbours i, j of 0 lying outside each other's edge to 0: if j ∈ X_i = {e}, then
(0, f_i, i, e, j, f_j, 0) is a 3-cycle through 0 (f_i ≠ f_j since j ∉ f_i; e ≠ f_i by assumption; e ≠ f_j since else 0, i
would share e and f_i). Every other step is as in the paper. ∎
*Corollary.* A linear counterexample to TARGET₄, if one exists, has every agent on a 3-cycle and (ledger T3) a good with
≥ 3 valuers. The code agrees: on linear instances every failure of the faithful algorithm is G4 (§2).

**Proposition HT** (PROVED). For t ≥ 2 the hypergraphs of the cores H_t (`k4/c4.md` §7) and HH_t
(`k4/lemmam_bt.md` §3) are linear, and the agent ℓ (ℓ_A in HH_t) lies on no 3-cycle. Hence, by Theorem T1, **every
monotone valuation profile on them** (in particular every additive one, not only the strict profiles of those files)
has an EFX₀ allocation, found by LSS's algorithm with ℓ as vertex 0 in polynomial time.
*Proof.* In H_t the valuers are: g_1: ℓ, x_{1,1}, x_{1,2}, x_{1,3}; g_j (2 ≤ j ≤ t): x_{j,1}, x_{j,2}, x_{j,3}, y_{j−1};
z: ℓ, y_t; a_{j,i}: x_{j,i}, y_j; b_{j,i}, c_{j,i}: x_{j,i}; u, u′: ℓ. Linear: the pairs that share a good are (ℓ, x_{1,i})
(only g_1), (ℓ, y_t) (only z), (x_{j,i}, x_{j,i′}) (only g_j), (x_{j,i}, y_j) (only a_{j,i}: y_j's other goods are
a_{j,i′} and e_j ∈ {g_{j+1}, z}) and (y_{j−1}, x_{j,i}) (only g_j). A 3-cycle through ℓ uses two different goods of ℓ that
another agent values, so g_1 and z, and has the form (ℓ, g_1, x_{1,i}, e, y_t, z, ℓ) with e shared by x_{1,i} and y_t;
y_t values only a_{t,·} and z, so for t ≥ 2 there is no such e. In HH_t the two copies share only u, valued by ℓ_A and ℓ_B;
the pairs inside a copy are as in H_t, and (ℓ_A, ℓ_B) shares only u. A 3-cycle through ℓ_A uses two of g_1^A, z^A, u, and
none of the pairs (x^A_{1,i}, y^A_t), (x^A_{1,i}, ℓ_B), (y^A_t, ℓ_B) shares a good for t ≥ 2. ∎

`k4/girth/ht_families.py` (log `results/k4_girth_ht_families.log`) builds both families from their definitions, checks
that they are isomorphic (with values) to the suite's c4-H1, c4-H2, c4-H5, lmbt-HH3, checks the two facts for t ≤ 6, and
runs LSS with vertex 0 = ℓ on 100 random additive profiles per t: EFX₀ every time, with no break of any invariant
(t ≥ 2). H_1 and HH_1 have every agent on a 3-cycle, so T1 does not apply there (H_1 has n = 5 and is certified, K4.R5).
These are the families on which LB₄ʳ needs unboundedly many rotations (Proposition H) and rule F fails (Proposition
HH, Corollary HH). The repository already had EFX₀ for their specific profiles (K4.D checks; Theorem Z covers every
H_t); Proposition HT covers every profile on these hypergraphs, by a different construction.

**Facts at a Pareto-maximum** (PROVED; linear, additive; the proofs also work for monotone valuations). Let X be a
partial EFX₀ orientation whose value vector is Pareto-maximal among all partial EFX₀ orientations (one exists: there
are finitely many). Write E / N for the envied / non-envied agents, L for the unallocated goods.
- **F1** (3) holds. Else j takes {e} alone: a one-good bundle is never strongly envied.
- **F2** Every good of L has only envied valuers. Else a non-envied valuer j adds e: a valuer k of e values X_j ∪ {e}
  at v_k(e) ≤ v_k(X_k) (by linearity k values nothing in X_j), any other k at v_k(X_j) ≤ v_k(X_k).
- **F3** Every envied agent holds exactly one good. (True in any EFX₀ orientation: an envier k values at most one good g
  of X_i, so with |X_i| ≥ 2, removing another good leaves g, which k envies.)
- **F4** (4) holds for every agent. Else i takes U_i; any k ≠ i values at most one good of it, worth ≤ v_k(X_k) by F1.
- **F5** The envy graph is acyclic. Else rotate the bundles along a cycle (each holder of a single good envied by its
  predecessor, F3): the same bundles, everyone on the cycle better off.
- **F6** Every non-envied agent r with an envy path r = r_q → ⋯ → r_0 = i to an envied agent i is safe for i:
  r ∈ S_i. Else (F4) r holds the good h shared with i and v_i({h} ∪ U_i) > v_i(x_i). Move every r_{t+1} to {x_{r_t}}
  and i to {h} ∪ U_i, releasing r's other goods. A valuer k ≠ i of h values i's new bundle at v_k(h), which is
  ≤ v_k(X_r) ≤ v_k(X_k) if k ≠ r and < r's new value if k = r; a valuer of a good of U_i values it at most v_k(X_k) by F1.
  Everyone on the path is better off and nobody is worse off: a Pareto improvement.

**Conjecture L and its weak form PL are REFUTED** (`attempts/k4-girth-linear-pl.md`). Conjecture L said that in
every linear instance every Pareto-maximal partial EFX₀ orientation completes by parks and slack absorbers (§3); PL said
only that it has some EFX₀ completion. Either would have given EFX₀ for every linear additive instance. Both survived
the random brute force (`k4/girth/linear_pm.py`: ~2.7·10⁵ Pareto-maxima of random linear instances with a 3-cycle,
n ≤ 7, ≤ 10 goods, degree ≤ 4 or ≤ 6, `results/k4_girth_linear_pm_*.log`; every non-parking maximum seen was a graph
completed by one slack absorber). They fail on hand-built instances, re-checked by an independent enumeration:
- n = 4, m = 7, three goods per agent (not a core: two agents are top-heavy);
- **a strict linear k = 4 core**, n = 5, m = 11, every agent with four goods, seven 3-cycles: 33 of its 34
  Pareto-maxima complete, one does not.

The mechanism is CFKS's second scenario with *rich* sources: for the leftover good e = {i, j}, the envier r of i is
dangerous for j, the envier s of j is dangerous for i, r and s hold two goods each (no slack absorber), and every other
non-envied agent is dangerous for i or j. So, as at k = 4 with 2-cycles (P1, `k4/sdc.md` §1), "take a Pareto-maximal
partial EFX₀ orientation and complete it" does not prove EFX₀ even for linear k = 4 cores.

**What survives** (EVIDENCE):
- *Existence forms.* On every instance tested, including both counterexamples, every maximum of welfare (Σ v_i(X_i)),
  of Nash welfare and of "Pareto-maximal, then most non-envied agents" satisfies PARK. The leximin maximum of the n = 4
  counterexample is the non-completable state, so leximin is out.
- *LSS's own order.* On both counterexamples every run of LSS's Algorithm 2 followed by the flexible sink (Lemma SINK;
  the sink chosen among all non-envied agents) ends EFX₀: FixProp3 hands out single goods by priority, so no source ends
  up holding {f, g}. On random linear instances (§2 and `k4/girth/lsflex_linear.py`) Algorithm 2 + flexible sink fails on
  about 1 run in 10⁴ and some vertex 0 always works. The smallest failing run (n = 3, m = 5, a triangle with two private
  goods) violates F6: a non-envied agent with an envy path to an envied agent is dangerous for it.
- **Algorithm LSS-ROT** (`lss.lss_rot`): LSS's Algorithm 2, and while an F5 or F6 rotation exists, apply it (a Pareto
  improvement, valid in linear hypergraphs by the proofs of F5, F6) and resume FixProp3 and Algorithm 2's loop. Values
  never decrease, so it stops, in a state with (1), (3), (4) for the envied agents, an acyclic envy graph and F6. Then
  park: orient leftover goods with a non-envied valuer to one, and give every other leftover good to some non-envied
  agent (`park_slack_state`: common safe vertices and absorbers; `park_any_state`: any choice, raw EFX₀ check).
  **Conjecture LR** (CONJECTURE): on every linear instance, for every labeling, the state LSS-ROT stops in can be
  completed by parking. With Lemma SINK this would prove EFX₀ for all linear instances. Evidence:
  `k4/girth/lssrot_linear.py` (`results/k4_girth_lssrot_*.log`, see the status block). PARK + SLACK alone is not always
  enough (one run in ~10⁵: a leftover good g8 whose valuers have disjoint safe sets, while the only absorber is also the
  only safe sink of another good g6; giving both g6 and g8 to it works, because S_i charges i for all of U_i at every
  sink).

**What a proof needs.** Take e ∈ L with no common safe vertex. By F6 every non-envied ancestor r of a valuer i of e is
safe for i but dangerous for another valuer j: it holds the good f_{rj} with v_j(f_{rj} ∪ U_j) > v_j(x_j). With degree
≤ 4, a valuer j of e has at most two dangerous agents (one for each good of j other than x_j and a good of U_j). CFKS
repair this configuration (their Lemma 11, second scenario) with a move that makes i worse off; the counterexamples show
that some such non-monotone step is necessary. A proof along LSS's lines must therefore use the priority order (to keep
sources poor) or a cardinal potential (welfare, Nash welfare).

## 5. Short cycles of length 2 (agents sharing two goods)

Every k = 4 core contains 2-cycles. There the LSS architecture itself fails, not just a lemma
(`attempts/k4-girth-sink-2cycles.md`): on the n = 2 core with two equal agents (8, 5, 4, 2) the only EFX₀ allocation
gives an envied agent two goods, which no run of Algorithm 2 followed by any sink, with or without the G5 repair,
produces. On GM4-E some Pareto-maximal partial EFX₀ orientation has no completion. With the flexible sink and the G5
repair, the architecture succeeds on 162/168 screen instances and 1,270/1,275 sampled n = 3 core profiles (for some
vertex 0), failing mostly at n = 2. So any extension to 2-cycles must let an envied agent hold two goods that its envier
both values (EFX₀ slack, as in Lemma SLACK), and must not be value-monotone (P1, `k4/sdc.md` §1).
