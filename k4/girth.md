# k = 4 and the girth-4 theorem of Lianeas–Sgouritsa–Sotiriou

Workstream `proof/k4-girth` (branch `claude/k4-girth`). Code in `k4/girth/`. Nothing here changes a ledger status;
the coordinator integrates.

**Status (burst 5, in progress).** Refereed CORRECT by the coordinator's review: Theorem T1, Proposition HT, Lemmas
SINK, PARK, SLACK (general). Everything else below is as marked.
- §6 (CERTIFIED, the coordinator's decisive test): **DYN∃ holds on every connected k = 4 core with n ≤ 4 and on every
  n = 5 core with one 4-good agent**: for every strict profile SOME labeling of LSS's Algorithm 2 (G1 repair) followed
  by dynamic parking with envy-cycle rotation completes. Exhaustive covering of the order types (`k4/girth/dyncert.py`):
  n = 2, 3 (all), n = 4 with one, two, three 4-good agents (all 783; 3.6·10¹⁰ profiles), pure n = 4 (running), n = 5 with
  one 4-good agent (all 1,735). No profile where every labeling fails. Independent second covering through `lss.py`
  with symbolic values (`k4/girth/dyncert_sym.py`): n = 2, n = 3 and n = 4 with one 4-good agent agree (all certified).
- §6 (findings): the n default labelings (choice of vertex 0 only) suffice at n = 3 and on the n = 5 cores with one
  4-good agent; **no labeling rule that reads only the hypergraph exists** (REFUTED: 6 of 51 n = 3 cores,
  `attempts/k4-girth-uniform-labeling.md`); exchange moves do not remove the dependence.
- §6 (CONJECTURE DOM, new main candidate): for EVERY labeling, Algorithm 2's state has a dominating complete EFX₀
  allocation. Exhaustive at n = 3 (all 300 labelings, every profile; one implementation), no failure in 766,395 n = 3
  and 101,316 n = 4 random profiles. DYN's parking misses these completions (they need generalized rotations).
- §7 (EVIDENCE, coordinator's question): every known OC₁^max failure (all 112,880 at n = 4, 24 stored at n = 5)
  has pattern P\*: one receiver, and either two truly dangerous agents sharing two junk goods (n = 4) or a pick swap of
  a dangerous agent with the receiver (n = 5); about 5% of OC₁-holding starts have it. "A 2-cycle through two
  dangerous agents" fails at n = 5 (5_pure#72).
- Earlier bursts: §1 digest (girth ≥ 3 used five times, girth ≥ 4 once, only for 3-cycles through vertex 0); §2
  faithful runs (EVIDENCE); §3 Lemmas SINK, PARK, SLACK, §5 Lemma EC and stuck states (PROVED); §4 Theorem T1,
  Proposition HT (PROVED), PL and LR (REFUTED), LR-dyn (CONJECTURE); §5 DYN evidence and refuted variants.
- Next: pure n = 4 and the independent covering on samples of the larger classes (running); a second exhaustive
  encoding of DOM; a proof route for DOM (a completion lemma for Algorithm 2's states).

**Ledger candidates** (for the coordinator; LEDGER.md is not edited here). Proposed IDs:

| ID | Claim | Status | Artifact |
|---|---|---|---|
| K4.GIRTH.DIG | Digest of LSS 2608.03171v1: girth uses G1–G6; girth ≥ 4 only for 3-cycles through vertex 0 | read | `k4/girth.md` §1 |
| K4.GIRTH.T1 | Linear instance + an agent on no 3-cycle ⟹ EFX₀ (monotone valuations) | PROVED (written, not refereed) | §4 |
| K4.GIRTH.HT | Every monotone profile on the hypergraphs of H_t, HH_t (t ≥ 2) has an EFX₀ allocation (by T1) | PROVED (written, not refereed) | §4, `k4/girth/ht_families.py` |
| K4.GIRTH.LEM | Lemmas SINK, PARK (linear), SLACK (any hypergraph); facts F1–F6 at Pareto-maxima (linear) | PROVED (written, not refereed) | §3, §4 |
| K4.GIRTH.PL | Every Pareto-maximal partial EFX₀ orientation of a linear instance completes | REFUTED (strict linear k = 4 core, n = 5) | `attempts/k4-girth-linear-pl.md`, `attempts/k4_girth_attempts.py` |
| K4.GIRTH.LR | LSS-ROT's final state on a linear instance completes by static parking, every labeling | REFUTED (n = 4) | `attempts/k4-girth-lr-static.md` |
| K4.GIRTH.LRD | Same with dynamic parking (⟹ EFX₀ for all linear instances) | CONJECTURE | §4, `results/k4_girth_lrdyn_*.log` |
| K4.GIRTH.DYN | Some labeling of LSS's Algorithm 2 (G1 repair) + dynamic parking completes (⟹ TARGET₄) | CONJECTURE | §5, `results/k4_girth_dyn_*.log`, `results/k4_girth_dyn_ksens.log` |
| K4.GIRTH.EC | Lemma EC; stuck states of parking with envy-cycle rotation have every non-envied agent holding ≥ 2 goods | PROVED (written, not refereed) | §5 |
| K4.GIRTH.DYNEC | Every labeling completes with envy-cycle rotation | REFUTED (rare, ~3·10⁻⁵ per run) | `results/k4_girth_dynec_*.log` |
| K4.GIRTH.Z2 | Vertex 0 on no 2-cycle ⟹ every order completes | REFUTED (n = 4, m = 7) | `results/k4_girth_dyn_zero2_*.log`, §5 |
| K4.GIRTH.FAITH | Faithful LSS on degree-≤ 4 instances with short cycles: failures by girth use | EVIDENCE | §2, `results/k4_girth_faithful.log`, `attempts/k4-girth-faithful.md` |
| K4.GIRTH.SINK2 | LSS's orientation + one sink with 2-cycles | REFUTED (n = 2) | `attempts/k4-girth-sink-2cycles.md` |
| K4.GIRTH.DYNP | DYN without the G1 repair | REFUTED (n = 4 core profile) | `attempts/k4-girth-dyn-plain.md` |
| K4.GIRTH.DYN4 | DYN∃ (some labeling; Algorithm 2 with the G1 repair, then dynamic parking with envy-cycle rotation) completes on every strict profile of every connected k = 4 core with n ≤ 4, and of every n = 5 core with one 4-good agent | CERTIFIED (pure n = 4 running; independent covering for n ≤ 3 and n = 4 with one 4-good agent) | §6, `k4/girth/dyncert.py`, `k4/girth/dyncert_sym.py`, `results/k4_girth_dyncert_*.log`, `results/k4_girth_dyncert_sym_*.log`, `results/k4_girth_dyncert_selftest.log`, `results/k4_girth_dyncert_xcheck.log` |
| K4.GIRTH.UNI | One labeling per core hypergraph works for every profile | REFUTED (n = 3, m = 6) | `attempts/k4-girth-uniform-labeling.md`, `attempts/k4_girth_uniform.py`, `results/k4_girth_dyncert_3_uniform.log` |
| K4.GIRTH.DYNX | With exchange moves in the parking, every labeling completes | REFUTED (n = 3: 253 of 300 labelings) | `k4/girth/dynx.py`, `results/k4_girth_dynx_3.log` |
| K4.GIRTH.DOM | For every labeling, Algorithm 2 (G1 repair) leaves a state with a dominating complete EFX₀ allocation (⟹ TARGET₄) | CONJECTURE (exhaustive at n = 3 by one implementation) | §6, `k4/girth/dom_test.py`, `results/k4_girth_dom_*.log` |
| K4.GIRTH.OCCYC | Every known OC₁^max failure has pattern P\* (one receiver; a D_T pair sharing two junk goods, or a dangerous–receiver pick swap); "a 2-cycle through two dangerous agents" fails at n = 5 | EVIDENCE | §7, `k4/girth/oc1_cycles.py`, `results/k4_girth_oc1_cycles.log` |

---

## 1. Digest of LSS, "EFX Allocation In (Multi)Hypergraphs", arXiv 2608.03171v1 (4 Aug 2026)

Read in full from the arXiv PDF (15 pp.: main text pp. 1–12, references, Appendix A = Subroutine 7; the reference list
was only skimmed). Paraphrased; my inferences are marked
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
- Algorithm 4 (FixProp3Gen) uses Subroutine 7 (Appendix A: "Algorithm 3 of [19]", their ref. [19] being Chaudhury,
  Kavitha, Mehlhorn, Sgouritsa, "A Little Charity Guarantees Almost Envy-Freeness", SIAM J. Comput. 2021 [not read
  here]): starting from Z = S, for each agent and each good g, drop g whenever the agent envies Z ∖ {g}; the result is a
  set none envies a proper subset of. The highest label among the vertices that prefer Z takes Z.
- Algorithm 6: if X_0 ⊆ P_e, two vertices j₁, j₂ ∈ e without goods of P_e exist (multiplicity ≤ |e| − 2); they are
  non-envied (Property 2) and park U_i(X) for i ∈ e (j₁) and U_{j₁}(X) (j₂); the rest goes to 0.
- Girth uses: Obs. 2.1 in Lemmas 4.5, 4.7 (patches instead of edges), Obs. 2.2 in Lemma 4.7 (as G4) and Lemma 4.8
  (j₁ and i ∈ e have no common neighbour outside e).
- Reading §4's proof as in §1.2 below (inference, not written out or checked line by line): Obs. 2.2 is used in
  Lemma 4.7 for 3-cycles through 0 and in Lemma 4.8 for 3-cycles that use the edge e ⊇ X_0 (which contains 0), so
  Theorem 2 should hold when the underlying simple hypergraph is linear and no 3-cycle passes through 0 or uses an edge
  at 0. On the certified k = 4 cores this would cover only 4 of 1,002 (n = 4) and 18 of 31,584 (n = 5) hypergraphs
  (scratch count), fewer than Theorem T1, so it is not pursued.
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
- `A3L4:G5env` (counted as G5): an earlier line-2 step made its receiver envied (not strongly; a 2-cycle), which
  Lemma 3.5 excludes with Obs. 2.1; that receiver's later leftovers reached X_0.

Some runs break EFX₀ transiently and repair it later (an envier's value rises); only the final allocation counts.
If no earlier step broke an invariant, an envier of X_0 at the last step is an envied neighbour of 0: a non-neighbour
values only U_i(X) there, and a non-envied vertex has no unallocated good left after line 2 (its goods are oriented) and
does not envy 0. With 2-cycles, line 2 can make its receiver envied without strong envy (`A3L4:G5env`); that receiver
may be a non-neighbour of 0, whose later leftovers then reach X_0.

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

**Lemma SLACK** (any hypergraph, monotone valuations). Let X be a partial EFX₀ allocation with (3) for all agents,
u a non-envied agent with X_u = {f} (or X_u = ∅), and e any unallocated good. Then X with X_u replaced by X_u ∪ {e} is a
partial EFX₀ allocation.
*Proof.* Let k ≠ u. If k values both f and e, removing either good leaves one good worth ≤ v_k(X_k) (f because u is
non-envied, e by (3)), so k does not strongly envy {f, e}. If k values only f, v_k({f, e}) = v_k(f) ≤ v_k(X_u) ≤
v_k(X_k); if only e, v_k({f, e}) = v_k(e) ≤ v_k(X_k) by (3). u's value does not drop. (X_u = ∅: a one-good bundle is
never strongly envied.) ∎
(An earlier draft assumed linearity; it is not used. With 2-cycles several agents may value both f and e, and each is
covered by the first case.)

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
*Valuation class.* "Monotone" means LSS's hypergraph model (§1.1): v_i monotone and normalized, and a good g changes
only the values of the agents in its edge e_g (v_i(S ∪ {g}) = v_i(S) for i ∉ e_g); for additive valuations e_g is the
set of agents valuing g positively. EFX can fail for general monotone, even submodular, valuations (2604.18216,
2605.06451; `proofs/citations.md`). T1 does not contradict this: it is LSS's own argument in LSS's own model, and it
needs a linear hypergraph with an agent on no 3-cycle. Everything used for TARGET₄ here is additive.
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
(t ≥ 2). H_1 and HH_1 have every agent on a 3-cycle, so T1 does not apply there (H_1 is a pure n = 5 core, covered by the certified row K4.R5p).
These are the families on which LB₄ʳ needs unboundedly many rotations (Proposition H) and rule F fails (Proposition
HH, Corollary HH). The repository already had EFX₀ for their specific profiles (K4.D checks; Theorem Z covers every
H_t); Proposition HT covers every profile on these hypergraphs, by a different construction.

*Other gadget families* (`k4/girth/dyn_families.py`, log `results/k4_girth_dyn_families.log`; builders copied from
`k4/d_stress.py`). The multi-head chains and the gadget trees of `k4/d_stress.md` are linear, and their (first) head is
on no 3-cycle for t ≥ 2 by the argument of Proposition HT: the head's shared goods are its gadget-1 good, valued by that
gadget's x's (and, in a tree, a joining agent), and z, valued by the other heads and by chain-end or leaf y's, and none
of the former shares a good with any of the latter. (Checked on the instances built: chains t = 2, 3 with up to 3 heads,
trees t = 3, 5; a general proof for every tree shape is not written out.) So Theorem T1 covers every profile on them. The
cycles of gadgets (no head) have every agent on a 3-cycle, so only Conjecture LR-dyn speaks to them.

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
the random brute force (`k4/girth/linear_pm.py`: 476,158 Pareto-maxima of random linear instances with a 3-cycle,
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
  *park*: give every leftover good to some non-envied agent (`park_slack_state`: common safe vertices and absorbers;
  `park_any_state`: exhaustive backtracking over all such choices, raw EFX₀ check).
  **Conjecture LR (static parking) is REFUTED** (`attempts/k4-girth-lr-static.md`): on a linear instance with n = 4,
  m = 8 (K₄ plus two private goods), 6 of the 24 labelings end in a state that no static parking completes. It had
  survived 531,400 random runs (`results/k4_girth_lssrot_d4.log`), 133,800 runs on every linear k = 4 core with n ≤ 6
  (`results/k4_girth_lssrot_cores.log`) and the adversarial climbs (`results/k4_girth_lr_climb_*.log`); the search grown
  around the trap found it (`results/k4_girth_lssrot_trap.log`).
  **Conjecture LR-dyn** (CONJECTURE): on every linear instance, for every labeling, LSS-ROT's final state is completed
  by *dynamic* parking (§5: receivers non-envied at the moment they receive). It completes all 24 labelings of that
  instance and both earlier counterexamples; no failure in 503,403 runs on random linear instances and 954,435 runs
  grown around the traps (`results/k4_girth_lrdyn_{random,trap}.log`). LR-dyn would give
  EFX₀ for all linear additive instances (any degree).
  Notes. (i) PARK alone fails at LSS-ROT states, rarely (about 1 run in 3·10⁴), at goods with two or three valuers;
  PARK + SLACK then usually works, and once a refined choice was needed (S_i charges i for all of U_i at every sink).
  (ii) The completion must choose where goods with a non-envied valuer go: orienting such a good to a one-good absorber
  can spoil its slack (three false alarms of an earlier, non-exhaustive search, rechecked and completable). (iii) Static
  parking cannot use an agent that stops being envied during the completion; in the counterexample that is exactly what
  is needed.
- *Coverage of Theorem T1 on small cores* (`k4/girth/core_stats.py`, `results/k4_girth_core_stats.log`): of the
  certified k = 4 core hypergraphs, 3 of 51 (n = 3), 24 of 1,002 (n = 4), 261 of 31,584 (n = 5) and 325 of 26,866
  (n = 6, one 4-good agent) are linear; T1 applies to 0, 5, 77 and 129 of them, LSS's girth-4 condition to 0, 5, 18 and
  14. Small cores are dominated by 2-cycles; the linear structure appears in long cores such as H_t.

**What a proof needs.** Take e ∈ L with no common safe vertex. By F6 every non-envied ancestor r of a valuer i of e is
safe for i but dangerous for another valuer j: it holds the good f_{rj} with v_j(f_{rj} ∪ U_j) > v_j(x_j). With degree
≤ 4, a valuer j of e has at most two dangerous agents (one for each good of j other than x_j and a good of U_j). CFKS
repair this configuration (their Lemma 11, second scenario) with a move that makes i worse off. The counterexamples show
that Pareto-maximality alone does not exclude it; LSS-ROT never lowers a value either, so a proof must use how the state
was reached (LSS's priority order hands out single goods first, so dangerous sources tend to hold one good and can
absorb; in the two LSS-ROT states without PARK that were inspected they did) or a cardinal potential (welfare, Nash
welfare).

## 5. Short cycles of length 2 (agents sharing two goods)

Every k = 4 core contains 2-cycles. With them the *static* LSS completion fails (`attempts/k4-girth-sink-2cycles.md`):
on the n = 2 core with two equal agents (8, 5, 4, 2) the only EFX₀ allocation, {a, d} | {b, c}, has an envied agent
holding two goods, which no run of Algorithm 2 followed by one sink (with or without the G5 repair) produces. On GM4-E
some Pareto-maximal partial EFX₀ orientation has no completion at all (P1, `k4/sdc.md` §1), so a value-monotone method
must steer clear of such states; it does not have to lower anyone's value.

**Dynamic parking** (`lss.park_dynamic`): give the leftover goods one at a time, each to an agent that is non-envied
*at that moment*, keeping EFX₀ (raw check after each step); search over the order and the receivers. Lemma SLACK (which
needs no linearity) makes these steps natural: a non-envied one-good holder can absorb any one good, even if that makes
it envied by agents valuing both goods. On the twin core, Algorithm 2 leaves {a} | {b} with c, d unallocated; B absorbs
c ({b, c} = 9, envied by A but only with slack 5 ≤ 8), after which A is non-envied and absorbs d. Nobody's value ever
drops, so LSS + dynamic parking is value-monotone from the empty allocation.

**G1 repair** (`lss.Run.alg2_safe`). Algorithm 2's line 4 gives the envied agent i the most valuable subset T ⊆ U_i with
v_i(T) > v_i(X_i) that keeps EFX₀ (raw check), and skips i when there is none. Without it, dynamic parking fails on 43 of
about 161,800 sampled n = 4 core profiles, each time because every labeling breaks at line 4
(`attempts/k4-girth-dyn-plain.md`); with it all 43 complete.

**Conjecture DYN** (CONJECTURE). For every instance with at most four relevant goods per agent, for some vertex 0 and
labeling, LSS's Algorithm 2 with the G1 repair ends in a state that dynamic parking completes. DYN implies TARGET₄.
Evidence (`k4/girth/dyn_2cycles.py`, `k4/girth/dyn_more.py`; logs `results/k4_girth_dyn_*.log`; per instance every
vertex 0 with the default and two random labelings, stopping at the first success in `dyn_more.py`):
- the screen set: all 160 instances with 2-cycles complete (1,573 of 1,704 runs). All 24 labelings of GM4-E (P1's
  counterexample) complete even without the repair, and at least 21 of 24 for every GM4 instance;
- the suite: 152/152 instances with 2-cycles (1,547 of 1,665 runs);
- random strict profiles of the k = 4 cores: n = 2 (250 instances), n = 3 (510), n = 4 (2,164,809; random cores of
  `results/k4_certs_4_*`), n = 5 (1,239,515): all complete; 1,905,183 random degree-≤ 4 instances with 2-cycles
  (n ≤ 9): all complete (`results/k4_girth_dyn_{cores4,cores5,random}.log`);
- 48,000 profiles next to the screen instances (one or two agents' types re-drawn; `k4/girth/dyn_neighbours.py`,
  `results/k4_girth_dyn_neighbours.log`) and the d_stress families (`results/k4_girth_dyn_families.log`): all complete.

**k-robustness** (`k4/girth/dyn_ksens.py`, `results/k4_girth_dyn_ksens.log`; every labeling). DYN survives every
counterexample to the k = 4 conjectures OC / OC₁ / RD that the coordinator listed: PW5 (k = 5, n = 5, m = 9; 120 of 120
labelings complete), RD5 (k = 5; 18 of 24), the k = 5 instance with n = 4, m = 8 of `proof/kgen-n3` (22 of 24), B< and
B> (k = 4 cores, n = 6; 528 of 528 each), and the 39 TTC core counterexamples of `results/k4_sdc/ttc_core_cex_39.json`
(120 of 120 each). So DYN is not tied to k = 4.

**Envy-cycle rotation and the stuck states.**
- *Lemma EC* (PROVED; the rotation of L3). In a partial EFX₀ allocation, giving every agent of an envy cycle the bundle
  of the agent it envies keeps EFX₀ and (3): the bundles are the same sets, and every value weakly rises.
- *Stuck states* (PROVED, from Lemmas SLACK and EC). Call a state of dynamic parking with envy-cycle rotation (DFS
  state with leftovers, no good placeable on a currently non-envied agent, and no envy cycle to rotate) *stuck*. Then
  the envy graph is acyclic, so non-envied agents exist, and every one of them holds at least two goods (one holding
  ≤ 1 could absorb any leftover by Lemma SLACK, since (3) persists). In data (`k4/girth/dyn_fail_stats.py`,
  `results/k4_girth_dyn_fail_stats.log`), 180 of the 328 terminal states of failing plain searches had *no*
  non-envied agent at all (an envy cycle), and all 328 had every non-envied agent holding ≥ 2 goods.
- *Parking with envy-cycle rotation* (`lss.park_dynamic_ec`) completes all 130 runs on which plain dynamic parking
  failed in that sample. With it, **every labeling** completes on every screen, suite and k = 5 / OC instance (376
  instances, 12,424 runs, `results/k4_girth_dynec_sets.log`). On random strict core profiles every labeling completes
  on all but about 1 run in 2·10⁴ (`results/k4_girth_dynec_{cores4,cores5,random}.log`; counts in the status block), so
  "every labeling" is false, but the existence form is untouched.
- *EFX₀-checked F5/F6 rotations* during Algorithm 2 (`lss.find_rotation_safe`, `lss.pipeline`) repair most of those
  runs: they let a non-envied agent trade up along an envy path when the end of the path gains. The rest all contain
  a line-4 step giving an envied agent several goods; dropping line 4 repairs them but breaks others (15 of 30,184
  runs), and the least-valuable-subset line 4 leaves 2 of 30,184. No fixed variant is correct for every labeling.

**Which labelings fail** (`results/k4_girth_dyn_fail_stats.log`; 1,500 random n = 3, 4 core profiles, all 29,338
labelings, 130 failures without envy-cycle rotation):
- *never* when (4) fails for some agent (16,031 runs, 0 failures): failures need a state where every agent already
  prefers its bundle to all its leftovers;
- mostly when vertex 0 has no private good (121 of 130; 0.77% of such runs), rarely with one (0.09%), never with two;
- only with ≥ 2 leftover goods;
- **always with vertex 0 on a 2-cycle** (a pair of agents sharing two goods, vertex 0 one of them): 0 failures in the
  2,768 runs where vertex 0 is on none, against about 12 expected at the overall rate (0.44%). This is G6's situation
  (§1.4) and the 2-cycle analogue of Theorem T1's hypothesis. 3-cycles show no such effect (0.46% with, 0.30% without).
  In these small cores most agents are on both kinds (26,570 and 26,292 of 29,338 runs), so the signal is a
  restriction, not yet a rule.
- *The rule is false* (`k4/girth/dyn_zero2.py`, `results/k4_girth_dyn_zero2_*.log`): with vertex 0 on no 2-cycle, every
  order fails on 482 of 1,422,688 runs (n = 4 cores), 585 of 1,350,618 (n = 5) and 55 of 1,104,548 (random instances).
  That is about 3–4·10⁻⁴ per run, an order of magnitude below the overall 0.44%. The full pipeline (EFX₀-checked
  rotations + parking with envy-cycle rotation) completes 1,537 of those 1,567 runs; 30 remain, the smallest
  n = 4, m = 7: {0: 5, 2: 8, 5: 4, 6: 6}, {1: 3, 4: 4, 6: 2}, {2: 2, 3: 3, 4: 4}, {3: 4, 5: 3, 6: 2} with labels
  (3, 1, 0, 2) (vertex 0 = agent 2, on no 2-cycle). Other labelings complete it.

No fixed rule found (480 instances: the screen and suite instances with 2-cycles and three random profiles of every
n = 2, 3 core): vertex 0 = an agent of least degree / greatest degree / agent 0, default labels, complete 463 / 462 /
468 with the parking search and 457 / 455 / 461 with greedy parking (goods by decreasing number of valuers, first
feasible receiver in label order); some vertex 0 with default labels and greedy parking completes 478 (scratch run,
not logged).

What is not settled: whether a fixed labeling rule works (per run, 2–9% fail), and what makes a state parkable (a
proof would need an invariant of LSS's states, as in Conjecture LR-dyn). The parking search is exponential in the number of
leftover goods; it is a test of existence, not an algorithm.

## 6. Exhaustive certification of DYN∃ for n ≤ 4 (CERTIFIED)

The coordinator's decisive test of Conjecture DYN in its existence form: on every k = 4 core with at most four agents
and every strict profile, does SOME labeling complete? (All earlier DYN evidence was random.)

**Statement certified (K4.GIRTH.DYN4).** Let H be a connected k = 4 core hypergraph with n ≤ 4 agents (the 5 + 51 +
1,002 hypergraphs of `results/k4_certs_{2,3,4}_*.json.gz`, i.e. those of K4.R3 and K4.R4), and give every agent a
strict core type (K4.OT: strictly balanced, all disjoint subset sums of its relevant goods distinct; p + q < s + t when
it has two private goods; the domains of `k4/check4.py`, 288 types for a 4-good agent and 6 for a 3-good agent, up to
288⁴ ≈ 6.9·10⁹ profiles per hypergraph). Then for some labeling (vertex 0, an order of its neighbours, an order of the
rest; LSS's priority) the following pipeline ends with a complete EFX₀ allocation:
1. LSS's Algorithm 2 with FixProp3 and the G1 repair (§5: the envied agent takes the most valuable subset of its
   unallocated goods that beats its bundle and keeps EFX₀; skipped if there is none);
2. if the state is EFX₀: dynamic parking with envy-cycle rotation, a depth-first search: put one leftover good on a
   currently non-envied agent if EFX₀ (raw check) survives; when every agent is envied, rotate the bundles along an
   envy cycle (Lemma EC; at most 50 cycles per node); at most 200,000 search nodes (running out counts as failure).

By K4.CORE and K4.TIE this is a constructive route to EFX₀ for every instance with ≤ 4 relevant goods per agent whose
core components have ≤ 4 agents. EFX₀ existence there was already CERTIFIED by direct search (K4.R3, K4.R4); what is
new is that LSS's algorithm, repaired as in §5, finds it for some labeling, everywhere. Nothing is claimed for n ≥ 5
beyond the sample below.

**Method** (`k4/girth/dyncert.py`). Every decision of the pipeline is a comparison v_i(S) vs v_i(T) for one agent i;
after cancelling common goods it compares two disjoint subsets of R_i (or is decided by positivity when one side is
empty), so in a strict type its answer is a function of the type. A run on a representative profile records every
comparison it makes; all profiles that answer them alike form a product of per-agent type sets (a *box*) on which the
run is identical, so its outcome holds on the whole box. Covering: a stack of (box, next labeling); run the next
labeling on the box's representative; the recorded class is certified if the run succeeds, else it is pushed with the
following labeling; the rest of the box is split into disjoint boxes that keep the same labeling. By induction every
profile of a box waiting at labeling li fails labelings 0, …, li − 1, so a box that runs out of labelings would consist of
counterexamples (none occurred; any would be re-checked with lss.py). A hypergraph is CERTIFIED when the certified
classes add up to the whole profile count. Labelings: all of them (≤ 24 at n = 4), the n *default* ones (blocks in
increasing agent order, one per vertex 0) first.

**Checks.**
- `dyncert.Run` is written separately from `lss.py`; `dyncert.FastRun` (bitmask bundles, used by the covering) makes
  the same comparisons in the same order: `python3 k4/girth/dyncert.py --selftest` (identical outcome and class on 5,868
  runs). `k4/girth/dyncert_xcheck.py` (`results/k4_girth_dyncert_xcheck.log`): outcomes agree with `lss.py` run by run, and
  profiles sampled inside recorded classes give the recorded outcome with `lss.py`.
- *Second, independent covering* (`k4/girth/dyncert_sym.py`): it runs `lss.py`'s own pipeline, unchanged
  (`lss.Run.alg2_safe`, `lss.is_efx0`, `lss.park_dynamic_ec`), on instances whose values are symbolic linear forms that
  answer every comparison from the representative and record it (anything other than a {−1, 0, 1}-comparison raises);
  classes are computed from the type values directly, with separately written bookkeeping. `--selftest`: profiles
  sampled in its classes give the same outcome with numbers (2,400 samples of 600 runs).

**Results** (`python3 k4/girth/dyncert_summary.py results/k4_girth_dyncert_*.log`; 4 CPUs):

| cores | hypergraphs | strict profiles | runs | result | log |
|---|---|---|---|---|---|
| n = 2 | 5 | 189,216 | 3,855 | all CERTIFIED; independent covering: all CERTIFIED (7,156 runs) | `results/k4_girth_dyncert_2.log`, `results/k4_girth_dyncert_sym_2.log` |
| n = 3 | 51 | 299,837,376 | 1,130,416 | all CERTIFIED; independent covering: all CERTIFIED (2,449,990 runs) | `results/k4_girth_dyncert_3.log`, `results/k4_girth_dyncert_sym_3.log` |
| n = 4, one 4-good agent | 135 | 7,247,232 | 268,107 | all CERTIFIED; independent covering: all CERTIFIED (366,486 runs) | `results/k4_girth_dyncert_4_n4_1.log`, `results/k4_girth_dyncert_sym_4_n4_1.log` |
| n = 4, two | 309 | 724,847,616 | 5,361,575 | all CERTIFIED | `results/k4_girth_dyncert_4_n4_2.log` |
| n = 4, three | 339 | 34,971,844,608 | 57,987,455 | all CERTIFIED | `results/k4_girth_dyncert_4_n4_3.log` |
| n = 4, four (pure) | 219 | (queued) | | | `results/k4_girth_dyncert_4_pure.log` |
| n = 5, one 4-good agent | 1,735 | 574,615,296 | 13,418,885 | all CERTIFIED | `results/k4_girth_dyncert_5_n4_1.log` |

No profile on which every labeling fails was found. The n = 5 row covers every core with one 4-good agent (not a
sample); the other n = 5 cores (two to four 4-good agents, 29,849 hypergraphs) would need about 10⁷ CPU-seconds in
Python, so only samples are run (queued).

**Which labelings are needed.**
- *Vertex 0 is the only freedom needed so far.* With the n default labelings alone (`--family=default`) every n = 3
  core is certified (`results/k4_girth_dyncert_3_default.log`), and at n = 5 with one 4-good agent the default
  labelings suffice on all 1,735 cores (on 1,733 of them labeling #0, vertex 0 = agent 0, alone).
- *No labeling rule that reads only the hypergraph* (REFUTED, `attempts/k4-girth-uniform-labeling.md`): 6 of the 51
  n = 3 cores, all with three 4-good agents, have no labeling that works on every profile
  (`results/k4_girth_dyncert_3_uniform.log`); on the smallest (n = 3, m = 6, every pair sharing two goods) two
  profiles split the six labelings 3 + 3. The labeling must depend on the values.
- *Exchange moves do not remove the dependence* (`k4/girth/dynx.py`, `results/k4_girth_dynx_3{,_base}.log`): letting
  any agent trade its bundle for a better subset of its bundle and the leftovers (EFX₀ kept, every value weakly up) in
  the parking search raises the number of n = 3 labelings that work on every profile only from 246 to 253 of 300, on
  the same 37 of 51 cores.

**Conjecture DOM** (CONJECTURE; `k4/girth/dom_test.py`). *For every labeling, the state X that LSS's Algorithm 2 with
the G1 repair leaves has a dominating completion: a complete EFX₀ allocation Z with v_i(Z_i) ≥ v_i(X_i) for every
agent.* Where every parking move set above fails, such completions exist and come from *generalized rotations*: on
the n = 3, m = 7 profile {0: 2, 3: 5, 4: 4, 6: 8}, {1: 6, 3: 3, 5: 4, 6: 8}, {2: 1, 4: 4, 5: 6, 6: 8} with labels
(0, 1, 2), Algorithm 2 leaves {3} | {6} | {2, 4, 5} with goods 0, 1 unallocated, parking is stuck, and
{6} | {1, 3} | {0, 2, 4, 5} dominates it: agent 0 takes agent 1's good, agent 1 takes agent 0's good plus a leftover,
which is no envy-cycle rotation (agent 1 does not envy {3}). Evidence: random strict profiles, every labeling, brute
force over all allocations: n = 3, 766,395 profiles (4,508,174 runs); n = 4 with m ≤ 10, 101,316 profiles
(2,054,352 runs); no state without a dominating completion (`results/k4_girth_dom_{3,4}.log`; for comparison, parking with
envy-cycle rotation fails on about 3·10⁻⁵ of all runs, §5, which would be about 200 of these). Exhaustive
at n = 3 (`python3 k4/girth/dom_test.py exhaustive 3`, the covering of `dyncert.py` with each labeling alone and the
brute force run through recorded comparisons): **DOM holds for all 300 labelings on every strict profile of all 51
n = 3 cores** (9,986,740 runs, `results/k4_girth_dom_exhaustive_3.log`; one implementation, built on the self-tested
`dyncert.FastRun`; the random runs above use `lss.py` with numbers; a second exhaustive encoding is still open). DOM does not follow from
LSS's Properties (3) and (4) alone: the PL state of `attempts/k4-girth-linear-pl.md` satisfies both and has no
completion. If DOM holds, TARGET₄ reduces to a completion lemma for the states of Algorithm 2, with no labeling search.

## 7. Short Berge cycles at the OC₁^max failures (EVIDENCE; coordinator's question, burst 5)

Question: which short-cycle patterns does every OC₁^max failure contain (`k4/sdc.md` §31, K4.SDC.OC1MAX)? Data: all
112,880 failing (profile, picks) pairs on the 11 failing n = 4 cores (`results/k4_oc1max/two_move_starts_n4.json.gz`,
complete by K4.SDC.OC1MAX.N3), and the 24 n = 5 failures that `main` stores (`results/k4_oc1max/oc1prime_cex_n5_partial.jsonl`:
the OC₁′^max failures among the first 137 OC₁^max failures on 5_pure, 5_pure#164 among them; failing OC₁′ implies
failing OC₁, since OC₁′ only adds moves; a biased subset). Contrast: perfect SD starts where OC₁^max holds, from random
strict profiles and every order (23,422 on the 11 cores, 10,403 on other n = 4 cores; the failing set removed by
order type), and 394 random perfect starts of 5_pure cores, whose OC₁^max status is unknown but failures are rare
(`k4/girth/oc1_cycles.py`, `results/k4_girth_oc1_cycles.log`).

Roles at the picks Y (`k4/oc1_hall.md`, `k4/oc1max_multi.md`): J the junk; F frozen (someone wants its pick); D ⊆ F
dangerous (values a junk good); D_T ⊆ D truly dangerous (J threatens it at its pick value); U unfrozen (the
receivers). A *pick swap* is a Berge 2-cycle whose two agents both value both of their picks.

| pattern | n = 4 failures | n = 5 failures | OC₁ holds, same 11 cores | OC₁ holds, other n = 4 | random n = 5 |
|---|---|---|---|---|---|
| \|U\| = 1 | 100% | 100% | 9.7% | 13.6% | 10.4% |
| 2-cycle between two dangerous agents | 100% | 23 of 24 | 26.2% | 21.9% | 53.8% |
| two dangerous agents sharing two junk goods | 100% | 0 of 24 | 4.4% | 1.9% | 6.9% |
| \|D_T\| = 2 | 100% | 0 of 24 | 8.1% | 4.7% | 11.7% |
| \|D_T\| = 0 | 0% | 24 of 24 | 53.6% | 68.4% | 57.6% |
| \|U\| = 1 and a D_T pair sharing two junk goods | 100% | 0 of 24 | 0.9% | 0.3% | 1.0% |
| pick swap between a dangerous agent and the receiver | 72.6% | 24 of 24 | 42.8% | 39.1% | 49.0% |
| **P\*:** \|U\| = 1 and (a D_T pair sharing two junk goods, or a dangerous–receiver pick swap) | **100%** | **24 of 24** | **5.2%** | **4.8%** | **5.3%** |

Findings:
- **n = 4: one mechanism.** Every failing start has exactly one receiver and exactly two truly dangerous agents, and
  these two form a Berge 2-cycle on two junk goods (their shared goods: two junk goods, plus possibly picks). With
  |U| = 1 this pattern occurs at 0.9% (same cores) and 0.3% (other cores) of the starts where OC₁ holds.
- **n = 5: another mechanism.** None of the 24 failures has a truly dangerous agent; each has a pick swap between a
  dangerous agent and the receiver (the "two disjoint conflicts" of `k4/sdc.md` §31 on 5_pure#164: 16 of 24 have two
  vertex-disjoint pick swaps through dangerous agents).
- **The hypothesis as stated is false at n = 5.** "Every two-move start has a Berge 2-cycle through two dangerous
  agents" holds on all n = 4 failures but not on 5_pure#72: sets [[0,2,6,7],[1,4,8,10],[3,5,9,10],[6,7,8,9],[7,8,9,10]],
  values [[4,3,8,6],[3,4,10,8],[4,3,8,6],[10,2,3,6],[4,8,7,2]], picks (6,8,9,7,10); roles D, D, D, F, U. Its 2-cycles
  are {0, 3} on {6, 7}, {1, 4} on {8, 10}, {2, 4} on {9, 10} and {3, 4} on {7, 8, 9}: pick swaps of dangerous agents
  with the frozen agent 3 and with the receiver 4, and no two dangerous agents share two goods.
- **Usable hypothesis: P\*.** On all known failures (n = 4 complete, n = 5 partial), OC₁ fails only if exactly one agent
  is unfrozen and either two truly dangerous agents share two junk goods or a dangerous agent and the receiver share
  both picks. P\* excludes about 95% of the perfect starts where OC₁ holds. With TTC's R2 (two receivers ⟹ OC₁^max;
  K4.SDC.R2.N4, certified at n = 4), the open cases of an OC₁ proof would be the |U| = 1 starts, and among them only
  those with a junk 2-cycle of two truly dangerous agents or a dangerous–receiver pick swap. The n = 5 part rests on
  24 stored failures; the other OC₁^max failures at n = 5 are not on `main` and were not checked.

## Reproduce

All plain Python (python-sat not needed); run from the repository root. Times on 4 CPUs.
```
python3 k4/girth/lss.py 1                          # sanity: faithful LSS on random girth-4 instances (~15 s)
python3 k4/girth/run_faithful.py                   # §2 table (~5 min)     -> results/k4_girth_faithful.log
python3 attempts/k4_girth_attempts.py              # every refutation and smallest failure, with independent re-checks (<1 s)
python3 k4/girth/ht_families.py 6 100              # Proposition HT checks  -> results/k4_girth_ht_families.log
python3 k4/girth/core_stats.py                     # T1 coverage of small cores -> results/k4_girth_core_stats.log
python3 k4/girth/linear_pm.py SEED SECS MAXDEG [graphs]   # Pareto-maxima, PARK, potentials -> results/k4_girth_linear_pm_*.log
python3 k4/girth/lsflex_linear.py SEED SECS MAXDEG        # LSS + flexible sink   -> results/k4_girth_lsflex_*.log
python3 k4/girth/lssrot_linear.py SEED SECS MAXDEG [NMAX] # Conjecture LR, random -> results/k4_girth_lssrot_d4.log
python3 k4/girth/lssrot_trap.py SEED SECS                 # Conjecture LR, around the trap -> results/k4_girth_lssrot_trap.log
python3 k4/girth/lr_climb.py SEED SECS                    # Conjecture LR, hill climbing -> results/k4_girth_lr_climb_*.log
python3 k4/girth/lssrot_cores.py 20                       # Conjecture LR, all linear cores n <= 6 -> results/k4_girth_lssrot_cores.log
python3 k4/girth/lrdyn_linear.py random|trap SEED SECS    # Conjecture LR-dyn -> results/k4_girth_lrdyn_{random,trap}.log
python3 k4/girth/dyn_families.py 5 1                      # DYN / LR on the d_stress families -> results/k4_girth_dyn_families.log
python3 k4/girth/dyn_2cycles.py 10                        # Conjecture DYN, screen/suite/cores n <= 3 -> results/k4_girth_dyn_2cycles.log
python3 k4/girth/dyn_more.py cores4|cores5|random SEED SECS   # Conjecture DYN -> results/k4_girth_dyn_{cores4,cores5,random}.log
python3 k4/girth/dyn_neighbours.py 300 7                  # DYN near the screen instances -> results/k4_girth_dyn_neighbours.log
PLAIN=1 python3 k4/girth/dyn_more.py cores4 1 1200        # the unrepaired version -> results/k4_girth_dyn_cores4_plain.log
python3 k4/girth/dyn_ksens.py                             # DYN on the k = 5 and OC/OC1 counterexamples -> results/k4_girth_dyn_ksens.log
python3 k4/girth/dyn_fail_stats.py 1500 1                 # failing labelings and stuck states -> results/k4_girth_dyn_fail_stats.log
python3 k4/girth/dynec_all.py sets | cores N SEED SECS | random SEED SECS   # every labeling, envy-cycle parking -> results/k4_girth_dynec_*.log
python3 k4/girth/dyn_zero2.py cores N SEED SECS | random SEED SECS          # vertex 0 on no 2-cycle -> results/k4_girth_dyn_zero2_*.log
python3 k4/girth/smallest.py SEED SECS                    # smallest failing configuration per girth use
python3 k4/girth/dyncert.py N [PART] [--family=all|default|uniform] [--every=E] [--timecap=S]   # §6 -> results/k4_girth_dyncert_*.log
python3 k4/girth/dyncert.py --selftest; python3 k4/girth/dyncert_sym.py --selftest    # §6 checks -> results/k4_girth_dyncert_selftest.log
python3 k4/girth/dyncert_xcheck.py PROFILES SEED                # §6 FastRun vs lss.py -> results/k4_girth_dyncert_xcheck.log
python3 k4/girth/dyncert_sym.py N [PART] [--every=E]            # §6 independent covering -> results/k4_girth_dyncert_sym_*.log
python3 k4/girth/dyncert_summary.py results/k4_girth_dyncert_*.log   # §6 table
python3 k4/girth/dynx.py 3 [--base]                             # §6 exchange moves -> results/k4_girth_dynx_3{,_base}.log
python3 k4/girth/dom_test.py N SEED SECS [MAXM] | exhaustive N  # §6 Conjecture DOM -> results/k4_girth_dom_*.log
python3 attempts/k4_girth_uniform.py                            # §6 no labeling per hypergraph (replay with lss.py)
python3 k4/girth/oc1_cycles.py 300 1                            # §7 cycle patterns at OC1^max failures -> results/k4_girth_oc1_cycles.log
```
Files: `lss.py` (the algorithm, instrumentation, sinks, parking, rotations, G1 repair), `brute.py` (brute force over
partial orientations), `gen.py` (generators), `sources.py` (repository instance sets).
