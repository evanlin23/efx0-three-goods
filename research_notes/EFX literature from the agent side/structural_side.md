# Structural restrictions for EFX / EFX₀: valuation structure and agent–good incidence (state to 26 Nov 2026)

Conventions used throughout. The *incidence hypergraph* H(I) of an instance: agents are vertices; a good valued positively by the agent set S is a hyperedge S (a good of one valuer is a singleton edge, so two private goods of one agent are a repeated edge). **k** = maximum vertex degree (our parameter: relevant goods per agent), **p** = maximum edge size (valuers per good), **q** = maximum number of goods shared by two agents (CFKS §6 / Kaviani et al. Def. 2.2). EFX₀ = removing *any* good, including goods worth 0 to the envier. "Our project" = this repository: EFX₀ is proved for additive valuations when k ≤ 3 (Draft and Exchange) and for monotone valuations when k ≤ 2 (`mrd-efx`, `MRDMono`), per `proofs/citations.md` and `proofs/pq_bounded.md`.

Read levels: **[full]**; **[section: …]** (named parts read this session); **[abstract]**; **[repo-full]** = read in full in an earlier session of this repository (notes in `proofs/pq_bounded.md`, `proofs/citations.md`, `proofs/multigraph_digest.md`), not re-read now. Texts read this session were fetched from arxiv.org (PDF, `pdftotext`) on 2026-11-26. **[preprint]** = arXiv only as far as checked; venue claims say where they come from. Anything not read at least in abstract form is marked [unverified].

## 1. Graphs and multigraphs (each good valued by ≤ 2 agents): exact statements and where the structure enters the proof

### Takeaway
For p ≤ 2 the picture is nearly complete: exact EFX₀ holds on all multigraphs for cancelable (hence additive) valuations, and for general monotone valuations on simple graphs, triangle-free multigraphs, multi-cycles, and multigraphs whose agents have few neighbours. Every proof has the same skeleton: a partial EFX₀ *orientation* with invariants, then dumping the leftover goods on an unenvied agent who values them 0. The graph hypothesis (simple, bipartite, triangle-free, girth) is used almost only in that final dumping step. The one theorem whose hypothesis is a *degree* bound (Sgouritsa–Sotiriou Thm 2, at most ⌈n/4⌉ − 1 neighbours) is the natural meeting point with our degree-≤ k programme.

### Cited Findings
**Christodoulou–Fiat–Koutsoupias–Sgouritsa (CFKS), "EFX Allocations on Graphs".** Peer-reviewed: EC 2023 pp. 473–488 and *Math. Oper. Res.* online 15 Jun 2026, DOI 10.1287/moor.2025.0915, per Crossref as recorded in `proofs/citations.md`. [section this session: §4.1–4.2, Claim 10, Lemmas 11 and 13, §6; repo-full]
- Model: "every item is relevant to at most 2 agents and for every pair of agents there exists at most one item relevant to both" (p = 2, q = 1). Valuations are monotone, and EFX is the all-goods form vᵢ(Xᵢ) ≥ vᵢ(Xⱼ \ {x}) ∀x ∈ Xⱼ (EFX₀) — [CFKS PDF](https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/fair-allocations-on-graphs.pdf).
- Theorem 3: "There is a complete EFX allocation for any graph that can be found in polynomial time" — [CFKS PDF](https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/fair-allocations-on-graphs.pdf).
- Zero goods: "without loss of generality … the graph is complete: … add extra edges of (marginal) value zero to both endpoints" (§4.2) — [CFKS PDF](https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/fair-allocations-on-graphs.pdf).
- The four key properties, with Uᵢ(X) = i's unallocated incident edges and the safe set Sᵢ(X) = {non-envied j : vᵢ(Xᵢ) ≥ vᵢ(Xⱼ ∪ Uᵢ(X))}: (1) X is an EFX orientation; (2) vᵢ(Xᵢ) ≥ vᵢ(e) for every e ∈ Uᵢ(X); (3) every envied i has vᵢ(Xᵢ) ≥ vᵢ(Uᵢ(X)); (4) any two envied i, j joined by an unallocated edge have Sᵢ(X) ∩ Sⱼ(X) ≠ ∅ — [CFKS PDF](https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/fair-allocations-on-graphs.pdf).
- Where simplicity enters:
  - Algorithm 1 gives every vertex at most one edge (Lemma 4).
  - Claim 10: a non-envied k holding the single edge (k, ℓ) lies in the safe set of every envied i ≠ ℓ.
  - Lemma 13 parks each edge with a non-envied endpoint at that endpoint, because "no non-envied vertex v has two of its adjacent edges assigned to any single other vertex". It parks each edge between two envied vertices at a vertex of Sᵢ ∩ Sⱼ.
  - Source: [CFKS PDF](https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/fair-allocations-on-graphs.pdf).
- Orientations: no EFX orientation exists for one 4-agent instance, which per Lianeas et al. is "a counterexample in a K4 graph" — [CFKS PDF](https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/fair-allocations-on-graphs.pdf); [2608.03171](https://arxiv.org/abs/2608.03171). Deciding orientability is NP-complete (Thm 2). Prop. 14: three additive agents with parallel edges may have no EFX orientation; Prop. 15: with three agents and multiplicity ≤ 2 an EFX orientation exists — [CFKS PDF](https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/fair-allocations-on-graphs.pdf).
- §6 open problem: generalise to "every item is relevant to at most … p agents" and/or "an upper bound q on the number of items relevant to both" — [CFKS PDF](https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/fair-allocations-on-graphs.pdf).

**Afshinmehr–Ashuri–Mahmoudkhan–Mehlhorn–Shahrezaei, "EFX Allocations Exist on Multi-Graphs", arXiv 2606.18665v1.** [repo-full; lemma-by-lemma digest in `proofs/multigraph_digest.md`]
- Theorem 3.4: on multigraph instances (vᵢ(S) = vᵢ(S ∩ Eᵢ)) a complete EFX₀ allocation exists for cancelable valuations and is computable in polynomial time — [arXiv 2606.18665](https://arxiv.org/abs/2606.18665).
- Venue: the reference list of Lianeas et al. (read this session) lists it as "In Proceedings of the 27th ACM Conference on Economics and Computation (Rome, Italy)", i.e. EC 2026 — [2608.03171 ref. [2]](https://arxiv.org/abs/2608.03171). This is a secondary source, but it supplies the source that `proofs/citations.md` said was missing.
- Where p ≤ 2 is used (repo digest §4; inference recorded there from the full read):
  - (F1) a held good is seen by at most one other agent;
  - (F2) goods split into pair classes with a fixed two-way cut;
  - (F3) pre-dump allocations are orientations, so envy is local to one pair.
  - Concretely: Lemma 2.5 ("one of b_{i,j}, a_{j,i} is unallocated") and Lemma 2.8/Obs. 2.12 (at most one resenter). It also enters the dumping accounting (Def. 5.3, Lemma 5.4) and the case analysis A–H.
  - Source: [arXiv 2606.18665](https://arxiv.org/abs/2606.18665), via `proofs/multigraph_digest.md`.
- An independent proof is reported: "Christodoulou et al. [2026] independently showed the existence of (exact) EFX allocations on multigraphs" — [2406.12413v3 §1.2.1](https://arxiv.org/abs/2406.12413). That paper is listed as Christodoulou, Mastrakoulis, Sgouritsa, Sotiriou, "EFX allocations on multigraphs", EC 2026 — [2608.03171 ref. [22]](https://arxiv.org/abs/2608.03171). [unverified: text not found on arXiv; a 2026-11-26 web search found no copy]

**Sgouritsa–Sotiriou, "On the existence of EFX allocations in multigraphs", arXiv 2502.09777v1.** AAMAS 2025 extended abstract, pp. 2735–2737, which states only the neighbour and girth results. [repo-full]
- Monotone valuations; EFX₀. A complete EFX allocation exists in three cases:
  - Thm 1: the multigraph is bipartite;
  - Thm 2: every agent has ≤ ⌈n/4⌉ − 1 neighbours (⌊n/4⌋ with at most two parallel edges);
  - Thm 3: the shortest cycle of non-parallel edges has length ≥ 6.
  - Source: [arXiv 2502.09777](https://arxiv.org/abs/2502.09777), via `proofs/pq_bounded.md` §2.5.
- Technique:
  1. A maximum-weight matching of agents to first/second-choice goods leaves ≤ ⌊n/2⌋ envied agents (Lemma 3.7).
  2. "Reducing envy" chains.
  3. Parking each unallocated bundle at a non-envied *non-neighbour*: the neighbour bound guarantees enough parking spots (Claim 3.13 counts the non-envied non-neighbours).
  - Source: [arXiv 2502.09777](https://arxiv.org/abs/2502.09777), via `proofs/pq_bounded.md`.
- Remark 1: under ordinary EFX (positively valued goods only), pairwise cut-and-choose already gives EFX on multigraphs; the difficulty is EFX₀ — [arXiv 2502.09777](https://arxiv.org/abs/2502.09777).

**Afshinmehr–Danaei–Kazemi–Mehlhorn–Rathi, "EFX Allocations and Orientations on Bipartite Multi-graphs: A Complete Picture", arXiv 2410.17002v3.** Peer-reviewed: AAMAS 2025, pp. 32–40, per [2608.03171 ref. [3]](https://arxiv.org/abs/2608.03171); a journal version is in JAAMAS 40:32 (2026) per `proofs/citations.md` [journal not read]. [section: abstract, §1–1.1, §2 Defs 2.3–2.15 and Lemma 2.10, §4.1–4.2, §4.7, §5, §6]
- Model (Def. 2.3): vᵢ(S) = vᵢ(S ∩ E(i)), with "an item g ∈ [m] has a positive marginal value for agent i if and only if g is incident to i". Strong envy (Def. 2.6) is "there exists an item g ∈ Xⱼ such that vᵢ(Xᵢ) < vᵢ(Xⱼ \ g)", i.e. EFX₀ — [arXiv 2410.17002](https://arxiv.org/abs/2410.17002).
- Theorem 4.11: bipartite multigraphs, monotone valuations, EFX exists; pseudo-polynomial in general and polynomial for cancelable valuations — [arXiv 2410.17002](https://arxiv.org/abs/2410.17002).
- Theorem 5.1: multi-cycles with MMS-feasible valuations; Corollary 5.2: multi-cycles with ≥ 4 agents and monotone valuations. The odd case removes one pair's goods, or two agents, leaving an even multi-path, and then does a 6-way case split — [arXiv 2410.17002](https://arxiv.org/abs/2410.17002).
- Lemma 2.10: in an EFX orientation of a multigraph, if j envies i then Xᵢ ⊆ E(i, j); "any vertex is envied by at most one neighbor" — [arXiv 2410.17002](https://arxiv.org/abs/2410.17002).
- Six key properties of the partial orientation:
  1. EFX orientation;
  2. each pair's goods are allocated by the T-side agent's cut (C₁, C₂);
  3. each agent beats every "available bundle";
  4. non-envied agents have Aᵢ(X) = ∅;
  5. non-envied agents have vᵢ(Xᵢ) ≥ vᵢ(Uᵢ(X));
  6. the envier j of an envied i lies in i's safe set Sᵢ(X).
  - Source: [arXiv 2410.17002](https://arxiv.org/abs/2410.17002).
- Where bipartiteness enters: Algorithm 5 / Lemma 4.10 dumps Aᵢ(X) onto "the agent who envies i". The proof uses i₁, …, i_l ∈ S, j ∈ T, and "k ∈ T and … j has not received any item valuable to agent k" — two T-vertices are never adjacent — [arXiv 2410.17002](https://arxiv.org/abs/2410.17002).
- Authors' diagnosis (§5): the general case fails when "two envied vertices i and j" are adjacent "such that no edge from E(i, j) was allocated". The suggested fix is |Sᵢ(X) ∩ Sⱼ(X)| ≥ 2. Conjecture: every multigraph instance admits EFX — [arXiv 2410.17002](https://arxiv.org/abs/2410.17002).
- Orientations (Table 1, additive): on acyclic bipartite multigraphs, EFX orientations exist when q = 2 and d(G) ≤ 4, or when q > 2 and d(G) ≤ 2, and may fail otherwise. They may fail on cyclic ones. Deciding is NP-complete even on multi-trees with a constant number of agents (Thm 3.6). There is an orientation in which ≥ ⌈n/2⌉ agents are EFX and the rest ½-EFX (Thm 4.12) — [arXiv 2410.17002](https://arxiv.org/abs/2410.17002).

**Bhaskar–Pandit, "EFX Allocations on Some Multi-graph Classes", arXiv 2412.06513v1.** Peer-reviewed as "Extending EFX Allocations to Further Multi-Graph Classes", FSTTCS 2025, LIPIcs 360, 15:1–15:18, per [2608.03171 ref. [12]](https://arxiv.org/abs/2608.03171). [full main text, §1–6]
- EFX: "vᵤ(Aᵤ) ≥ vᵤ(A_w \ {x}), for all x ∈ A_w" (EFX₀); valuations integer-valued and monotone — [arXiv 2412.06513](https://arxiv.org/abs/2412.06513).
- Thm 3 (bipartite, cancelable, polynomial time). For each u ∈ L in turn, every neighbour w cuts E_{u,w}. The ordinary neighbours take their preferred piece. u picks between its favourite neighbour f_u's piece S_{u,f_u} and the union of the leftovers.
  - Lemma 4: "the only possible envy … is that a resolved agent u′ ∈ L is envied by its favourite agent f_{u′}".
  - Bipartiteness is used because a structure St_u contains no L-agent other than u, so the allocations of resolved L-agents never change and new envy stays inside St_u.
  - Source: [arXiv 2412.06513](https://arxiv.org/abs/2412.06513).
- Thm 5 (multi-trees, *monotone*; proof by leaf induction).
  - Remove a leaf ℓ with parent p. p cuts E_{ℓ,p}, and ℓ takes its preferred piece.
  - If p is a source of the envy graph, p takes the leftover. Otherwise the leftover goes to a source s with a path to p, and if p now envies s, that envy cycle is rotated.
  - Source: [arXiv 2412.06513](https://arxiv.org/abs/2412.06513).
- Thm 12 (t-chromatic multigraphs with non-parallel girth ≥ 2t − 1, cancelable). The bipartite algorithm is run in phases, colour class by colour class; goods only move rightward (Prop. 8).
  - Claims 9–10 bound the distance from a good's holder to its valuers by colour differences.
  - Girth enters in Lemma 11: "u does not value w's bundle", otherwise there is a cycle of length t + 1 < 2t − 1; and an outsider u′ cannot envy f_u, otherwise there is a cycle of length 2t − 2.
  - Source: [arXiv 2412.06513](https://arxiv.org/abs/2412.06513).

**Afshinmehr–Ashuri–Mahmoudkhan–Mehlhorn, "EFX Allocations Exist on Triangle-Free Multi-Graphs", arXiv 2512.21644v1.** AAMAS 2026 per Crossref as recorded in `proofs/citations.md`. [section: abstract, technical overview, Thm 3.1, §3.3 in full, §4]
- Theorem 3.1: EFX allocations exist when the skeleton has no 3-cycle. Computation is pseudo-polynomial for monotone and polynomial for cancelable valuations. Strong envy is "there exists a good g ∈ T such that vᵢ(S) < vᵢ(T \ g)" (EFX₀) — [arXiv 2512.21644](https://arxiv.org/abs/2512.21644).
- Phase One: fixed *unit bundles*, one EFX-feasible 2-cut per pair, the cutter chosen by a selection order. Each agent takes one incident unit bundle, the allocation is EFX, nobody prefers a free incident unit bundle, and "the longest path in the envy graph has length at most one" (the envy graph is a union of stars) — [arXiv 2512.21644](https://arxiv.org/abs/2512.21644).
- "the first two phases can be applied to any multi-graph instance; i.e., we use the triangle-free condition only in the final phase" — [arXiv 2512.21644](https://arxiv.org/abs/2512.21644).
- Phase Three (Algorithm 3; Lemma 3.14) dumps the leftover unit bundles B⁽¹⁾ᵢ onto "the agent who envies i". Triangle-freeness gives three facts:
  - two envied adjacent agents i, k have different enviers (j ≠ l);
  - the agents j_p envied by a recipient i are pairwise non-adjacent;
  - every other agent r is non-adjacent to i, or to all the j_p.
  - Source: [arXiv 2512.21644](https://arxiv.org/abs/2512.21644).
- The authors conjecture that every multigraph instance admits EFX — [arXiv 2512.21644](https://arxiv.org/abs/2512.21644).

**Valuation-restricted multigraph results.**
- Kaviani–Seddighin–Shahrezaei 2407.05139 (WINE 2024), Thm 8.1: exact EFX₀ for restricted additive valuations (vᵢ(g) ∈ {0, v_g}) on (2, ∞)-bounded instances — [arXiv 2407.05139](https://arxiv.org/abs/2407.05139) [repo-full].
- 2/3-EFX on additive multigraphs (Amanatidis–Filos-Ratsikas–Sgouritsa, EC 2024) — [2406.12413](https://arxiv.org/abs/2406.12413) [repo-section].
- 1/√2-EFX on additive multigraphs (Kaviani et al.) — [2506.09288](https://arxiv.org/abs/2506.09288) [repo-full].
- MMS and PMMS on multigraphs for additive, XOS and subadditive valuations — [Christodoulou–Mastrakoulis 2506.20317](https://arxiv.org/abs/2506.20317) [abstract]; AAAI 2026 per [2608.03171 ref. [21]](https://arxiv.org/abs/2608.03171).

### Inferences
- **Subsumption for monotone valuations.** Triangle-free (2512.21644) contains:
  - bipartite (2410.17002 Thm 4.11; 2502.09777 Thm 1);
  - multi-trees (2412.06513 Thm 5);
  - non-parallel girth ≥ 6 (2502.09777 Thm 3);
  - Bhaskar–Pandit's t-chromatic class: girth ≥ 2t − 1 ≥ 5 when t ≥ 3, and bipartite when t = 2.

  Not subsumed: Sgouritsa–Sotiriou Thm 2 (neighbour bound; triangles allowed) and multi-triangles (3-agent multi-cycles), which 2410.17002 handles only for MMS-feasible valuations via Akrami et al. For cancelable valuations, and hence additive ones, 2606.18665 subsumes everything in this section.
- **Common skeleton.** The steps are an orientation phase that is valid on all multigraphs, then a dump of the leftover onto an *unenvied agent who values it 0*. The graph hypothesis certifies that this agent's bundle is invisible to the agents who see the dumped goods. The canonical dump target, "the unique envier", exists because of 2410.17002 Lemma 2.10, an envied agent has exactly one envier, which is a p = 2 fact. With a good of three valuers its holder can be envied by two agents (`proofs/multigraph_digest.md` §4 item 3). This is the precise point a degree-≤ k hypergraph extension must replace.
- **The degree meeting point (to verify before use).** In a multigraph-type instance, max degree ≤ k implies ≤ k neighbours, provided each private good of i is modelled as an extra edge parallel to an existing edge of i, with marginal 0 for the other endpoint. That keeps neighbour counts unchanged; isolated agents are trivial. Sgouritsa–Sotiriou Thm 2 then gives **monotone EFX₀ for every instance with p ≤ 2 and k ≤ ⌈n/4⌉ − 1, i.e. n ≥ 4k + 1**. Two checks are needed:
  - that their monotone model permits incident edges of zero marginal value, as their "vᵢ monotone and normalized" suggests per `proofs/citations.md`;
  - that "neighbours" is counted in the multigraph as given.

  If both hold, the monotone p ≤ 2, degree-≤ k question is open only for n ≤ 4k agents with triangles, a finite family of graphs for each k.
- CFKS's K4 example is a simple graph with every vertex of degree 3. So already at k = 3 (with p = 2, q = 1) every EFX₀ allocation of it must give some good to an agent who values it 0. This matches our L3 (junk must be placed) and shows a "pure orientation" route cannot work at k = 3.

### Gaps
- The EC 2026 paper of Christodoulou–Mastrakoulis–Sgouritsa–Sotiriou was not found, so its technique, and whether it covers monotone valuations, is unknown.
- 2512.21644 Phases One–Two (pp. 4–13) and 2410.17002 §§3, 4.3–4.6 were not read line by line. The "orientation phase is valid on all multigraphs" claim rests on the authors' own sentence.
- No source settles EFX₀ on multigraphs *with triangles* for *general monotone* valuations. Both 2410.17002 and 2512.21644 state it as a conjecture.

## 2. EFX orientations (every good to one of its valuers) and their obstructions

### Takeaway
Orientations are the "non-wasteful" sub-question. For simple graphs it is now fully characterised which graphs are orientable for *all* valuations (bipartite, or one special non-bipartite block). For fixed valuations, deciding orientability is NP-complete even on very restricted structures. For EFX₀ this mostly confirms that parking goods at agents who value them 0 is unavoidable.

### Cited Findings
- Zeng–Mehta, "On the structure of EFX orientations on graphs", arXiv 2404.13527v2; AAMAS 2025, pp. 2309–2316, per [2608.03171 ref. [43]](https://arxiv.org/abs/2608.03171). [section: abstract, §1, Lemma 3.1, Cor. 3.2, Lemma 4.1, statements]
  - Graphs with χ(G) ≤ 2 are "strongly EFX orientable" (orientable for every monotone valuation), and graphs with χ(G) > 3 are not — [arXiv 2404.13527](https://arxiv.org/abs/2404.13527).
  - Lemma 4.1 proof: in a bipartite graph each vertex of class A picks its favourite edge and all other edges go to B; envy from B to A is EFX because each A-vertex holds one edge — [arXiv 2404.13527](https://arxiv.org/abs/2404.13527).
  - Lemma 3.1 characterises 0-1 strong orientability by a forest / independent-set condition — [arXiv 2404.13527](https://arxiv.org/abs/2404.13527).
  - Their "strongly EFX" means orientable for all valuations, not EFX₀ (`proofs/novelty.md`).
- Zeng, arXiv 2609.36498v2 (1 Oct 2026) [abstract] [preprint]:
  - a connected G is strongly EFX orientable iff (1) G is bipartite, or (2) its block decomposition has exactly one non-bipartite block B with a vertex v ∈ B of degree 2 in B such that G − v is bipartite;
  - "This proof was discovered by AI, with human intervention".
  - Source: [arXiv 2609.36498](https://arxiv.org/abs/2609.36498).
- Complexity of EFX orientations [all abstracts]:
  - Deligkas–Eiben–Goldsmith–Korchemna (IJCAI-25): NP-hard even with vertex cover 8 or with a 10-vertex multigraph; EF1 orientations always exist (monotone, pseudo-polynomial) — [arXiv 2409.13616](https://arxiv.org/abs/2409.13616).
  - Blažej–Gupta–Ramanujan–Strulo (SAGT 2025): NP-complete even for symmetric binary valuations on graphs two edge-removals from bipartite; linear time on bounded treewidth — [arXiv 2506.15379](https://arxiv.org/abs/2506.15379).
  - Kanellopoulos et al.: parameterised EF/EFX orientations; per 2608.03171, hardness down to vertex cover 4 or 4-vertex multigraphs — [arXiv 2512.25033](https://arxiv.org/abs/2512.25033); [2608.03171](https://arxiv.org/abs/2608.03171).
  - Hsu (ECAI 2025): bi-valued symmetric multigraphs: NP-complete even if bipartite; "non-trivial odd multitrees" are the obstruction — [arXiv 2410.12039](https://arxiv.org/abs/2410.12039).
- Zhou/Li et al., "A Complete Landscape of EFX Allocations on Graphs" (IJCAI 2024) [abstract] — [arXiv 2409.03594](https://arxiv.org/abs/2409.03594):
  - for goods, an orientation satisfying "another weaker notion of EFX" always exists in polynomial time;
  - for chores, EFX orientation existence is decidable in polynomial time;
  - for mixed manna, the strongest EFX notion may not exist and is NP-complete to decide.
- Misra–Sethia (ADT 2024): EF on binary graphical valuations is decidable in polynomial time, NP-hard with values {0, 1, d}; the price of EFX is 1 for binary — [arXiv 2410.14272](https://arxiv.org/abs/2410.14272) [abstract].

### Inferences
- The weaker (ordinary-EFX) orientation always exists on graphs (Zhou et al.), and ordinary EFX is trivial on multigraphs (Sgouritsa–Sotiriou Remark 1). This is the graph-side mirror of Viswanathan–Mehta's 4-limited result being *ordinary* EFX: in each case the hard content is the zero-valued goods.
- Zeng–Mehta's bipartite orientation is a one-round serial dictatorship on one colour class, then "everything else to the other side". This is the same mechanism as our k ≤ 2 serial dictatorship and as Hosseini et al.'s lexicographic algorithm (§4). No hypergraph analogue of strong orientability was found.

### Gaps
- No orientation result for hypergraphs (p ≥ 3) or for bounded-degree hypergraphs was found.

## 3. Hypergraphs (goods valued by ≥ 3 agents): exact results, and exactly where girth is used

### Takeaway
The only exact EFX₀ results with p ≥ 3 and no bound on n, m or values are Lianeas–Sgouritsa–Sotiriou's two theorems (girth ≥ 4; monotone valuations). Reading their proof shows that girth ≥ 3 (linearity) is used globally, while girth ≥ 4 is used only around the pre-chosen parking vertex 0. Degree plays no role anywhere. Everything else with p ≥ 3 and q = 1 is approximate (EF2X, partial EFX₀, √2/2-EFX). Viswanathan–Mehta's 4-limited result is the only degree-bounded hypergraph result besides ours, and it is ordinary EFX with a sketch only.

### Cited Findings
**Lianeas–Sgouritsa–Sotiriou, "EFX Allocation In (Multi)Hypergraphs", arXiv 2608.03171v1.** Peer-reviewed: AAAI-26, 40(20):17102–17110, per Crossref in `proofs/citations.md`. [full: all of §1–5 and App. A; reference list skimmed]
- Model: monotone normalised valuations; edges not incident to i are irrelevant: vᵢ(S ∪ {e}) = vᵢ(S). EFX is "vᵢ(Xᵢ) ≥ vᵢ(Xⱼ \ {g}), ∀g ∈ Xⱼ" (EFX₀). A Berge cycle of length k is (x₁, e₁, …, x_k, e_k, x₁) with distinct vertices and distinct edges, and girth is the shortest cycle length — [arXiv 2608.03171](https://arxiv.org/abs/2608.03171).
- Theorem 1: "Instances on hypergraphs of girth at least 4 always admit an EFX allocation that can be constructed in polynomial time" — [arXiv 2608.03171](https://arxiv.org/abs/2608.03171).
- Theorem 2: "For multi-hypergraphs with girth at least 4 where there exists a vertex whose incident edges have multiplicity at most the edge's size minus 2, there exists an EFX allocation constructed in pseudo-polynomial time". The girth is that of the underlying simple hypergraph — [arXiv 2608.03171](https://arxiv.org/abs/2608.03171).
- The two structural observations:
  - Obs. 2.1 (girth ≥ 3): "any two vertices may share at most one edge".
  - Obs. 2.2 (girth ≥ 4): "any two vertices of an edge e do not share any other common neighbor outside e".
  - Source: [arXiv 2608.03171](https://arxiv.org/abs/2608.03171).
- Algorithm.
  - An arbitrary vertex is named 0. Its neighbours get labels 1..n₀ and the rest n₀+1..n−1, and "vertices will be prioritized based on their names-labels, in a decreasing order".
  - FixProp3 repeatedly gives the highest-labelled vertex that prefers some unallocated edge e to its bundle its best single unallocated edge.
  - Algorithm 2 then offers each envied i all of Uᵢ(X) whenever vᵢ(Uᵢ(X)) > vᵢ(Xᵢ), re-running FixProp3 each time.
  - Algorithm 3 orients each leftover edge to a non-envied endpoint and gives everything else to vertex 0.
  - Source: [arXiv 2608.03171](https://arxiv.org/abs/2608.03171).
- The four properties:
  1. a partial EFX orientation;
  2. vertex 0 non-envied, and a neighbour of 0 envied only if it holds the edge it shares with 0;
  3. vᵢ(Xᵢ) ≥ vᵢ(e) for every e ∈ Uᵢ(X);
  4. every envied i has vᵢ(Xᵢ) ≥ vᵢ(Uᵢ(X)).
  - Source: [arXiv 2608.03171](https://arxiv.org/abs/2608.03171).
- **Exactly where the girth hypotheses are used in §3 (Theorem 1):**
  - Lemma 3.2 (giving Uᵢ(X) to i keeps EFX): "By Observation 2.1, for any other vertex j, Uᵢ(X) contains at most one edge … relevant to j".
  - Lemma 3.3 (0 never envied) uses *no* girth, only the priority order. FixProp3 considers 0 last, so whenever 0 receives an edge no other vertex wants any unallocated edge.
  - Lemma 3.4 (Property 2):
    - |Xᵢ| > 1 ⇒ i is non-envied, by Obs. 2.1 and EFX;
    - for |Xᵢ| = 1 with e not the edge shared with 0: a neighbour j of 0 in the edge 0 shares with i does not value e (Obs. 2.1);
    - a neighbour j of 0 *not* in that edge does not value e, because "Due to Observation 2.2, vertices i, j cannot both belong in the same edge … or else they would have vertex 0 as a common neighbor outside e′".
  - Lemma 3.5 (Algorithm 3): orienting a leftover edge to a non-envied endpoint is safe because e is the only edge the other endpoints share with it (Obs. 2.1). Dumping on 0 is safe because every envied i either is not adjacent to 0 or holds its shared edge with 0 (Property 2), so vᵢ(X₀) = 0.
  - Source for all four: [arXiv 2608.03171](https://arxiv.org/abs/2608.03171).
- §4 (Theorem 2).
  - FixProp3Gen "basically applies rule U1 of [Chaudhury–Kavitha–Mehlhorn–Sgouritsa] to each patch separately". A patch P_e is the set of all copies of edge e. Subroutine 7 finds an inclusion-wise minimal envied subset.
  - Property 4 is required for all i ≠ 0.
  - Algorithm 6 uses two non-envied vertices j₁, j₂ ∈ e (where X₀ ⊆ P_e) that hold no edge of P_e; they exist because |P_e| ≤ |e| − 2. It parks the other vertices' leftovers on j₁ and j₁'s on j₂.
  - Lemma 4.8 uses Obs. 2.1, and Obs. 2.2 in the form "i and j₁ do not have any common neighbor outside e".
  - Termination is by social welfare, hence pseudo-polynomial.
  - Source: [arXiv 2608.03171](https://arxiv.org/abs/2608.03171).
- Lemma 4.1 (why the multiplicity condition matters): any instance with n agents and m ≥ n goods (positive monotone valuations) embeds into a girth-∞ multi-hypergraph with an extra vertex 0, the edge e₀ = {0, 1}, and all other goods as copies of the edge [n]. An EFX allocation there gives an EFX allocation of the original instance with at most one unallocated good — [arXiv 2608.03171](https://arxiv.org/abs/2608.03171).
- The authors' summary: "We introduce a different angle … by designating from the start special vertices to allocate non-oriented edges"; "any restrictions come merely from the structure of the multi-hypergraph" — [arXiv 2608.03171](https://arxiv.org/abs/2608.03171).

**Approximate and partial results for p ≥ 3, q = 1 (girth ≥ 3 = "two agents share at most one good").**
- Kaviani–Seddighin–Shahrezaei, (∞, 1)-bounded, monotone: a partial EFX₀ allocation discarding ≤ ⌊n/2⌋ − 1 goods (Thm 5.6) and a complete EF2X allocation (Thm 5.7). Subadditive: √2/2-EFX (Thm 7.1). Restricted additive: √2/2-EFX (Thm 6.1) — [arXiv 2407.05139](https://arxiv.org/abs/2407.05139) [repo-full].
- Kakatelis–Lianeas–Sgouritsa–Sotiriou — [arXiv 2606.26948](https://arxiv.org/abs/2606.26948) [repo-full]:
  - girth ≥ 3: EF2X (monotone; polynomial time) and √2/2-EFX (subadditive);
  - multiplicity ≤ 2: EF3X and 2/3-EFX (additive).
- Akrami–Rezvan–Seddighin, restricted additive with no structural bound: complete EF2X, and EFX discarding ≤ ⌊n/2⌋ − 1 goods — [arXiv 2202.13676](https://arxiv.org/abs/2202.13676) [abstract].
- Search completeness (2026-11-26): the arXiv search "EFX hypergraph" (all fields) returns only 2606.26948 and 2608.03171 — [arXiv search](https://arxiv.org/search/?query=EFX+hypergraph&searchtype=all).

**Degree-bounded (agent-side) hypergraph result.** Viswanathan–Mehta (AAMAS 2024 extended abstract) — [AAMAS PDF](https://www.ifaamas.org/Proceedings/aamas2024/pdfs/p2534.pdf) [repo-full, 3 pp.]:
- ordinary EFX for additive "4-limited" instances (each agent likes ≤ 4 goods), and for ternary {0, a, b} with b ≤ 2a;
- the leftover goods, "valued zero by all agents", go "to an arbitrary agent";
- the proof is sketched only: phases of maximum matchings on "k-th value graphs", then an "EFX graph" source argument.

### Inferences
- **Our reading of Theorem 1 (not a claim of the authors; verify before citing).** In §3, Obs. 2.2 is invoked only in Lemma 3.4, and only for two neighbours i, j of vertex 0 that lie in different edges through 0. Every other step uses Obs. 2.1 or the label priority. So the proof as written seems to show EFX₀ (monotone valuations, polynomial time) for every **linear hypergraph (q = 1) that has at least one vertex on no Berge 3-cycle**, taking that vertex as 0.

  For Theorem 2, Lemma 4.8 also uses Obs. 2.2 for vertices i, j₁ of an edge e through 0. That forbids Berge 3-cycles that use an edge through 0 even when they avoid 0. So the needed condition there is a little stronger: no Berge triangle meets an edge at 0.
- **Private goods.** Two private goods of one agent form a repeated singleton edge, so Theorem 1 (simple hypergraphs) does not apply, and Theorem 2 needs the multiplicity condition at vertex 0. A singleton edge at 0 would need multiplicity ≤ 1 − 2 < 0. So vertex 0 must have no private goods, and every edge e at 0 must have ≤ |e| − 2 copies. Our cores, where most agents have private or shared-pair goods, rarely meet this.
- **Degree ≤ k and Lianeas.** Nothing in their proof uses degree, so for k ≤ 3 they add nothing to TARGET. For k = 4 they would cover the linear instances with a vertex on no Berge triangle. The `proofs/pq_bounded.md` obstruction family H_t (p = 4, q = 1, Berge girth 3) is linear. A cheap test for the k = 4 workstream: does some vertex of H_t avoid all Berge 3-cycles? If so, the Lianeas algorithm (implemented with our reading) should produce an EFX₀ allocation of H_t even for monotone valuations.
- **Monotone versus additive.** Lianeas et al. get *monotone* exact results, whereas our k = 3 theorem is additive. Their proofs exploit the structural bound "a bundle contains ≤ 1 relevant good per pair", which makes monotone comparisons single-good comparisons. That is exactly what fails at q ≥ 2.

### Gaps
- No exact EFX₀ result was found for p ≥ 3 with Berge triangles, nor any result parameterised by edge size p alone (e.g. p = 3). The (k, p) = (4, 3) cell of `proofs/pq_bounded.md` remains uncovered by the literature.
- No hypergraph analogue of Sgouritsa–Sotiriou's neighbour bound was found, nor of Bhaskar–Pandit's multi-tree leaf induction (Berge-acyclic hypergraphs).
- Viswanathan–Mehta's 4-limited proof is not available beyond the 3-page sketch (repo: no full version exists).

## 4. Valuation-class restrictions (values, not incidence): exact statements and zero handling

### Takeaway
Exact EFX₀ is known for binary (0/1) additive valuations (every maximum-Nash-welfare allocation), for 2-value instances, for personalized bivalued valuations including b_i = 0, for binary-marginal non-additive valuations, for identical monotone valuations, and for lexicographic preferences (no zeros in that model). For our problem these say that agents who value all their relevant goods equally are easy for every k; the difficulty sits with agents whose relevant goods have distinct values. The standard EFX → EFX₀ reduction (zeros ↦ ε) destroys sparsity, so ordinary-EFX results for few relevant goods (Viswanathan–Mehta) do not transfer to EFX₀.

### Cited Findings
**Amanatidis–Birmpas–Filos-Ratsikas–Hollender–Voudouris, "Maximum Nash Welfare and Other Stories About EFX".** Peer-reviewed: *TCS* 863 (2021) 69–85. [section: abstract, §1, §2 incl. Prop. 2.3 with proof, statements of Thms 3.1–3.2]
- Both notions are named: "for the latter case we adopt the name EFX0 suggested by Kyropoulou et al.", and the paper notes EF ⇒ EFX₀ ⇒ EFX ⇒ EF1 — [arXiv 2001.09838](https://arxiv.org/abs/2001.09838).
- Thm 3.1: "For every binary instance, any MNW allocation is EFX0", where MNW means first maximise the number of agents with positive value, then the product of values — [arXiv 2001.09838](https://arxiv.org/abs/2001.09838).
- Thm 3.2: for 2-value instances with a > b > 0, any MNW allocation is EFX; "in this case EFX0 coincides with EFX". MNW ⇒ EFX₀ fails for ≥ 3 values. There is also a polynomial-time algorithm for 2-value EFX₀ — [arXiv 2001.09838](https://arxiv.org/abs/2001.09838).
- Prop. 2.3: computing EFX₀ for k-value instances reduces to computing EFX for k-value instances, by replacing every 0 with ε < δ/m. Hence additive EFX existence would imply additive EFX₀ existence — [arXiv 2001.09838](https://arxiv.org/abs/2001.09838).

**Byrka–Malinka–Ponitka, "Probing EFX via PMMS".** arXiv 2507.14957v2; AAAI 2026 per `proofs/novelty.md` [venue not checked here]. [section: abstract, §1 results, Def. 2.5, EFX definition, Example 2.9 discussion, §4 opening, Lemma 4.1]
- Def. 2.5: personalized bivalued means additive with "values aᵢ > bᵢ ≥ 0 such that vᵢ({g}) ∈ {aᵢ, bᵢ}". The paper adds: "Whenever we write aᵢ/bᵢ and bᵢ = 0, we interpret it as a sufficiently large number K" — [arXiv 2507.14957](https://arxiv.org/abs/2507.14957).
- Theorem 2: EFX exists for personalized bivalued valuations, with EFX in the all-goods form (EFX₀). It is PMMS when every aᵢ is a multiple of bᵢ. The proof uses a personalised Match-and-Freeze algorithm (from Amanatidis et al.); the MNW argument does not extend (Prop. 4.6). Jin–Tao (arXiv 2507.18251) found the same independently — [arXiv 2507.14957](https://arxiv.org/abs/2507.14957).
- Other results: PMMS exists for binary-valued MMS-feasible valuations (vᵢ(S) ∈ {0, 1}) and for "pair-demand" valuations, where "each agent derives value from at most two items". There is a 3-agent instance with no PMMS allocation — [arXiv 2507.14957](https://arxiv.org/abs/2507.14957) [abstract].
- On zero-valued goods: "The key issue … is the presence of zero-valued items". Many works use EFX>0, and PMMS ⇒ EFX>0 for additive valuations — [arXiv 2507.14957](https://arxiv.org/abs/2507.14957).

**Other value classes.**
- Binary marginals (non-additive), Bu–Song–Yu: if vᵢ(S ∪ {g}) − vᵢ(S) ∈ {0, 1}, an EFX allocation (Def. 2.1: "any item g ∈ Aⱼ", i.e. EFX₀) exists and is computable in polynomial time (Thm 3.1, via a social-welfare potential and a U1-type rule) — [arXiv 2308.05503](https://arxiv.org/abs/2308.05503) [section: abstract, §2, Thm 3.1].
- Babaioff et al. compute an MNW EFX₀ allocation for submodular dichotomous valuations — [as reported in 2001.09838](https://arxiv.org/abs/2001.09838) [original unverified].
- Bivalued EFX + fPO:
  - Liu–Zhang (Apr 2026) "provide a counterexample demonstrating that [Garg–Murhekar's 2021] algorithm may fail to terminate" and give a polynomial WEFX + fPO algorithm instead — [arXiv 2604.08345](https://arxiv.org/abs/2604.08345) [abstract] [preprint].
  - Lin–Wu–Zhou give tight MNW guarantees for (personalized) bi-valued instances and show they deteriorate for tri-valued ones — [arXiv 2610.00122](https://arxiv.org/abs/2610.00122) [abstract] [preprint].
- Ternary {0, a, b} with b ≤ 2a: ordinary EFX only, sketch only (Viswanathan–Mehta) — [AAMAS PDF](https://www.ifaamas.org/Proceedings/aamas2024/pdfs/p2534.pdf) [repo-full].
- Restricted additive vᵢ(g) ∈ {0, v_g}: EF2X (Akrami–Rezvan–Seddighin); √2/2-EFX (Kaviani et al. Thm 6.1); exact when p ≤ 2 (Kaviani et al. Thm 8.1); a polynomial EEFX + EF1 algorithm (Akrami–Feige–Mahara–Mehlhorn–Rathi) — [2202.13676](https://arxiv.org/abs/2202.13676); [2407.05139](https://arxiv.org/abs/2407.05139); [2602.11732](https://arxiv.org/abs/2602.11732) [abstract].
- Lexicographic preferences, Hosseini–Sikdar–Vaish–Xia (AAAI 2021) — [arXiv 2012.07680](https://arxiv.org/abs/2012.07680) [section: §2, Prop. 1, Alg. 1, Thm 1]:
  - preferences are strict linear orders over all of M (no zero goods), and EFX removes any good;
  - Prop. 1: "An allocation A is EFX if and only if each envied agent in A gets exactly one good";
  - Algorithm 1: "a single round of serial dictatorship", then the leftover goods go "among the unenvied agents according to a picking sequence";
  - Thm 1: these are exactly the EFX + PO allocations.
- Identical monotone valuations, Plaut–Roughgarden (SODA 2018; *SIDMA* 2020): a modified leximin is EFX. With "nonzero marginal utility", leximin is EFX + PO for identical general valuations and for two additive players. Without it, some cases have no EFX + PO allocation — [arXiv 1707.04769](https://arxiv.org/abs/1707.04769) [abstract; grep of §1]. Their EFX tests "the removal of every good, including goods of zero marginal value" — [as described in 2604.18216v4](https://arxiv.org/abs/2604.18216).
- Few valuation types (types of agents, not incidence):
  - EFX for ≤ 3 distinct additive valuations (EC 2025) — [arXiv 2410.13580](https://arxiv.org/abs/2410.13580) [abstract; notion not checked];
  - 2/3-EFX for ≤ 4 types — [arXiv 2508.15380](https://arxiv.org/abs/2508.15380) [abstract];
  - EFX + PO for two types of *goods* with positive valuations (AAAI 2026) — [arXiv 2601.03438](https://arxiv.org/abs/2601.03438) [abstract].
- Range-parameter approximations: Barman–Kar–Pathak use EFx "up to the removal of any positively-valued good", i.e. ordinary EFX — [arXiv 2312.13791](https://arxiv.org/abs/2312.13791) [abstract].
- "Few relevant goods" in other notions:
  - Gowda et al.: round-robin EF1 is CC-hard even when each agent values ≤ 3 goods and each good ≤ 3 agents (complexity, not existence) — [arXiv 2605.16791](https://arxiv.org/abs/2605.16791) [repo-grep].
  - Pair-demand PMMS (Byrka et al., above).
  - A web search found nothing on MMS or EF1 existence parameterised by relevant goods per agent — [search result list incl. 2409.01963](https://arxiv.org/abs/2409.01963).

### Inferences
- **Flat agents are easy for every k.** If every agent values all its relevant goods equally, the instance is binary up to per-agent scaling, which EFX₀ does not see. Then any MNW allocation is EFX₀ (Amanatidis et al. Thm 3.1), with no bound on k. Byrka et al. allow b_i = 0 and mixtures of agents with different ratios aᵢ/bᵢ. So a counterexample to EFX₀ at k = 4, if one exists, needs agents with at least two distinct positive values among their relevant goods.
- **Prop. 2.3 does not preserve k.** The perturbation makes every good relevant to every agent (value ε). So Viswanathan–Mehta's ordinary EFX for 4-limited instances, and for ternary {0, a, b}, does not yield EFX₀ through this route. The perturbed instance is no longer 4-limited, and no longer of the form {0, a, b}.
- **Lexicographic shape.** For lexicographic agents, EFX reduces to "every envied agent holds one good". This is the extreme case of our "unbalanced" agent (top > sum of the rest) and of Viswanathan–Mehta's Phase I (top > second + third). It suggests treating unbalanced agents by serial dictatorship before the balanced core, which is consistent with the project's peeling rule R1.

### Gaps
- Whether HV et al.'s three-types result is EFX₀ was not checked.
- Garg–Murhekar (SAGT 2021) itself was not read; only Liu–Zhang's abstract claims the termination flaw.
- No existence result for MMS, EF1 variants or PMMS parameterised by "relevant goods per agent" was found.

## 5. Non-existence and computer-assisted results

### Takeaway
EFX (all-goods form) is now refuted for monotone, even weighted-coverage (submodular), valuations: 3 agents and 8 goods, every agent valuing every good. That is a degree-8, p = 3, girth-∞ multi-hypergraph. So for monotone valuations the smallest degree k at which EFX₀ can fail lies in {3, …, 8}: k ≤ 2 holds and k = 8 fails. Additive EFX/EFX₀ stays open for n ≥ 4. Structural non-existence results otherwise concern orientations only.

### Cited Findings
- Akrami–Mackenzie–Mayorov–Mehlhorn–Srinivas–Suzuki–Weidenbach, "EFX Need Not Exist", arXiv 2604.18216v4 (10 Nov 2026). It consolidates 2604.18216v3 with Mackenzie–Suzuki 2605.06451. [section: abstract, §1 pp. 1–4, §3.1 construction pp. 7–8, Lemma 3.5 pp. 12–13] [preprint]
  - Thm 1.1: "There exists a fair division instance with three agents and eight goods in which all agents have weighted coverage valuations and no EFX allocation exists" — [arXiv 2604.18216](https://arxiv.org/abs/2604.18216).
  - Thm 1.2: every instance with three agents, at most seven goods and monotone valuations has an EFX allocation — [arXiv 2604.18216](https://arxiv.org/abs/2604.18216).
  - EFX existence for monotone valuations is equivalent to EFX existence for weighted-coverage valuations — [arXiv 2604.18216](https://arxiv.org/abs/2604.18216).
  - The paper follows Plaut–Roughgarden's convention ("tests the removal of every good, including goods of zero marginal value") — [arXiv 2604.18216](https://arxiv.org/abs/2604.18216).
  - The construction (§3.1):
    - goods M = {A₁, A₂, B₁, B₂, C₁, C₂, x, y}, with agents a, b, c associated with types A, B, C;
    - "uᵢ({g}) = 1 for every good g", and a larger bundle is worth its best pair, ranked Ty > UV > Tx > Uy, Vy > TU, TV > the rest;
    - vᵢ = 7 on bundles containing an exceptional triple UVx;
    - the counterexample is symmetric under simultaneous relabelling of agents and types.
    - Source: [arXiv 2604.18216](https://arxiv.org/abs/2604.18216).
  - Extensions: Lemma 3.5 extends the counterexample to all n ≥ 3 and m ≥ n + 5. It adds copies of one agent c and new goods worth L only to those copies, then dummy goods of value zero — [arXiv 2604.18216](https://arxiv.org/abs/2604.18216).
  - Bounds: α-EFX fails for subadditive valuations for α > 2^(−1/6) ≈ 0.891, and for submodular ones for α > 0.958. Positively, when two agents are arbitrary monotone and one is subadditive, there is an allocation that is EFX for the two and 2^(−1/3)-EFX for the third — [arXiv 2604.18216](https://arxiv.org/abs/2604.18216).
  - Method: a SAT/SMT search found the first version, followed by pen-and-paper proofs; "the first use of SAT/SMT solving for EFX" — [arXiv 2604.18216](https://arxiv.org/abs/2604.18216). v3's §9 has a Lean proof of the soundness of the SAT encoding (`proofs/citations.md`).
- Mackenzie–Suzuki v2 (18 Nov 2026) is merged into the above — [arXiv 2605.06451](https://arxiv.org/abs/2605.06451) [abstract].
- Hosseini–Khurana–Pathak–Vaish: even the agent-wise disjunction "EFX or MMS" can fail, with 3 agents and 8 submodular goods, or 3 agents and 7 submodular chores — [arXiv 2608.10397](https://arxiv.org/abs/2608.10397) [abstract] [preprint].
- Additive, computer-assisted: Alkassar–Fouz–Mehlhorn prove EFX₀ for 4 additive agents with ≤ 9 goods (SMT certificates, independent certifier) — [arXiv 2608.08590](https://arxiv.org/abs/2608.08590) [repo-full]. Chores: non-existence for binary-marginal XOS or supermodular costs, verified in Lean — [arXiv 2608.10572](https://arxiv.org/abs/2608.10572) [repo-abstract].
- Structural non-existence (orientations only):
  - CFKS's K4 example and Prop. 14 — [CFKS PDF](https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/fair-allocations-on-graphs.pdf);
  - bipartite multi-trees and cycles, Thms 3.2, 3.4, 3.5 — [arXiv 2410.17002](https://arxiv.org/abs/2410.17002);
  - non-trivial odd multitrees — [arXiv 2410.12039](https://arxiv.org/abs/2410.12039);
  - for mixed manna on graphs, the strongest EFX notion may not exist — [arXiv 2409.03594](https://arxiv.org/abs/2409.03594).
- A hardness transfer, not a non-existence result: Lianeas et al. Lemma 4.1 (§3 above) — [arXiv 2608.03171](https://arxiv.org/abs/2608.03171).

### Inferences
- **Incidence structure of the counterexample.** Every agent values every good positively (singletons are worth 1). So the 3-agent instance is one 3-vertex hyperedge of multiplicity 8: k = 8, p = 3, q = 8, Berge girth ∞. The extensions of Lemma 3.5 have degree ≥ 8 as well.
  - For monotone, even weighted-coverage, valuations, "every agent values ≤ k goods ⇒ EFX₀" is false at k = 8.
  - It holds at k ≤ 2 (`mrd-efx` `MRDMono`, this project).
  - For monotone valuations with 3 ≤ k ≤ 7, no source either way was found. Our k = 3 theorem is additive only.
- **Consequence for Lianeas et al.** The same instance shows that the multiplicity hypothesis of their Theorem 2 cannot simply be dropped for monotone valuations: girth ∞, but multiplicity 8 > |e| − 2 = 1, and no EFX allocation. This is a genuine non-existence result, stronger than the hardness transfer of their own Lemma 4.1.
- No monotone counterexample with p ≤ 2 (multigraph) is known. The only known counterexample needs a good valued by three agents, and indeed every good is valued by all three.

### Gaps
- Whether a sparser monotone counterexample exists (fewer relevant goods per agent, or p = 2) is not addressed by the paper's abstract or by §1–3.
- No SAT/SMT search restricted to degree-bounded *additive* instances was found in the literature, other than this project's own.

## 6. Zero-valued goods: which papers handle EFX₀ explicitly, and how

### Takeaway
Nearly all structural papers use EFX₀ (removal of any good) and must place goods with agents who value them 0. Four techniques recur:
- (i) a pre-designated sink that is never envied (Lianeas: lowest priority);
- (ii) safe sets, i.e. unenvied agents whose bundle stays unattractive after adding the dumped goods (CFKS; 2410.17002);
- (iii) dumping onto the unique envier (2410.17002; 2512.21644), which is a p = 2 device;
- (iv) giving the leftover to an envy-graph source and rotating the cycle if needed (Bhaskar–Pandit trees).

Only Viswanathan–Mehta works with ordinary EFX, and they dump "to an arbitrary agent". Perturbing zeros to ε (Amanatidis et al.) handles zeros in value classes but destroys incidence structure.

### Cited Findings
- **CFKS** (EFX₀): zero-value edges are added to make the graph complete; leftover edges are "parked" at a non-envied endpoint or at a vertex in Sᵢ ∩ Sⱼ (Lemma 13). §6 calls parking a property of their solutions: "items are 'parked' at vertices that have no value for them" — [CFKS PDF](https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/fair-allocations-on-graphs.pdf).
- **Lianeas et al.** (EFX₀): vertex 0 gets the lowest priority, so it is never envied (Lemma 3.3), and it receives every edge whose endpoints are all envied (Algorithm 3). In the multi-hypergraph case two extra parking vertices j₁, j₂ are taken inside 0's edge — [arXiv 2608.03171](https://arxiv.org/abs/2608.03171).
- **2410.17002** (EFX₀): safe sets Sᵢ(X), and Property 6 (the envier lies in the safe set). Algorithm 5 gives Aᵢ(X) to i's envier — [arXiv 2410.17002](https://arxiv.org/abs/2410.17002).
- **2512.21644** (EFX₀): Algorithm 3, "Dumping Remaining Items", gives B⁽¹⁾ᵢ to the agent who envies i — [arXiv 2512.21644](https://arxiv.org/abs/2512.21644).
- **2606.18665** (EFX₀): dumping onto unenvied sinks after building "support pairs"; recipients of goods they do not value must be completely unenvied — [arXiv 2606.18665](https://arxiv.org/abs/2606.18665) via `proofs/multigraph_digest.md` §4 items 9–11.
- **Bhaskar–Pandit** (EFX₀): Tree-EFX gives the leftover Ā_ℓ to p if p is a source, else to "a source with a path P to p", resolving the envy cycle if p then envies s — [arXiv 2412.06513](https://arxiv.org/abs/2412.06513).
- **Sgouritsa–Sotiriou** (EFX₀): parking at non-envied non-neighbours; Remark 1 says ordinary EFX is trivial on multigraphs — [arXiv 2502.09777](https://arxiv.org/abs/2502.09777) [repo-full].
- **Amanatidis et al.** treat EFX and EFX₀ explicitly. MNW is EFX₀ for binary instances (zeros included). Prop. 2.3 reduces EFX₀ to EFX by zeros ↦ ε — [arXiv 2001.09838](https://arxiv.org/abs/2001.09838).
- **Hosseini et al.**: there are no zero goods, and leftover goods go to unenvied agents by a picking sequence — [arXiv 2012.07680](https://arxiv.org/abs/2012.07680).
- **Akrami et al. v4**: the all-goods convention; the extension pads instances with "dummy items of value zero" — [arXiv 2604.18216](https://arxiv.org/abs/2604.18216).
- **Viswanathan–Mehta**: ordinary EFX; footnote 2 describes the stronger notion; leftover goods go "to an arbitrary agent" — [AAMAS PDF](https://www.ifaamas.org/Proceedings/aamas2024/pdfs/p2534.pdf) [repo-full].
- **Byrka et al.** use the all-goods EFX and discuss EFX>0 separately (PMMS ⇒ EFX>0) — [arXiv 2507.14957](https://arxiv.org/abs/2507.14957).
- **Naming**: Amanatidis et al. attribute the name EFX₀ to Kyropoulou–Suksompong–Voudouris (IJCAI 2019; *TCS* 841, 2020) — [arXiv 2001.09838](https://arxiv.org/abs/2001.09838); [arXiv 1901.08463](https://arxiv.org/abs/1901.08463) [abstract].

### Inferences
- Our L3 ("worthless goods must go to an envy-graph source") is technique (iv) in its simplest form. Techniques (i)–(iii) are certificates that the sink's bundle stays *invisible* to the goods' valuers, and each is guaranteed by a structural hypothesis.
- With degree ≤ k but unbounded p, invisibility cannot come from structure, since a good may be seen by many agents. It has to come from values ("budget" inequalities like Property 4 or safe sets), which is how our k = 3 proof already works.
- Technique (i) seems the most portable to degree-bounded hypergraphs: pre-commit one agent as the sink, give it lowest priority in every greedy step, and keep all its neighbours "satisfied by their shared good" (Lianeas Property 2). Its structural cost is that the sink's neighbours must not see each other's goods (the Berge-triangle condition at 0). In a degree-≤ k instance the sink has ≤ k incident goods, so the condition concerns only a bounded neighbourhood. Note, though, that with unbounded p that neighbourhood can be large.

### Gaps
- No paper was found that isolates "how to place zero-valued goods" as a stand-alone lemma valid for hypergraphs with short cycles.

## 7. Gap analysis: where agent-side (degree ≤ k) and structure-side work could meet

### Takeaway
Six concrete meeting points. Two of them are free strengthenings of published proofs that still need verification:
- Lianeas et al. need girth ≥ 4 only around the parking vertex;
- Sgouritsa–Sotiriou's neighbour bound becomes a degree bound for p ≤ 2.

The others are research directions: the (4, 3) cell, a two-envier dump rule, matching-based starts, and the monotone threshold (3 ≤ k ≤ 7 open). No published structural theorem settles any part of the 4-relevant-goods EFX₀ case beyond the cases p ≤ 2, girth ≥ 4, n ≤ 3, n = 4 with m ≤ 9, m ≤ n + 3, and the value classes of §4.

### Cited Findings
- Covered parts of the k = 4 EFX₀ problem, one bullet per published result:
  - p ≤ 2: exact for cancelable valuations — [2606.18665](https://arxiv.org/abs/2606.18665);
  - girth ≥ 4: exact for monotone valuations — [2608.03171](https://arxiv.org/abs/2608.03171);
  - m ≤ n + 3: monotone — [2107.09901](https://arxiv.org/abs/2107.09901) [repo-full];
  - n = 3: additive — CGM, [2002.05119](https://arxiv.org/abs/2002.05119) [repo-section];
  - n = 4, m ≤ 9: additive — [2608.08590](https://arxiv.org/abs/2608.08590);
  - binary or 2-value — [2001.09838](https://arxiv.org/abs/2001.09838);
  - personalized bivalued — [2507.14957](https://arxiv.org/abs/2507.14957);
  - identical valuations — [1707.04769](https://arxiv.org/abs/1707.04769).
- The only degree-bounded hypergraph result besides ours is ordinary EFX, with a sketch — [Viswanathan–Mehta](https://www.ifaamas.org/Proceedings/aamas2024/pdfs/p2534.pdf).
- Hooks used below:
  - Lianeas Lemma 3.4 is the only use of Obs. 2.2 in §3 — [2608.03171](https://arxiv.org/abs/2608.03171);
  - Sgouritsa–Sotiriou Thm 2 (neighbour bound) — [2502.09777](https://arxiv.org/abs/2502.09777);
  - the unique envier exists only for p = 2 (Lemma 2.10) — [2410.17002](https://arxiv.org/abs/2410.17002);
  - 2410.17002's diagnosis that adjacent envied pairs need |Sᵢ ∩ Sⱼ| ≥ 2 — [2410.17002](https://arxiv.org/abs/2410.17002);
  - Kaviani et al.'s Nash-welfare rankpath potential — [2407.05139](https://arxiv.org/abs/2407.05139);
  - the U1 social-welfare potential per patch — [2608.03171](https://arxiv.org/abs/2608.03171); [2308.05503](https://arxiv.org/abs/2308.05503).

### Inferences
1. **Lianeas with a local girth condition (cheap to verify; possibly publishable as a remark).** Per §3, Theorem 1's proof seems to need only q = 1 globally plus one vertex on no Berge 3-cycle. Next steps:
   - re-check every use of Obs. 2.2;
   - implement the algorithm and test it on linear k = 4 instances (in particular H_t) that have such a vertex.

   If it holds, any linear degree-4 instance with a "Berge-triangle-free" agent is EFX₀ even for monotone valuations.
2. **Sgouritsa–Sotiriou Thm 2 as a degree theorem.** For p ≤ 2 and monotone valuations it would give EFX₀ whenever k ≤ ⌈n/4⌉ − 1, which leaves n ≤ 4k (§1 inference; check the private-good modelling). A hypergraph version would need, in place of "envied by at most one neighbour", a bound on enviers per held good: at most p − 1, hence at most k(p − 1) neighbours. So the natural hypergraph analogue is a condition on both k and p, matching the (k, p) table of `proofs/pq_bounded.md`.
3. **The (4, 3) cell.** With k = 4 and p = 3, a held good has ≤ 2 other viewers, so at most two enviers. 2410.17002's suggested fix (|Sᵢ ∩ Sⱼ| ≥ 2 for adjacent envied pairs) and Lianeas's two auxiliary sinks j₁, j₂ are both "two parking spots" devices. A *two-envier dump rule*, in which the dumped goods split between the two enviers or two safe agents, is the obvious generalisation to try. No paper attempts it.
4. **Matching starts on "k-th value graphs".** Three starting rules appear in the literature:
   - Viswanathan–Mehta's phases (maximum matchings of agents to their first and second choices);
   - Sgouritsa–Sotiriou's maximum-weight matching on first/second choices, which leaves ≤ ⌊n/2⌋ envied agents;
   - Match-and-Freeze for (personalized) bivalued valuations.

   All three are concrete initial-allocation rules for Draft and Exchange at k = 4 (also suggested in `proofs/pq_bounded.md` §3.2). None comes with an EFX₀ proof for k ≥ 4.
5. **Value-class reductions.** Agents whose relevant goods are all equal (binary) can be absorbed by an MNW-style argument for any k (Amanatidis et al. Thm 3.1). A mixed statement, "EFX₀ when every agent either has ≤ 3 relevant goods or is binary", may be provable by combining Draft and Exchange with Match-and-Freeze. This is untested.
6. **The monotone threshold.** The smallest k at which monotone EFX₀ can fail lies in {3, …, 8} (§5). Lianeas et al. show that monotone exact results are possible when the structure forbids two relevant goods of one agent inside another agent's bundle. Whether Draft and Exchange works for monotone valuations at k = 3 is a well-posed question that would align our k = 3 result with the structure-side papers, which are all monotone.
7. **Hypertrees.** Bhaskar–Pandit's leaf induction (monotone) would extend to Berge-acyclic hypergraphs only if a leaf hyperedge of size s can be resolved among its s agents with one pre-endowed agent. That is a constrained s-agent EFX problem, hard for s ≥ 3 in general. With k ≤ 3 per agent it falls inside our theorem, so hypertrees with k = 4 are a possible small test class.

### Gaps
- Inferences 1 and 2 are readings of proofs, not results. Each needs a line-by-line check (Lianeas Lemmas 3.2–3.5 and 4.5–4.8; Sgouritsa–Sotiriou's model on zero-valued incident edges and Claim 3.13).
- No structural paper discusses degree bounds on the agent side, except via neighbour counts (Sgouritsa–Sotiriou).
- The EC 2026 Christodoulou–Mastrakoulis–Sgouritsa–Sotiriou proof could contain techniques for triangles (p = 2) that transfer, but it is unavailable.
- Whether EFX₀ for additive valuations is equivalent to EFX₀ restricted to bounded-degree instances (a sparsification reduction) is not addressed anywhere found. Amanatidis et al.'s Prop. 2.3 goes the other way, densifying.
