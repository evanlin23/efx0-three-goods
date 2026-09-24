# Citations in PROMPT.md §2: verification status (Step 0)

**Read from the full text (2026-09-24):** Viswanathan–Mehta (AAMAS 2024 extended abstract, PDF) and the arXiv versions of Mahara 2107.09901v2, Afshinmehr et al. 2606.18665v1, Lianeas–Sgouritsa–Sotiriou 2608.03171v1, Wang 2608.30203v1, Alkassar–Fouz–Mehlhorn 2608.08590v1, Akrami et al. 2604.18216v3 and Mackenzie–Suzuki 2605.06451v1. The repository owner pasted the texts into a session because no scholarly host is reachable from the cloud container (list below). Statements below marked "read" are quoted or paraphrased from those texts. Anything not read is still [unverified].

**Result: none of these papers implies TARGET or conjecture D.** Viswanathan–Mehta (at most 4 relevant goods) proves ordinary EFX only and gives worthless goods to an arbitrary agent, so it does not settle TARGET. Two of them cover parts of TARGET for every n (ledger row T3): Mahara's theorem covers cores with m ≤ n + 3, and the multigraph theorem covers cores in which every good is relevant to at most two agents. Neither says anything about D's shape (at most one bundle of more than two goods).

## Per citation

1. **Mahara, "Extension of Additive Valuations to General Valuations on the Existence of EFX", arXiv:2107.09901v2 (26 Jul 2021).** Read.
   - Theorem 3: "For general valuations, there exists a complete EFX allocation when m ≤ n + 3."
   - Valuations: "general" means normalized (v(∅) = 0) and monotone; additive valuations are included.
   - EFX notion: agent i "EFX envies" a set S "if there exists some h ∈ S such that i envies S ∖ h"; an allocation is EFX if no agent EFX envies another. Every good counts, including goods worth 0 to i, so this is EFX₀. L1 is not needed to transfer it.
   - Journal version: *Mathematics of Operations Research* 49(2), cited that way by 2608.08590 and 2606.18665 [journal text not read]. PROMPT.md's [Mah23] is this paper.
   - Use here: every core with m ≤ n + 3 has an EFX₀ allocation, for every n. R1 already certifies this range for n ≤ 6 without the citation. It gives existence only, not D's shape.
2. **Viswanathan–Mehta, "On the existence of EFX under picky or non-differentiative agents", Proc. AAMAS 2024, pp. 2534–2536 (Extended Abstract, 3 pages).** Read (PDF supplied by the repository owner).
   - Results: EFX exists, via a polynomial-time algorithm, (1) when every agent values at most 4 goods positively ("4-limited"), and (2) for ternary values {0, a, b} with 0 < a < b ≤ 2a.
   - EFX notion: **ordinary EFX, not EFX₀.** Agent i EFX-envies i′ if v_i(X_i) < v_i(X_i′ ∖ {j}) "for some j ∈ X_i′ with v_i(j) > 0". Footnote 2 names the stronger version, in which the removed good may be worth zero to i, as a different notion.
   - Zero-valued goods: the 4-limited algorithm ends by giving the remaining goods, "which must be valued zero by all agents, to an arbitrary agent". That step is harmless for EFX but can break EFX₀, which is exactly what TARGET is about (compare L3: worthless goods must go to an envy-graph source).
   - The abstract gives a proof sketch only (phases of maximum matchings in the "k-th value graphs", then an "EFX graph" source argument); no full proof is in the text.
   - Use here: none for TARGET or D. It does not imply TARGET, and L1 does not transfer it, because it is a statement about few relevant goods, not about a class of (n, m) (Note (scope) under L1 in `proofs/lemmas.md`). It confirms that PROMPT.md's description ("ordinary EFX only") is right.
   - Its reference [14] is the conference version of Mahara's paper: ESA 2021, LIPIcs 204, 66:1–66:15.
3. **Christodoulou–Fiat–Koutsoupias–Sgouritsa (EC 2023).** [unverified] Not supplied. 2606.18665 summarizes it as proving EFX for graphical valuations on simple graphs, where each good is an edge valued positively only by its endpoints. Subsumed for additive valuations by item 4.
4. **Afshinmehr–Ashuri–Mahmoudkhan–Mehlhorn–Shahrezaei, "EFX Allocations Exist on Multi-Graphs", arXiv:2606.18665v1 (17 Jun 2026).** Read.
   - Main result (abstract): EFX allocations exist for multigraph instances under cancelable valuations, a strict superclass of additive valuations, and can be computed in polynomial time.
   - Model: agents are the vertices of a multigraph and goods are its edges; for every agent i and set S, v_i(S) = v_i(S ∩ E_i), where E_i is the set of edges at i. Incident goods may be worth 0. Their conclusion: "each good is valued by at most two agents, but pairs of agents may share multiple goods."
   - EFX notion: i strongly envies T with respect to S "if there exists a good g ∈ T such that v_i(T ∖ g) > v_i(S)". This is EFX₀.
   - Use here (our inference, not stated in the paper): take an additive instance with n ≥ 2 agents in which every good is positively valued by at most two agents. Make a good valued by agents i and j an i–j edge. Make a good valued only by i an edge from i to any other agent, which values it 0. Make a good valued by nobody an edge anywhere. The result is a multigraph instance, so an EFX₀ allocation exists. For a core this is the case Σ(deg − 2) = 0 of L4, that is 3n = 2m − π. It gives existence only, not D's shape. PROMPT.md §2 says multigraph cores are included in our exhaustive checks; the theorem covers them for every n.
5. **Chaudhury–Garg–Mehlhorn, "EFX Exists for Three Agents" (JACM 2024).** [unverified] Not supplied. 2608.08590 and 2608.30203 both cite three additive agents as known.
6. **Alkassar–Fouz–Mehlhorn, "Complete EFX Allocations Exist for Four Additive Agents and Up to Nine Goods", arXiv:2608.08590v1 (9 Aug 2026).** Read.
   - Abstract: every instance with four agents, additive valuations over the non-negative reals and at most nine goods has a complete allocation that is EFX "in the strong, zero-tolerant sense (EFX₀)". So PROMPT.md's "EFX₀" is right.
   - Method: hand-proven reductions plus a machine-verified certificate corpus. The valuation polytope is covered by smaller polytopes, each with a family of allocations; sufficiency is a linear-arithmetic UNSAT verdict, re-derived by an independent certifier and re-checkable by a third implementation.
   - Also reports that only about 0.14 % of all 4⁹ allocations are EFX₀ on near-identical valuations.
7. **Akrami–Mayorov–Mehlhorn–Srinivas–Weidenbach, "A Counterexample to EFX n ≥ 3 Agents, m ≥ n + 5 Items, Submodular Valuations via SAT-Solving", arXiv:2604.18216v3 (14 May 2026).** Read (abstract).
   - EFX allocations need not exist for monotone valuations with n ≥ 3 and m ≥ n + 5; this gives a submodular counterexample too. Every instance with three agents and seven goods has an EFX allocation. Both results come from SAT solving.
   - Use here: none directly (not additive). With Mahara's m ≤ n + 3, only m = n + 4 is open for general monotone valuations.
8. **Mackenzie–Suzuki, "Counterexamples to EFX for Submodular and Subadditive Valuations", arXiv:2605.06451v1 (7 May 2026).** Read (abstract).
   - A three-agent, eight-good instance with monotone subadditive valuations in which no allocation is α-EFX for any α > 2^(−1/6) ≈ 0.89; a closely related three-agent, eight-good weighted-coverage (submodular) instance with no EFX allocation. The agents' valuations are identical up to relabeling the goods.
   - Use here: none (not additive).

## Other papers checked (PROMPT.md §5 rule 5)
- **Lianeas–Sgouritsa–Sotiriou, "EFX Allocation In (Multi)Hypergraphs", arXiv:2608.03171v1 (4 Aug 2026).** Read.
  - Theorem 1: instances on hypergraphs of girth at least 4 always have an EFX allocation, for general monotone valuations, constructible in polynomial time. Agents are vertices and goods are hyperedges; only a hyperedge's vertices may have positive marginal value for it. It extends to multi-hypergraphs of girth ≥ 4 on the underlying simple hypergraph, under an extra condition on the edge multiplicities.
  - Use here: in our setting a good valued by k agents is a hyperedge on those k agents. Cores usually contain short cycles; for example two agents that share two goods whose other valuers differ. So the girth condition fails on most cores. It does not imply TARGET or D. Which cores it does cover was not worked out.
- **Wang, "Rival-Injective Allocations: Support-List Structure and Maximum-Anchor EFX₀ Certificates", arXiv:2608.30203v1 (31 Aug 2026).** Read.
  - Defines rival-injective (RI) ownership: each good goes to an agent who values it positively, and each ordered observer–owner pair is used by at most one good. Every RI allocation in which each agent's bundle is worth at least its most valuable single good is EFX₀ (using all goods). Gives sufficient certificates and witness families.
  - It states that EFX₀ remains open for general additive valuations with four or more agents, and that its 4 × 10 family "is not an unrestricted 4 × 10 theorem". It does not imply TARGET or D.
  - Possible proof idea: RI plus "own bundle ≥ best single good" is a sufficient condition in the spirit of L9. Not yet explored.

## Not read (leads only)
- "Almost EFX in Hypergraphs", arXiv 2606.26948; "EFX Allocations on Some Multi-graph Classes", arXiv 2412.06513; "On the existence of EFX allocations in multigraphs", arXiv 2502.09777; "A Simple Polynomial-Time EFX Repair for Cancelable Valuations", arXiv 2608.08864; Afshinmehr–Danaei–Kazemi–Mehlhorn–Rathi, "EFX allocations and orientations on bipartite multi-graphs: A complete picture", *Autonomous Agents and Multi-Agent Systems* 40:32, 2026 (cited by 2608.30203).
- EGRES Quick-Proof 2022-01, "A note on the existence of EFX allocations" (https://egres.elte.hu/qp/egresqp-22-01.pdf).

## Network access from the cloud container (2026-09-24)
- `curl` through the container's egress proxy got HTTP CONNECT 403, "policy denial", for arxiv.org, export.arxiv.org, ar5iv.org, ar5iv.labs.arxiv.org, alphaxiv.org, dblp.org, api.semanticscholar.org, www.semanticscholar.org, api.crossref.org, doi.org, api.openalex.org, pubsonline.informs.org, drops.dagstuhl.de, egres.elte.hu, dl.acm.org, link.springer.com, www.sciencedirect.com, ojs.aaai.org, www.ifaamas.org, www.researchgate.net, scholar.google.com, scholar.archive.org, web.archive.org, core.ac.uk and huggingface.co. Only GitHub was reachable. The WebFetch tool returned "EGRESS_BLOCKED" for arxiv.org, egres.elte.hu, api.semanticscholar.org and api.crossref.org.
- To read more sources: paste the text into a session, or allow these hosts in the environment's network settings.
