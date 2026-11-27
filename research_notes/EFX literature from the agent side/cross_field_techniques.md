# Cross-field techniques for EFX-type existence with few relevant goods per agent

Researched 2026-11-26 for the k = 4 EFX₀ problem (TARGET₄; `k4/sdc.md` conjectures SD-C, OC and OC₁). It complements `proofs/citations.md` and `proofs/novelty.md`, which record the fair-division papers already read and are not repeated here.

**Read levels** (for each item):
- **section**: named pages read from the extracted PDF text.
- **abstract**: the arXiv or publisher abstract page was opened.
- **snippet**: only search-engine result text was seen. Theorems known only at this level are marked [snippet].
- **secondary**: the statement comes from a survey or Wikipedia page that was read, not from the primary paper.
- **[unverified]**: not read in any form this session; recalled background, given only so the sketches can be followed.

Every sketch under "Inferences" is our speculation unless it cites a source.

The setting, in the repository's terms:
- Agents are vertices and goods are hyperedges, and every agent has degree ≤ 4.
- In the dual view, each agent is a set of ≤ 4 goods: a rank-4 hypergraph on the goods whose vertex degree (the number of agents valuing a good) is unbounded.
- The open step (`k4/sdc.md` §2, §4, §29): for a fixed serial-dictatorship order, the picks must extend. The unpicked goods go to "free slots" of other agents, at most one each, and to one absorber, so that no bundle strictly contains another agent's *danger set*. A danger set is two or three of that agent's goods worth more than what it holds.
- A naive count (the deficit) does not decide extendability (`k4/sdc.md`, around line 390).

## Q1. Extremal combinatorics: rainbow cycle number, rainbow matchings, Hall-type theorems for hypergraphs

### Takeaway
- **The rainbow cycle number does not fit the complete-allocation question.** It is already an EFX technique, but it bounds *leftover* goods, through Pareto-improving cycle swaps. That is exactly the value-monotone kind of move the project has refuted at k = 4 (K4.SDC.P1). So it can at best bound how many goods are left over, never complete the allocation.
- **Haxell's hypergraph Hall theorem is the closest fit.** It is already used in fair division, for the restricted Santa Claus / max-min problem. Its quantitative condition is too strong to apply here as stated, but its alternating-tree proof is a natural non-value-monotone search pattern.
- **Topological Hall theorems and Drisko-type rainbow matchings fit the "protect each frozen agent by a distinct placement" subproblem best**, as sufficient conditions with a factor-2 slack.

### Cited Findings
**Rainbow cycle number**
- Definition (CGMMM, [section, pp. 1–13]): R(d) is the largest k such that some k-partite digraph has:
  - parts of size ≤ d;
  - for any two parts V_i and V_j, an incoming edge into every vertex of V_i from some vertex of V_j;
  - no cycle that meets every part at most once.

  Theorem 3 there: R(d) ≤ d⁴ + d. — [Chaudhury–Garg–Mehlhorn–Mehta–Misra, arXiv 2103.01628](https://arxiv.org/abs/2103.01628)
- How it is applied to EFX (CGMMM §4, [section]):
  - The parts are the *unallocated goods* g. Part V_g holds copies of the envy-graph sources assigned to the agents that find g "valuable" (v_a(g) > ε·v_a(X_a)).
  - An edge (g, s(a)) → (h, s(b)) means that agent a is the champion of X_{s(b)} ∪ g.
  - Under assumption (*) (acyclic envy graph; rules U1 and U2 inapplicable), every vertex has an in-edge from every other part (Obs. 13).
  - A cycle meeting each part at most once gives, through rule U3, a (1−ε)-EFX allocation that Pareto-dominates the current one (Lemma 14).
  - So the number of "low-demand" leftover goods (each valuable to ≤ d agents) is at most R(d) (Lemma 15). There are fewer than 2n/(εd) "high-demand" goods, because each agent finds at most 2/ε leftover goods valuable (Obs. 12).
  - The notion is the all-goods one: the champion definition requires (1−ε)·v_ℓ(S∖h) ≤ v_ℓ(X_ℓ) "for all h ∈ S" (p. 7).

  — [CGMMM, arXiv 2103.01628](https://arxiv.org/abs/2103.01628)
- Improved bounds:
  - R_f(d) ≤ d^{2+o(1)}, and 2d − 2 when all labels are permutations; the authors conjecture R_f(d) = d [abstract, via search snippet of the DROPS/arXiv abstract]. — [Berendsohn–Boyadzhiyska–Kozma, MFCS 2022, arXiv 2201.08753](https://arxiv.org/abs/2201.08753)
  - R(d) = O(d log d), which gives (1−ε)-EFX with O_ε(√(n log n)) discarded goods; R(d) ≤ 2d − 4 in the permutation case [abstract, v3 and v4; the abstract prints "Ω(d log d)", apparently a typo for an upper bound]. — [Chashm Jahan–Seddighin–Seyed-Javadi–Sharifi, arXiv 2212.09482](https://arxiv.org/abs/2212.09482v4)
  - The same abstract lists the earlier bounds O(d⁴) (Chaudhury et al.), O(d^{2+o(1)}) (Berendsohn et al.) and O(d²) (Akrami et al.). — [2212.09482](https://arxiv.org/abs/2212.09482v3)
  - The journal version of Akrami–Alon–Chaudhury–Garg–Mehlhorn–Mehta (EC 2023; *Operations Research* 2025) is described as improving the bound to O(d log d) by the probabilistic method, with charity Õ((n/ε)^{1/2}) [snippet]. Its arXiv v2 abstract (2205.07638, "EFX Allocations: Simplifications and Improvements") states the charity improvement but does not mention rainbow cycles [abstract]. **Attribution of O(d log d) is therefore split between two groups.** — [INFORMS record](https://pubsonline.informs.org/doi/fpi/10.1287/opre.2023.0433); [arXiv 2205.07638](https://arxiv.org/abs/2205.07638)
- The same Akrami et al. work moves "in the space of complete allocations, improving a potential as long as the allocation is not EFX", in contrast to earlier update rules over partial EFX allocations [snippet]. — [Princeton record](https://collaborate.princeton.edu/en/publications/efx-a-simpler-approach-and-an-almost-optimal-guarantee-via-rainbo-2/)

**Haxell's condition and the Santa Claus problem**
- Haxell (1995) [secondary]:
  - Setting: a bipartite hypergraph on X ∪ Y whose edges have size ≤ r (one vertex in Y, the rest in X).
  - Condition: for every Y₀ ⊆ Y, the neighbourhood hypergraph has cover number τ ≥ (2r − 3)(|Y₀| − 1) + 1.
  - Conclusion: there is a Y-perfect matching.
  - The constant 2r − 3 is tight, and r = 2 gives Hall's theorem.

  — [Wikipedia, "Hall-type theorems for hypergraphs"](https://en.wikipedia.org/wiki/Hall-type_theorems_for_hypergraphs), citing *Graphs and Combinatorics* 11 (1995) 245–248.
- Aharoni–Haxell (2000) [secondary]: if the matching-width of N_H(Y₀) is at least |Y₀| for every Y₀ ⊆ Y, a Y-perfect matching exists. The proof is topological (Sperner). Meshulam (2001) weakened the condition to "mw ≥ |Y₀| or w ≥ 2|Y₀| − 1". — [Wikipedia](https://en.wikipedia.org/wiki/Hall-type_theorems_for_hypergraphs) (*J. Graph Theory* 35 (2000) 83–88; *Combinatorica* 21 (2001) 89–94).
- Application to max-min fair allocation (restricted Santa Claus):
  - Asadpour–Feige–Saberi, "Santa Claus meets hypergraph matchings" (2008; TALG 2012), reduce it to hypergraph matching and "reinterpreted Haxell's method" as an algorithm [snippet].
  - Annamalai–Kalaitzis–Svensson made a modified Haxell argument run in polynomial time (12.33-approximation) [abstract, as summarized in Davies et al.].
  - Davies–Rothvoss–Zhang build a matroid version on "Haxell's augmenting tree" [abstract].
  - Haxell–Szabó replace the combinatorial argument with topological methods [snippet].

  — [Davies–Rothvoss–Zhang, arXiv 1807.07189](https://arxiv.org/abs/1807.07189); [AFS, DOI](https://dx.doi.org/10.1007/978-3-540-85363-3_2); [Haxell–Szabó record](https://refubium.fu-berlin.de/handle/fub188/47165?show=full)
- Conforti–Cornuéjols–Kapoor–Vušković [secondary]: a balanced hypergraph has a perfect matching iff, for all disjoint vertex sets V₁, V₂ with |V₁| > |V₂|, some edge e has |e ∩ V₁| > |e ∩ V₂|. — [Wikipedia](https://en.wikipedia.org/wiki/Hall-type_theorems_for_hypergraphs)

**Rainbow matchings**
- Drisko's theorem as generalized by Aharoni–Berger: any 2n − 1 matchings of size n in a bipartite graph have a rainbow matching of size n. The Aharoni–Berger conjecture: n colour classes, each of size ≥ n + 1, should suffice in bipartite multigraphs. It implies Ryser–Brualdi–Stein [snippet]. — [Wikipedia, Rainbow matching](https://en.wikipedia.org/wiki/Rainbow_matching); [Keevash–Yepremyan, arXiv 1710.03041](https://arxiv.org/pdf/1710.03041)
- In general graphs, 3n − 2 matchings suffice (Aharoni–Berger–Chudnovsky–Howard–Seymour) [snippet]. — [Aharoni–Berger–Chudnovsky–Zerbib, arXiv 2012.14992](https://www.arxiv.org/pdf/2012.14992v2)

**Envy-free matchings**
- A matching is envy-free when no unmatched X-vertex is adjacent to a matched Y-vertex.
- Results: a sufficient condition for a nonempty envy-free matching, with a polynomial-time algorithm; a unique partition containing all envy-free matchings.
- Applications: proportional cake-cutting, 1-out-of-(2n−2) MMS for goods, 1-out-of-⌊2n/3⌋ MMS for bads.
- Read level: [abstract via search summary; *Information Sciences* 587 (2022) 164–187].

— [Aigner-Horev–Segal-Halevi, arXiv 1901.09527](https://arxiv.org/abs/1901.09527)

### Inferences
**Rainbow cycle with bounded relevant goods (speculation)**
- With k ≤ 4 relevant goods, "valuable" can be read as "relevant", and ε drops out of the CGMMM count: each agent values at most k leftover goods. That gives at most kn/d high-demand goods, and at most R(d) low-demand goods with no rainbow cycle.
- So a Pareto-maximal partial EFX₀ allocation would leave O(min_d(kn/d + R(d))) = O(√(n log n)) goods unallocated. Goods nobody values go to an envy-graph source, as in L3.
- That is a sublinear leftover bound, not completeness. It is consistent with K4.SDC.P1, where a Pareto-maximal partial EFX₀ allocation with one leftover good is stuck.
- Conclusion: the rainbow-cycle machinery is intrinsically value-monotone (rule U3 Pareto-dominates), so it **cannot by itself** prove TARGET₄.
- What may transfer is the *permutation case* (R ≤ 2d − 4 or 2d − 2): it is the right tool when every leftover good has a unique champion. It can then certify that a simultaneous multi-chain trade, each chain using a distinct leftover good, exists once there are more than about 2d leftover goods.

**Haxell's condition: does not fit as stated, but its proof does (speculation)**
- As stated, it fails quantitatively. Model each agent as a Y-vertex whose hyperedges are its acceptable bundles. With k ≤ 4 relevant goods plus junk, r ≈ 5 or 6. The condition then needs τ ≥ 7(|Y₀| − 1) + 1, while |Y₀| agents with ≤ 4 relevant goods each have τ ≤ 4|Y₀|.
- The *alternating (augmenting) tree* proof is the useful part:
  - It keeps a partial matching and grows a tree of "blocking" edges.
  - It swaps hyperedges, so a matched player's bundle can change but the player stays matched.
  - It terminates through a lexicographic signature, not through agents' values.
- That is the non-value-monotone search that P1 says is needed at k = 4. The analogue here:
  - a state is a set of bases (as in §29 of `k4/sdc.md`);
  - "matched" means "has an acceptable base";
  - a blocking edge is a base that some frozen agent's danger set forces to change;
  - the signature is the layered count of blocking bases.

**Drisko / rainbow matching for the protection subproblem (speculation)**
- Build a bipartite multigraph between junk goods and free slots. Colour each edge (g, s) by every frozen agent i for which putting g in slot s breaks all of i's danger sets inside the absorber (a "key good" of i).
- A rainbow matching of size |F| protects every frozen agent of F with a distinct placement.
- Drisko–Aharoni–Berger then gives a sufficient counting condition: if each frozen agent has ≥ 2|F| − 1 disjoint protecting placements, all can be protected simultaneously.
- This is a factor-2-slack sufficient condition, not exact. It ignores the benefit of one placement protecting several agents, which is exactly what `k4/sdc.md` reports when the deficit is positive but the picks still extend ("frozen agents share goods").

**Envy-free matching (speculation)**
- Its "unmatched vertex not adjacent to a matched vertex" condition is the shape of SD-C's Lemma 1: every good an agent prefers to its holding is the favourite of its holder.
- Its unique-partition theorem may describe which agents can be "unwanted" in some extendable SD outcome.

### Gaps
- Not read: the full texts of 2212.09482 and of Akrami et al. (EC 2023), so who first proved O(d log d) is unresolved; the AFS and AKS papers themselves; the Haxell 1995 and Aharoni–Haxell primary texts (statements are from Wikipedia).
- Found no paper applying rainbow cycles, Haxell's theorem or rainbow matchings to *exact* EFX, or to bounded relevant goods.

## Q2. Topological methods (Sperner/KKM, Brouwer, consensus halving and necklace splitting, Meshulam connectivity)

### Takeaway
- Discrete-topological methods prove **EF1-type** results (connected bundles on paths, chores, consensus divisions). They round a fractional envy-free division at *boundary* items, which gives "up to one good" but no control over *which* good. They have not given EFX. The only EFX-directed fixed-point paper (Etesami) is a conditional reformulation, not an existence proof.
- The topological tool that does fit is Meshulam's **topological Hall theorem**, a Hall-type theorem for transversals in a simplicial complex. It suits "choose placements so that the absorber's set avoids every danger set".

### Cited Findings
**Connected bundles and chores**
- Igarashi proves that a connected EF1 division of a path exists for every n with monotone valuations, settling Bilò et al.'s question (they had n ≤ 4). The method:
  - Su's Sperner encoding of path divisions on a triangulated simplex;
  - a multi-labelled Sperner lemma of Meunier–Su (2019);
  - rounding.

  [abstract via search summary] — [Igarashi, AAAI 2023](https://ojs.aaai.org/index.php/AAAI/article/view/25705); [arXiv 2209.01348](https://arxiv.org/pdf/2209.01348)
- Sun–Li prove connected EF1 for discrete chores. They use the Simmons–Su Sperner framework with "virtual disutility" functions, and note that the rounding of Bilò et al. and Igarashi does not transfer to chores directly [abstract; IJCAI-ECAI 2026 full version]. — [Sun–Li, arXiv 2609.32545](https://arxiv.org/abs/2609.32545)
- Mahara: an EF1 and PO (indeed fPO) allocation of chores exists for additive costs, by "a novel combination of a fixed point argument and a discrete algorithm" [abstract]. — [Mahara, arXiv 2507.09544](https://arxiv.org/abs/2507.09544)

**Consensus halving**
- The Simmons–Su Borsuk–Ulam theorem gives consensus halving with ≤ n cuts. For additive utilities there is a polynomial algorithm with ≤ n cuts; with simple monotone utilities the problem is PPAD-hard [abstract, MOR 2022]. — [Goldberg–Hollender–Igarashi–Manurangsi–Suksompong, arXiv 2007.06754](https://arxiv.org/abs/2007.06754)

**Fixed points for EFX**
- Etesami relaxes the EFX constraints by randomized rounding, rewrites the problem as a difference-of-convex program, and links it to a Brouwer fixed point.
- The map fails self-containedness "by an arbitrarily small positive constant", so a perturbed map is used. Its fixed point gives EFX only *if* the original map has one.
- So existence is not proved [abstract]. `proofs/novelty.md` already lists it as irrelevant to TARGET.

— [Etesami, arXiv 2510.04915](https://arxiv.org/abs/2510.04915)

**Meshulam's topological Hall theorem** [secondary]
- Statement: let C be a complex on V, with sets V_y ⊆ V. If η(C[V_{Y₀}]) ≥ |Y₀| for all Y₀, then C contains a transversal of the V_y.
- Meshulam's CON/NON game score Ψ(G) lower-bounds η of a graph's independence complex. That gives a sufficient condition for an independent set meeting each V_y once.

— [Wikipedia](https://en.wikipedia.org/wiki/Hall-type_theorems_for_hypergraphs) (*JCTA* 102 (2003) 321–330)

### Inferences
**Sperner and Brouwer methods: do not fit EFX₀ (speculation)**
- These methods round a fractional EF division by giving each boundary item to one side, so envy is bounded by *one specific* item.
- EFX₀ asks that removing *any* good, including goods worth 0 to the envier, ends the envy. That needs the boundary item to be the envier's least valuable good in the other bundle, which the topology does not control.
- Our goods also carry no linear order. Goods are hyperedges on agents, so the path or simplex encodings have no natural analogue.

**Meshulam's theorem: fits as a sufficient condition (speculation)**
- Let C be the independence complex of the *threat hypergraph* on the junk: the sets the absorber can hold without strictly containing a danger set. This is the object of Lemma H1 in `k4/hall.md` §1.
- Placements must be chosen so that the absorber's residue lies in C. Its connectivity can be bounded through domination or Ψ-type parameters, and bounded degree helps there: each frozen agent contributes at most 3–4 small danger sets.
- This yields an Aharoni–Berger-type "matroid ∩ complex" condition (see Q5).

### Gaps
- Not found: any topological proof of exact EFX or EFX₀, even for special classes.
- Not found: whether connected EFX on paths can fail. Not searched.
- The Meunier–Su multilabelled Sperner lemma was not read.

## Q3. Stability and matching theory (Scarf, kernels, housing markets and TTC, serial dictatorship, popular matchings)

### Takeaway
- **Serial dictatorship and Pareto-optimal matching theory fit directly.** SD outcomes are exactly the Pareto-optimal matchings, which gives a vocabulary for choosing the order. The popular-matching characterization by first and second choices (f-posts, s-posts) is a model for an existence condition stated by a Hall condition on a reduced graph.
- **Scarf's lemma, cores and kernels fit poorly.**
  - EFX₀ is not a blocking-coalition condition.
  - Scarf-type results give fractional or approximately feasible outcomes (k − 1 over-allocation), not exact ones.
  - Multi-unit housing markets with additive preferences can have empty cores (KQW). So TTC-style core arguments do not extend, and EFX₀ must be weak enough to escape that.

### Cited Findings
**Scarf's lemma and approximately feasible outcomes**
- Every hypergraphic preference system has a fractional stable matching (Theorem 2.1, via Scarf's lemma). The paper also gives a fractional Gale–Shapley biorder theorem for arbitrarily many matroids, and fractional kernels [snippet, JCTB 87 (2003) 72–80]. — [Aharoni–Fleiner, EGRES TR-01-15](https://egres.elte.hu/www/tr-01-15.html)
- Finding a Scarf / fractional stable solution in hypergraphs is PPAD-complete [snippet]. — [Kintali et al., "Scarf is PPAD-complete", arXiv 0812.1601](https://arxiv.org/pdf/0812.1601)
- Nguyen–Vohra combine Scarf's lemma with iterative rounding for stable matching with couples ("near feasible") [snippet]. — [Nguyen–Vohra, NBER](https://conference.nber.org/conf_papers/f82351/f82351.pdf)
- Nguyen–Peivandi–Vohra [abstract]:
  - They allocate bundles without transfers.
  - "If agents don't want bundles larger than k", each good is over-allocated by at most k − 1 units ex post.
  - The result rests on a generalized Birkhoff–von Neumann theorem: lotteries over approximately feasible allocations.
  - Envy-freeness appears only as a keyword.

  — [JET 165 (2016) 209–241](https://econpapers.repec.org/RePEc:eee:jetheo:v:165:y:2016:i:c:p:209-241)

**Housing markets and serial dictatorship**
- Konishi–Quint–Wako [abstract via RePEc]:
  - With multiple types of indivisible goods, the core can be empty even with strict, additively separable preferences.
  - With one type and multi-unit consumption, it can be empty even without complementarities.
  - A secondary source reports nonemptiness for three agents [snippet].

  — [J. Math. Econ. 35 (2001) 1–15](https://ideas.repec.org/a/eee/mateco/v35y2001i1p1-15.html)
- Abraham–Cechlárová–Manlove–Mehlhorn [snippet]: Pareto-optimal matchings in house allocation; a "signature" characterization of instances with a unique PO matching; an O(√n·m) TTC-based algorithm for a maximum-cardinality PO matching. — [ISAAC 2004 / LNCS, DOI](https://www.doi.org/10.1007/11602613_115); [MPI PDF](https://testweb-11.mpi-inf.mpg.de/fileadmin/inf/d1/teaching/winter20/Ideen/ParetoMatchings.pdf)
- That every Pareto-efficient matching is a serial-dictatorship outcome for some order is attributed (in the same search results) to Abdulkadiroğlu–Sönmez 1998 [snippet; primary not read]. — [search source](https://www.arxiv.org/pdf/2602.14816)

**Popular matchings** (Abraham–Irving–Kavitha–Mehlhorn, SICOMP 2007) [snippet]
- An f-post is some applicant's first choice. s(a) is a's best post that is not an f-post.
- A matching is popular iff every f-post is matched and each applicant gets f(a) or s(a) (house-allocation form).
- An O(√n·m) algorithm.

— [AIKM journal PDF](https://people.mpi-inf.mpg.de/%7Emehlhorn/ftp/PopularMatchingsJournal.pdf)

**Kernels** [snippet]
- Richardson: a digraph with no odd directed cycle has a kernel.
- Aharoni–Holzman, via Scarf: every clique-acyclic digraph has a strong fractional kernel.
- Boros–Gurvich: perfect graphs are kernel-solvable (if the one-way arcs in every clique are acyclic, a kernel exists).

— [IMR preprint](https://hkumath.hku.hk/~imr/IMRPreprintSeries/2015/IMR2015-6.pdf); [arXiv 0904.1435](https://arxiv.org/pdf/0904.1435)
- Sands–Sauer–Woodrow: every 2-arc-coloured digraph (no monochromatic infinite outward paths) has an independent set S that every vertex reaches by a monochromatic path. It fails for more colours [snippet].
  - Langlois–Meunier generalize SSW and Galeana-Sánchez–Neumann-Lara [abstract].
  - A Rocq formalization exists [snippet].

  — [Langlois–Meunier, arXiv 2502.02482](https://arxiv.org/abs/2502.02482); [Rocq SSW, arXiv 2604.21376](https://arxiv.org/pdf/2604.21376)
- Galvin: every k-edge-colourable bipartite multigraph is k-edge-choosable. The proof orients the line graph so that each clique is transitive and invokes a kernel [snippet]. — [CPC short proof](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/short-proof-of-galvins-theorem-on-the-listchromatic-index-of-a-bipartite-multigraph/3AFBDAFC38FF81E217A2D63E76523B82); [Bondy–Murty notes](https://faculty.etsu.edu/gardnerr/5340/notes-Bondy-Murty-GT/Bondy-Murty-GT-17-5.pdf)

**Matching methods already used for EFX**
- Kobayashi–Mahara–Sakamoto prove EFX for chores when m ≤ 2n, when all but one agent share a cost ordering, and for two cost types [snippet; *TCS* 1026 (2025)]. — [arXiv 2305.04168](https://arxiv.org/abs/2305.04168)

### Inferences
**SD orders and PO matchings (speculation)**
- SD-C's equivalent form ("some EFX₀ allocation extends a Pareto-optimal one-good-per-agent matching", `k4/sdc.md` Lemma 1) puts the choice of order inside house-allocation theory.
- Useful imports:
  - **Local certificates of Pareto-optimality.** ACMM characterize a matching as PO iff it is maximal, trade-in-free and coalition-free [recalled, not confirmed in what was read: unverified]. These would replace "an order π" by a matching with checkable local properties. Then "change the order" becomes "apply a trading cycle (TTC-like) or a trade-in", which is the repository's improving-chain move.
  - **Maximum-cardinality PO matchings** (TTC-based). The candidate is a rule of the form "a PO matching maximizing the number of matched agents with a frozen-safe pick". `k4/sdc.md` §3 shows that the simplest extremal rules fail, so any such rule must be tested against `sdc_rules_screen.log`.

**Popular matchings (speculation)**
- The f/s-post structure is a two-level analogue of the repository's "want" and "pair" arrows.
- AIKM decide existence by an applicant-complete matching in the reduced graph of f- and s-edges, which is a Hall condition.
- An analogous reduced graph, with each agent's pick, its key good and its absorber-compatible goods, might carry an exact Hall condition for "this order extends".

**Scarf (speculation)**
- Encoding EFX₀ needs "no agent i strongly envies X_j". The violation involves a bundle held by someone else, not an alternative hyperedge that a coalition could take. So there is no direct Scarf or kernel encoding.
- Fractional stable solutions plus Nguyen–Vohra-style rounding give at most k − 1 over-allocation, which is infeasible for exact EFX₀. **Does not fit.**

**SSW kernels (speculation)**
- The two arrow types (want and pair) make a 2-arc-coloured digraph on agents. An SSW kernel is an independent set S reached from every agent by a monochromatic path.
- It is conceivable as the set of "chain heads" from which improving chains start. This is only weakly motivated, and the theorem fails for three colours.

**KQW is a warning**
- Any argument that proves EFX₀ by exhibiting a *core-like* (coalition-proof) allocation of multi-unit additive goods would contradict KQW. So the TTC moves must rely on EFX₀'s pairwise structure, not on coalition stability.

### Gaps
- Not read: the full text of ACMM (PO characterization) or Abdulkadiroğlu–Sönmez (PO = SD); AIKM's theorem wording; the primary Galvin, Boros–Gurvich and SSW papers.
- Not found: any application of Scarf's lemma, kernels or popular matchings to EFX.

## Q4. Markets and equilibria (Walrasian equilibrium, CEEI, Fisher markets, Nash welfare)

### Takeaway
- **Price-based and welfare-based arguments give EF1 + PO, not EFX₀.**
  - EFX and PO can be incompatible when there are zero values (Plaut–Roughgarden), and, per a 2026 preprint, even with all-positive values.
  - MNW is EFX only for ≤ 2 distinct values.
  - Equal-income competitive equilibria with indivisible goods may fail to exist.
- So no PO-preserving market argument can prove TARGET₄. Markets could only be used as an *intermediate* fractional object, with forest-structured supports, before a non-PO rounding.

### Cited Findings
**Fisher markets and EF1 + PO**
- Barman–Krishnamurthy–Vaish [abstract]: a pseudo-polynomial algorithm for EF1 + PO, polynomial for bounded values. They construct Fisher markets whose equilibria are fair, using price-envy-freeness up to one good (pEF1). Additive Fisher-market equilibria are fPO, and EF1 + fPO allocations always exist (EC 2018). — [arXiv 1707.04731](https://arxiv.org/abs/1707.04731)
- Barman–Krishnamurthy perturb budgets by a bounded amount to get a "pure" market with an integral equilibrium. That gives strongly polynomial fair (relaxed EF1 or proportionality) and PO allocations [abstract]. — [arXiv 1811.08673](https://arxiv.org/abs/1811.08673)

**Nash welfare and EFX**
- MNW is EFX when goods take at most two values, and not for three or more [snippet, IJCAI 2020]. — [Amanatidis–Birmpas–Filos-Ratsikas–Hollender–Voudouris, arXiv 2001.09838](https://arxiv.org/abs/2001.09838)
- For additive valuations, an EFX allocation of a subset of the items with at least half the maximum Nash welfare exists. The algorithm starts from an MNW allocation and donates items [snippet]. — [Caragiannis–Gravin–Huang, arXiv 1902.04319](https://arxiv.org/abs/1902.04319)
- Zero marginal values are "a common technical obstacle" for EFX combined with welfare or efficiency [snippet]. — [Lim–Neoh–Teh, arXiv 2601.12849](https://arxiv.org/html/2601.12849v1)

**EFX and PO**
- Plaut–Roughgarden: with zero values allowed, PO and EFX can be incompatible (two agents, three goods); under nonzero marginals, PO + EFX exists for two additive agents or identical valuations [snippet]. — [Plaut–Roughgarden PDF](https://www.timroughgarden.org/papers/efx.pdf)
- A 2026 preprint claims a positive-valued additive instance with no PO EFX allocation [snippet; unverified preprint]. — [arXiv 2610.29201](https://arxiv.org/pdf/2610.29201)

**Competitive equilibrium with indivisible goods**
- With indivisible goods a CE can fail even with one good, two agents and equal incomes. Babaioff–Nisan–Talgam-Cohen's CEFAI exists for ≤ 3 items, or 4 items and 2 agents. Segal-Halevi:
  - for 4 goods and 3 agents with additive preferences, CE exists for almost all incomes;
  - for monotone preferences, positive-measure non-existence;
  - CEFAI can fail with 4 items and 4 agents.

  The journal version corrects an AAMAS 2018 error [snippet]. — [Segal-Halevi, arXiv 1705.04212](https://arxiv.org/abs/1705.04212); [AAMAS journal 34 (2020)](https://link.springer.com/article/10.1007/s10458-020-09444-z)
- Sandomirskiy–Segal-Halevi study fair and efficient division that minimizes sharing. A fair (proportional, EF or equitable) allocation with at most n − 1 shared objects exists [snippet]. — [arXiv 1908.01669](https://arxiv.org/abs/1908.01669)

### Inferences
**Why PO-preserving arguments fail here (speculation)**
- PO is a value-monotone global optimum, and K4.SDC.P1 shows that Pareto-maximal *partial* EFX₀ allocations can be uncompletable. Combined with Plaut–Roughgarden's zero-value incompatibility, this closes the door on "EFX₀ + PO" routes at k = 4.

**What a market argument could still do (speculation)**
- Take an equal-income Fisher equilibrium, which is EF and fPO. Its support has at most n − 1 shared goods (Sandomirskiy–Segal-Halevi type), and with ≤ 4 relevant goods it is a forest of agent degree ≤ 4. Use it only to *choose the SD order* or the absorber: the agent with the most slack (spending minus price of its pick), not PO.
- Kelso–Crawford / Gul–Stacchetti equilibria require money transfers, and EFX₀ has none [unverified: not read this session]. **Not a fit.**

**MNW (speculation)**
- At k = 4 with generic values (more than 2 values), MNW is not EFX. It could serve as a tie-break among SD orders, but `k4/sdc.md` §8 reports that extremal-welfare rules fail, so expect failure.

### Gaps
- Not read: Kelso–Crawford, Gul–Stacchetti, Budish (A-CEEI), Caragiannis et al. 2016 (MNW is EF1 + PO), or Babaioff–Nisan–Talgam-Cohen's primary paper.
- Found no EFX existence proof by prices.

## Q5. Combinatorial optimization and matroids: an exact Hall/flow condition for slot placement with protected agents

### Takeaway
- **The one-absorber completion of a fixed order looks, to us, like a *matroid partition (union) problem* whenever the frozen agents' danger domains are pairwise disjoint and no frozen agent is in one specific "heavy-best-unheld" configuration (derivation below).** Matroid union then gives an exact Hall-type condition, a polynomial test, and an infeasibility certificate (a violating set S of junk goods). That is the certificate `k4/sdc.md` §4 item 1 asks for.
- Overlapping danger domains (goods shared by frozen agents) break the matroid structure, which is exactly where the repository's naive deficit fails. There the tools are matroid ∩ simplicial complex (topological Hall) or LP integrality on balanced or TU structure.
- Discrete-convexity (M♮) and dec-min orientation results exist for fair *counts*, not for heterogeneous EFX values.

### Cited Findings
**Matroid and discrete-convexity methods in fair division**
- Benabbou–Chakraborty–Igarashi–Zick: for matroid-rank (binary submodular) valuations, a utilitarian-optimal EF1 allocation exists, and leximin is computable in polynomial time [snippet; TEAC 2021]. — [arXiv 2003.07060](https://arxiv.org/abs/2003.07060)
- EFX may fail to exist with identical valuations under identical uniform-matroid (cardinality) constraints [snippet]. — [arXiv 2010.07280](https://arxiv.org/pdf/2010.07280v4.pdf)
- Frank–Murota: decreasingly minimal elements of M-convex sets (integral base polyhedra) are exactly the minimizers of the sum of squares and form a matroid-like M-convex set. The applications include egalitarian graph and hypergraph orientations and resource allocation, with strongly polynomial algorithms [snippet]. — [Part I, arXiv 1808.07600](https://arxiv.org/abs/1808.07600); [Algorithms and applications, arXiv 2007.09618](https://arxiv.org/abs/2007.09618)

**Conflict-graph constraints**
- Hummel–Hetland: each bundle must be independent in a conflict graph of maximum degree Δ.
  - For n > Δ an equitable colouring exists (Hajnal–Szemerédi, via Kierstead–Kostochka), which equals EF1 for identical values.
  - A 1/Δ-MMS allocation is found in polynomial time.
  - Later: EF1 exists if n ≥ the largest component size.

  [snippet] — [arXiv 2104.06280](https://arxiv.org/abs/2104.06280); [follow-up, arXiv 2607.01059](https://arxiv.org/pdf/2607.01059)
- Conforti et al.'s perfect-matching criterion for balanced hypergraphs [secondary]. — [Wikipedia](https://en.wikipedia.org/wiki/Hall-type_theorems_for_hypergraphs)

**Standard tools needed below** [unverified: textbook theorems, not re-read this session]
- Rado's theorem (independent transversals in a matroid).
- The Edmonds / Nash-Williams matroid union (partition) theorem: E is the union of an independent set of M₁ and one of M₂ iff |S| ≤ r₁(S) + r₂(S) for every S ⊆ E.
- Edmonds' matroid intersection theorem.
- Max-flow min-cut, and Hoffman's and Gale's feasibility theorems.
- Transversal matroids (sets matchable into slots).

### Inferences
**Setting for the derivation** (our derivation, to be checked against the repository's exact danger-set definitions)
- Fix an order π, its picks B, the absorber o, and the junk J.
- Every other agent u has a set of *free slots* (one junk good each, in the one-absorber shape of OC₁). Slot acceptability (g may go to u's slot without making u's bundle strictly contain someone's danger set, or making u envy) is a bipartite graph. So the sets of junk goods matchable into slots form a **transversal matroid M_T**.
- The absorber receives A = J ∖ (placed goods). For each frozen agent i, write D_i for i's relevant goods that could end up with the absorber (inside J ∪ B_o, conditioned on o's base). Danger sets are subsets T ⊆ D_i with v_i(T) > v_i(X_i). By (F1) of `k4/sdc.md` they have at least two goods, and since i holds ≥ 1 good, |D_i| ≤ 3. The absorber must not (strictly) contain any T.

**When is "A contains none of i's danger sets" a matroid on D_i?** Write D_i = {x ≥ y ≥ z} by i's values, with holding value h. The danger family is upward closed, and pairs are ordered xy ≥ xz ≥ yz, so its minimal sets are one of:
1. none (the free matroid);
2. {xyz} only (the uniform matroid U_{2,3});
3. {xy} (a rank-2 matroid in which x and y are parallel);
4. {xy, xz}: the maximal safe sets are {x} and {y, z}, of different sizes, so this is **not a matroid**. It occurs iff v(x) + v(z) > h ≥ v(y) + v(z);
5. {xy, xz, yz} (U_{1,3}).

When |D_i| ≤ 2, the family is always a matroid. At k = 3 every frozen agent has |D_i| ≤ 2 (a top-holder's only danger set is {b, c}, `k4/sdc.md` §2), so **at k = 3 the per-agent constraint is always a matroid**. Case 4 is new at k = 4: an agent holding exactly one good, with three unheld goods, whose best unheld good x is dangerous with anything.

**Exact condition (disjoint D_i, no case-4 agent).**
- The absorber-admissible sets form the direct sum M_abs = ⊕_i M_i ⊕ (free on J ∖ ∪D_i).
- A one-absorber completion exists iff J splits into an M_abs-independent A and an M_T-independent J ∖ A.
- By matroid union, that holds iff for every S ⊆ J:

  Σ_i ( |S ∩ D_i| − r_i(S ∩ D_i) ) ≤ r_T(S).

  - Left side: the number of goods of S that frozen agents force out of the absorber.
  - Right side: the maximum number of goods of S matchable into distinct acceptable free slots (König).
- This is the repository's deficit with three corrections:
  1. a maximum over subsets S (Hall);
  2. matching rank r_T(S) in place of a raw slot count, which captures "unwanted agents need their own slots" and slot acceptability;
  3. per-agent matroid ranks in place of a fixed number of goods kept out.
- Edmonds' algorithm tests the condition in polynomial time and returns a violating S, the infeasibility certificate.

**Overlapping D_i (shared goods)**
- The admissible family is an intersection of several matroids, not a matroid. That explains why the naive deficit errs in the "frozen agents share goods" cases (38 of 690 R1 outcomes extend with deficit > 0, `k4/sdc.md`).
- Routes from there:
  - (a) Branch on the shared goods (each is in ≤ 4 agents' sets only if its valuers are few; good degree is unbounded in general), reducing to the disjoint case.
  - (b) The Aharoni–Berger "intersection of a matroid and a simplicial complex" theorem, applied to M_T* and the threat complex [recalled, not confirmed in what was read: unverified].
  - (c) LP integrality when the frozen-agent incidence structure is balanced or TU (Conforti et al.'s balanced-hypergraph criterion is of this kind).
- Case-4 agents can be handled by a 2-way branch: either x goes to the absorber (then y and z must be placed), or x is placed (then {y, z} is free).

**Practical next step (for the repository)**
- Implement the matroid-union test for OC₁ completions on the screen set.
- Check whether its failures coincide with the non-extendable SD outcomes when the D_i are disjoint and no case-4 agent is present.
- Then study the certificates S on the outcomes that do not extend: the obstruction-to-order step (`k4/sdc.md` §4 item 2).

**Dec-min and M♮ (speculation)**
- These make "how many goods each agent gets" egalitarian. EFX₀ depends on heterogeneous values, which are not M♮-concave in the bundle-assignment sense. Only the counting layer above uses matroids. **Not a fit beyond that.**

### Gaps
- The derivation above was not checked against the repository's code (`k4/sdc/sdclib.py`), and in particular not against:
  - the strictness clause (the absorber's bundle may equal a danger set);
  - whether slots of "unwanted" agents can always be modelled as independent unit slots;
  - frozen agents whose danger sets include the absorber's own pick;
  - frozen agents that themselves receive a junk good in a free slot. Their holding value rises and their danger family shrinks ("An agent's danger sets shrink when it receives goods of its own", `k4/sdc.md` §2), which couples M_T and M_abs. The derivation assumes frozen agents' holdings are fixed, or that this coupling is handled by branching.
- The Aharoni–Berger matroid–complex theorem and the matroid union theorem were not read this session.

## Q6. Computational and logical methods (SAT/SMT/QBF, counterexample-guided synthesis, PLS, potentials)

### Takeaway
- SAT and SMT with certificates is already the leading method for small EFX cases: Akrami et al. (n = 3, m = 7, Lean-verified encoding) and Alkassar–Fouz–Mehlhorn (n = 4, m ≤ 9; both in `proofs/citations.md`). Heule-style DRAT certificates and cube-and-conquer are the proven toolchain for UNSAT claims.
- Two transferable ideas:
  - **Tang–Lin's "inductive lemma + finite base case by SAT"**, which matches a minimal-counterexample or discharging plan for bounded degree;
  - **counterexample-guided synthesis (CEGIS) of the order or chain rule**, a 2QBF "∃ rule ∀ core".
- The PLS results say potential-based local search is the right complexity frame for general valuations. P1 rules out only value-monotone potentials over partial EFX₀ states.

### Cited Findings
**Computer-assisted proofs**
- Tang–Lin: computer-aided proofs of Arrow's and other impossibility theorems. An inductive proof reduces the theorem to a base case (3 alternatives, 2 voters), which a SAT solver checks, and the same scheme gives Sen and Muller–Satterthwaite [snippet, AIJ 2009]. — [Tang–Lin PDF](https://cse.hkust.edu.hk/faculty/flin/papers/arrow_aij.pdf)
- Survey of SAT methods in social choice: an unsatisfiable formula is "the beginnings of an impossibility theorem" [snippet]. — [Geist–Peters chapter](https://www.dominik-peters.de/publications/sat-chapter.pdf)
- Schur number five (S(5) = 160): SAT, a DRAT proof (reported at about 2 PB), and cube-and-conquer with about 10 million cubes [snippet]. — [Heule, arXiv 1711.08076](https://arxiv.org/abs/1711.08076); [project page](https://cs.utexas.edu/~marijn/Schur)
- Keller's conjecture in dimension 7, with symmetry breaking [snippet]. — [Brakensiek–Heule–Mackey–Narváez](https://par.nsf.gov/servlets/purl/10392658)
- Already-read EFX computer proofs:
  - Akrami et al., 2604.18216: SAT, with the encoding's soundness proved in Lean.
  - Alkassar–Fouz–Mehlhorn, 2608.08590: QF_LRA certificates with an independent certifier.

  — [`proofs/citations.md`](../../proofs/citations.md)

**Local search and PLS**
- EFX is PLS-complete for two agents with submodular valuations, even identical ones. A greedy algorithm handles two "weakly well-layered" agents (including gross substitutes). PLS membership follows from Plaut–Roughgarden's leximin++, and hardness goes through local optima on Kneser graphs [snippet, SAGT 2023]. — [Goldberg–Høgh–Hollender, arXiv 2301.10354](https://arxiv.org/abs/2301.10354)
- Already in the repository: a simulated-annealing local search for EFX, and a potential for identical valuations. — [Brânzei 2510.05429, in `proofs/novelty.md`](../../proofs/novelty.md)

### Inferences
**Tang–Lin style plan (speculation)**
- Prove an inductive lemma: every minimal counterexample to TARGET₄ is a core (K4.CORE) with no reducible local configuration. The repository has `proofs/min_counterexample.md` and the peeling rules R1, R2 and L3.
- Then reduce the remaining configurations to a finite set, checked by SAT with DRAT or LRAT certificates.
- The missing piece is an **unavoidability** lemma (see Q7, discharging).

**CEGIS for the order rule (speculation)**
- Search over rules ρ (decision trees over local features: R1-priority, neediest-first, deficits, matroid-union slack from Q5) for "∀ profile of the n ≤ 5 cores, SD(ρ(profile)) extends".
- Alternate a synthesizer (SAT over rule parameters) with a verifier (the existing `sdsat.py` and `sdclib.py`), adding each counterexample profile.
- This systematizes the repository's manual "rule fails on instance X" loop (`k4/sdc.md` §8–§24).
- Rules that survive on all n ≤ 5 cores are candidates to prove by hand.

**Potentials (speculation)**
- P1 forbids potentials that never lower an agent's value over *partial EFX₀ allocations*. It does not forbid:
  - potentials over pre-allocations or bases (LB⁺ at k = 3 is of this kind);
  - lexicographic signatures as in Haxell's alternating trees (Q1);
  - potentials over *complete* allocations (Akrami et al.'s "simpler approach", Q1).
- These are the three families still open.

### Gaps
- Found no QBF/CEGIS application to fair-division existence.
- Found no PLS result for additive EFX with n ≥ 3. Not searched specifically.

## Q7. Graph theory (orientations with degree constraints, list colouring and kernels, independent transversals, discharging, bounded-degree probabilistic tools)

### Takeaway
- **Bounded-degree combinatorics fits the protection subproblem.**
  - Haxell's independent-transversal theorem: parts of size ≥ 2Δ suffice, and this is tight.
  - Equitable colouring is already used for conflict-constrained EF1.
- **Orientation theory fits only p ≤ 2 (multigraphs).** EFX₀ orientations can fail to exist and are NP-hard to decide (CFKS, in the repository).
- **Discharging fits as a *proof architecture*:** reducible configurations (the repository's peeling) plus an unavoidable set. It has no fair-division precedent.
- **The Lovász Local Lemma and discrepancy need slack** that EFX₀ at k = 4 does not have, so they do not fit.

### Cited Findings
**Independent transversals**
- Haxell: a graph of maximum degree Δ with a vertex partition into parts of size ≥ 2Δ has an independent transversal. This confirmed a Bollobás–Erdős–Szemerédi conjecture and improved Alon's 2eΔ; parts of size 2Δ − 1 do not suffice [snippet, from the abstracts of later papers].
- Partial-transversal and reconfiguration extensions: with 2Δ + 1, independent transversals are connected under single-vertex moves; this fails at 2Δ (disjoint K_{Δ,Δ}) [abstract-level snippets].

— [Haxell–Mittal–Zhao, arXiv 2506.09515](https://arxiv.org/abs/2506.09515); [reconfiguration, arXiv 2407.04367](https://arxiv.org/abs/2407.04367)

**Equitable colouring for conflict-constrained allocation**
- Hummel–Hetland use equitable colouring for n > Δ (see Q5). — [arXiv 2104.06280](https://arxiv.org/abs/2104.06280)

**Orientations**
- Orientation results for p ≤ 2, as already read in the repository:
  - EFX₀ orientations need not exist, and deciding them is NP-complete (CFKS).
  - Zeng–Mehta: "strongly EFX orientable" graphs (orientable for all values), via chromatic number.

  — [`proofs/citations.md`](../../proofs/citations.md), [`proofs/novelty.md`](../../proofs/novelty.md)
- Frank–Murota cover egalitarian (dec-min) hypergraph orientations (see Q5). — [arXiv 2007.09618](https://arxiv.org/abs/2007.09618)

**Discrepancy**
- Manurangsi–Suksompong: envy-freeness up to c goods for groups. For two groups, c = Θ(√n), via discrepancy theory (IJCAI 2021) [snippet]. — [arXiv 2105.01609](https://arxiv.org/abs/2105.01609); [IJCAI](https://www.ijcai.org/proceedings/2021/47)

**Lovász Local Lemma**
- The constructive LLL of Haeupler–Saha–Srinivasan is tied to the Santa Claus problem [snippet]. No LLL-based envy-free existence proof for indivisible goods was found. Probabilistic existence results (Dickerson et al.; Manurangsi–Suksompong) need m ≥ 2n or similar [snippet]. — [arXiv 1001.1231](https://arxiv.org/abs/1001.1231); [Manurangsi–Suksompong, "When do envy-free allocations exist?"](https://arxiv.org/pdf/1811.01630)

### Inferences
**Independent transversals for the protection step (speculation)**
- `k4/sdc.md` reports that for 63 of 63 (and 297 of 298) hard exposed agents, *one good meets every danger set*. So each exposed agent i has a small key set K_i, and the task is to pick one key good per agent and route it to a slot.
- In the *conflict-graph* form: vertices are (good, slot) placements, a part is the set of i's placements, and two placements conflict if they share a slot or a good. Each placement conflicts with at most (deg of the slot) + (deg of the good) others. Haxell then gives a selection whenever each agent has ≥ 2Δ placement options.
- That is a clean sufficient condition. The exact version is the Q5 matroid condition.

**Discharging (speculation)**
- The four-colour template is:
  1. a minimal counterexample contains no reducible configuration;
  2. charge counting shows every admissible structure contains one.
- The repository already has step 1 in large part: peeling R1, R2 and L3, K4.CORE, components (L6) and the counting L4/L7.
- A discharging step would put initial charges on goods (for example deg(g) − 2) and on agents. It would use the double count Σ_g deg(g) = Σ_i |R_i|, the identity behind L4's m ≤ 2n₃ + 3n₄. Redistribution rules would then show that a core with no reducible configuration has impossible total charge.
- This is useful only once a catalogue of reducible configurations at k = 4 exists, for example "an agent whose 4 goods include a private pair" or "a good valued by exactly 2 agents adjacent to a 3-good agent".

**LLL and discrepancy: do not fit (speculation)**
- The LLL needs each bad event (agent i unsafe) to have probability ≤ 1/(e(D+1)), with D bounded. Here the good degree is unbounded, so D is unbounded, and a random SD order makes a given agent unsafe with constant probability.
- Discrepancy rounding errors of ±1 good are exactly what EFX₀ cannot absorb.

**Galvin and kernels: weak fit (speculation)**
- The kernel method proves *choosability*: lists are given, and a kernel in an orientation built from a colouring selects compatible choices.
- The structural analogue would be "every agent has a list (its acceptable bases); orient conflicts by the SD order; a kernel is a compatible choice". But EFX₀ conflicts are not pairwise conflicts between list elements: danger sets involve three bundles (the holder, the absorber, the envier). We do not see a direct encoding.

### Gaps
- Not read: the Haxell 2001 primary paper; Bilò et al.; Hajnal–Szemerédi; any discharging paper.
- Found no fair-division paper using discharging or the kernel method.

## Q8. Which techniques best fit the open k = 4 step (ranking for the project)

### Takeaway
The ranking below is our judgement, based on the cited structure. Ranked by fit to "fixed SD order → one-absorber completion with protected frozen agents", then "choose the order":

| Rank | Technique | Fit |
|---|---|---|
| 1 | Matroid union / intersection, Rado | an exact Hall condition plus a certificate, when the frozen agents' danger domains are disjoint and no case-4 agent is present (Q5) |
| 2 | Topological Hall (Meshulam), matroid ∩ complex | the overlapping case, as a sufficient condition (Q2, Q5) |
| 3 | Haxell alternating trees | a non-value-monotone search pattern that escapes P1 (Q1) |
| 4 | Independent transversals (2Δ), Drisko rainbow matchings | sufficient protection conditions with factor-2 slack (Q1, Q7) |
| 5 | House-allocation PO theory, popular-matching f/s-posts | a language and Hall conditions for choosing the order (Q3) |
| 6 | Tang–Lin induction plus SAT, CEGIS, discharging | proof architecture (Q6, Q7) |

Poor fits:
- rainbow cycle number (value-monotone, bounds leftovers only);
- Sperner, Brouwer and consensus halving (EF1-type boundary rounding);
- Scarf and Nguyen–Vohra (fractional, or k − 1 over-allocation);
- markets and MNW (PO is incompatible with EFX₀);
- the LLL and discrepancy (no slack);
- M♮ and dec-min (counts only).

### Cited Findings
- P1 refutation, SD-C, OC and OC₁, danger sets, and the failure of the naive deficit (overlapping goods; unwanted agents' own slots). — [`k4/sdc.md`](../../k4/sdc.md)
- The owner-validity covering form (Lemma H1: a threat hypergraph, and an independent set X ⊇ B_o with enough goods) and the big-top frozen obstruction. — [`k4/hall.md`](../../k4/hall.md)
- The rainbow-cycle method's Pareto-dominating update U3. — [CGMMM, arXiv 2103.01628](https://arxiv.org/abs/2103.01628)
- Haxell's augmenting tree in Santa Claus. — [Davies–Rothvoss–Zhang, arXiv 1807.07189](https://arxiv.org/abs/1807.07189)
- EFX and PO incompatible with zeros. — [Plaut–Roughgarden](https://www.timroughgarden.org/papers/efx.pdf)

### Inferences
**Concrete next experiment (speculation)**
- Implement the Q5 test. Per frozen agent, compute the matroid M_i of absorber-safe subsets of D_i, flagging case-4 agents. Build the slot transversal matroid M_T, and decide matroid union for each OC₁ instance on the screen set.
- Expected outcome if the derivation is right:
  - exact agreement with SAT on outcomes with disjoint D_i and no case-4 agent;
  - disagreements only where frozen agents share goods or a case-4 agent appears. That would localize the k = 4 difficulty to those two phenomena.
- The violating sets S are then the obstruction objects for "obstruction → better order".

**Concrete proof architecture (speculation)**
1. For a fixed order, the completion exists iff the matroid-union condition holds (plus the overlap and case-4 refinements).
2. When it fails, the tight set S names a frozen agent whose freezing is too costly. Re-insert that agent earlier in the order (the LB⁺ need-chain analogue).
3. Termination by a Haxell-style lexicographic signature over the sequence of tight sets, rather than by agents' values.

### Gaps
- Whether the matroid formulation is exact for the repository's danger-set definition is unverified and must be checked in code first.
- Whether overlapping danger domains can be reduced to the disjoint case by branching (each shared good is valued by several frozen agents, but frozen agents per good are unbounded) is unknown.
- No literature found applies any of these cross-field tools to *exact* EFX or EFX₀ with bounded relevant goods. The application sketches are all ours.
