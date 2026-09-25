# (p, q)-bounded instances: what is known and how it relates to this project

Workstream `proof/lit-pq`, 2026-09-25. It answers the coordinator's question: what do the "(p, q)-bounded" papers prove, and how does that relate to TARGET (k = 3), conjecture D, T3/T5, K4.MC7 and the k = 4 route? Queries: `results/lit_search_log.md` §7. Every paper cited is recorded in `proofs/citations.md`. No ledger status is changed.

Read levels, as in `proofs/novelty.md`: **full**, **section** (named pages or sections), **abstract**, **earlier** (read in full in an earlier session, recorded in `proofs/citations.md`). Anything else is marked [unverified].

## 1. The three parameters

Let B(I) be the bipartite *incidence graph* of an instance: agents on one side, goods on the other, and an edge i–g whenever v_i(g) > 0 (g is *relevant* to i).
- **k** (this project): the largest agent degree in B(I), i.e. every agent positively values at most k goods.
- **p** (Christodoulou–Fiat–Koutsoupias–Sgouritsa, "CFKS", §6, p. 15; formal definition in Kaviani et al. 2407.05139, Def. 2.2, p. 3): the largest good degree in B(I), i.e. every good is relevant to at most p agents.
- **q** (same sources): the largest number of common neighbours of two agents in B(I), i.e. two agents share at most q relevant goods.

So k and p are the degree bounds of the two sides of the same bipartite graph, and q is a codegree bound on the agent side. This is what `proofs/novelty.md` meant by "the dual of our bound". The precise relations:
1. **k-bounded ⇒ (∞, k)-bounded.** Two agents share at most min(|R_i|, |R_j|) ≤ k goods. So TARGET's class (k ≤ 3) lies inside the (∞, 3)-bounded instances, and TARGET₄'s class (k ≤ 4) inside the (∞, 4)-bounded ones.
2. **(p, q)-bounds do not bound k.** Take a star: one agent shares one good with each of many others. It is (2, 1)-bounded and its centre has unbounded degree. The two families are incomparable, and the interesting classes are intersections. (2, ∞) ∩ {k ≤ d} is the multigraphs of maximum degree d (private goods as pendant edges); (∞, 1) ∩ {k ≤ d} is the linear hypergraphs of agent degree ≤ d.
3. **Hypergraph language.** The papers below put agents at vertices and goods on (hyper)edges, so a good valued by p agents is a hyperedge of size p. There:
   - q = 1 is "girth at least 3". Kakatelis et al. 2606.26948 (earlier) say girth ≥ 3 means "any two agents share at most one good/edge" (p. 2); Lianeas et al. 2608.03171 (earlier) say the same.
   - Lianeas et al.'s "girth at least 4" is a strict subclass of (∞, 1) that also excludes Berge 3-cycles.
   - Kakatelis et al.'s "multiplicity 2" allows one agent set to share up to two goods, on a girth-≥ 3 underlying hypergraph.
4. **The notion is EFX₀ throughout.** Every paper below defines EFX with the removed good ranging over all of X_j, including goods worth 0 to the envier:
   - CFKS p. 3;
   - 2407.05139 p. 2 ("every X′_j ⊂ X_j") and p. 3 (strong envy "if there exists a good g ∈ X_j");
   - 2506.09288 p. 2 ("for every good g ∈ X_j");
   - Sgouritsa–Sotiriou 2502.09777 p. 5;
   - Amanatidis–Filos-Ratsikas–Sgouritsa 2406.12413 Def. 2.6 (α-EFX "for any good g ∈ X_j").

   Sgouritsa–Sotiriou's Remark 1 (p. 3) makes the point sharply. Under ordinary EFX, where only positively valued goods may be removed, multigraphs are trivial: cut-and-choose on each pair's common goods gives an EFX orientation. The whole difficulty is EFX₀. This is the same gap that separates Viswanathan–Mehta (ordinary EFX, ≤ 4 goods) from TARGET.

## 2. The papers

### 2.1 Kaviani, Seddighin, Shahrezaei, "Almost Envy-free Allocation of Indivisible Goods: A Tale of Two Valuations", arXiv 2407.05139v2 (9 Dec 2024; WINE 2024 as cited in 2506.09288, p. 17). Read in full (32 pp.)
- **Model.**
  - Valuations: monotone (Def. 2.2, p. 3), with an added assumption that they are *strictly* monotone on relevant goods.
  - Also *restricted additive* valuations: v_i(g) ∈ {0, v_g} (Def. 2.1).
  - Allocations: partial allocations carry a pool X₀; "complete" means X₀ = ∅.
  - Notion: EFX₀, with (1/β)-EFX for approximations (p. 3).
- **Results.** The overview is Table 1, p. 9.

  | Theorem | Setting | Guarantee |
  |---|---|---|
  | 5.6 (p. 14) | (∞, 1)-bounded, monotone | partial EFX₀ allocation discarding at most ⌊n/2⌋ − 1 goods |
  | 5.7 (p. 14) | (∞, 1)-bounded, monotone | complete EF2X allocation (algorithm CXXRA) |
  | 6.1 (p. 16) | restricted additive | complete √2/2-EFX |
  | 7.1 (p. 20) | (∞, 1)-bounded, subadditive | complete √2/2-EFX |
  | 8.1 (p. 27) | restricted additive and (2, ∞)-bounded | complete **exact** EFX₀ (algorithm PQRAX) |

  They mark (2, ∞) monotone and (∞, ∞) monotone as open (Table 1). Termination is shown by potentials; no running time is claimed.
- **Techniques.**
  - *Basic feasible allocation* (p. 4): one good per agent, maximizing Nash welfare. Lemma 2.5 (p. 4) uses Hall's theorem to remove a constrained set of agents that have fewer relevant goods than agents, and recurses.
  - *Weighted envy graph*, with edge weights v_i(X_j)/v_i(X_i) (Def. 2.3).
  - *Rank*, from Farhadi et al. [unverified]: the maximum weight product over paths ending at the agent. It is well defined when LP (1) is feasible (Lemmas 2.8–2.9); for restricted additive valuations, whenever every bundle holds only relevant goods (Lemma 2.10).
  - *Rankpath*, *root* and *virtual value* v_i(X_i)/R_i(X) (Defs. 2.6–2.7).
  - *Update rules with a potential* (the framework of §2.1):
    - Pareto-type rules with φ = (social welfare, number of allocated goods), with envy-cycle resolution, a "most envious agent" (minimal envied subset) and a cycle through sources (§5, Rules 1–4);
    - an envy-elimination rule (§6);
    - the key rule of §7: give a minimal virtually-envied subset of the pool to the agent i with the largest ratio, *shift the bundles along i's rankpath*, and return the first bundle of the path to the pool. Lemmas 7.1–7.6 show that virtual values never decrease, no agent virtually strongly envies another, every bundle stays junk-free, and Nash welfare strictly increases.
  - The paper stresses (p. 10) that this rule may *lower* actual utilities while still guaranteeing termination. It suggests such non-monotone updates may be needed in general.
  - Theorem 8.1 adds rules that finalize agents one at a time. It uses the p = 2, restricted-additive structure: every vertex of G₀ has in-degree ≤ 1 (Lemma 8.6).

### 2.2 Kaviani, Keshavarz, Seddighin, Shahrezaei, "Improved Approximate EFX Guarantees for Multigraphs", arXiv 2506.09288v2 (18 Jul 2025). Read in full (18 pp.)
- **Model.** Additive goods (p. 3), notion EFX₀ (p. 2). Page 3 says "we focus on the special case where p = 2 and q = 1", but the abstract, introduction and every result are for (2, ∞). We read this as a typo.
- **Result.** Theorem 4.9 (p. 15): every additive (2, ∞)-bounded instance has a complete (1/√2)-EFX allocation. This improves the 2/3 of Amanatidis et al. (§2.4).
- **Techniques.**
  - Start from the basic feasible allocation of 2.1. Maintain five invariants (p. 4), among them "each remaining agent's bundle is relevant only to it and one other agent" (property (v)), so G₀ has in-degree ≤ 1 and splits into disjoint cycles (Lemma 4.3).
  - Rules 1–5 (pp. 8–15) finalize agents. Two-cycles are closed with Mahara's two-valuation theorem: as restated in Theorem 4.4 (p. 10), a partial EFX allocation for agents with at most two distinct valuations extends to all goods without lowering anyone's utility (Mahara, *Discrete Appl. Math.* 340 (2023); arXiv 2008.08798, abstract read).
  - Heavy cycles (all weights > 1/√2) are rotated at a loss of at most √2; heterogeneous cycles are cut.
  - The final step gives the pool to the last finalized agent.
  - Termination only; no running-time claim.

### 2.3 Christodoulou, Fiat, Koutsoupias, Sgouritsa, "EFX Allocations on Graphs" (EC 2023; author PDF of 15 Mar 2025). Read in full (17 pp.; earlier only pp. 1–4)
- **Model.** Simple graphs, i.e. (2, 1): agents are vertices and each good is an edge relevant only to its endpoints. General monotone valuations; EFX₀ (p. 3).
- **Results.**
  - Theorem 2 (p. 4): deciding whether an EFX orientation exists is NP-complete, even for symmetric instances. Example 1 (p. 4) has no EFX orientation on 4 agents, so EFX₀ may force a good onto an agent who values it 0.
  - **Theorem 3 (p. 6): every graph has a complete EFX₀ allocation, found in polynomial time.**
  - Proposition 14 (pp. 13–14): with multiplicity, three additive agents may have no EFX orientation. Proposition 15 (p. 14): three agents with multiplicity ≤ 2 have an EFX orientation.
  - §6 (p. 15) introduces the generalization to p (hyperedges) and q (multiplicity) and leaves it open. Footnote 3 notes the later progress by Kaviani et al. and Amanatidis et al.
- **Techniques.**
  - Algorithm 1 (p. 7): a greedy chain. An agent takes its best adjacent edge, then the other endpoint of that edge picks, and so on.
  - Algorithm 2 (p. 8), "reducing envy": an envied vertex i takes its unallocated adjacent edges and releases its edge to the vertex that envied it; that vertex releases its own edge, and so on along a chain until a non-envied vertex is reached.
  - Safe sets S_i(X) (§4.1).
  - Lemma 13 (p. 13): the remaining edges are *parked* at non-envied vertices or at a vertex in the intersection of the endpoints' safe sets.

### 2.4 Amanatidis, Filos-Ratsikas, Sgouritsa, "Pushing the Frontier on Approximate EFX Allocations", arXiv 2406.12413v3 (29 Jul 2026; conference version EC 2024). Read: section (abstract, §1–1.2.1 pp. 1–5, §2 definitions pp. 6–7, §4.2 pp. 20–21)
- **Model.** Additive valuations; α-EFX in the all-goods form (Def. 2.6). "Multigraph value instances" (Def. 2.4) are the additive (2, ∞) instances.
- **Results.** Complete 2/3-EFX in polynomial time for:
  - multigraph value instances (Theorem 4.4, p. 20);
  - n ≤ 7 agents (Theorem 4.6);
  - 3-value instances (Theorem 5.1).
- **Technique.** The 3PA algorithm, built on critical goods (worth more than half of one's bundle, Def. 2.7). On multigraphs, the goods critical for two agents are given to a source of the enhanced envy graph, and then Envy Cycle Elimination finishes.
- **§1.2.1 (p. 5)** is a useful map of what followed:
  - Kaviani et al. 2025 improved the multigraph bound to 1/√2; Kaviani et al. 2024 gave exact EFX for restricted additive valuations.
  - "Afshinmehr et al. [2026] and Christodoulou et al. [2026] independently showed the existence of (exact) EFX allocations on multigraphs for additive and cancelable valuations, respectively." The second paper is presumably the EC 2026 paper "EFX allocations on multigraphs" (Christodoulou, Mastrakouis, Sgouritsa, Sotiriou), which we have not read [unverified]. The sentence pairs "additive" with Afshinmehr et al., but 2606.18665 itself states cancelable valuations (`proofs/citations.md` item 4).
  - Kakatelis et al. recover 1/√2 on girth-≥ 3 hypergraphs and prove 2/3 with multiplicity 2.

### 2.5 Sgouritsa, Sotiriou, "On the existence of EFX allocations in multigraphs", arXiv 2502.09777v1 (13 Feb 2025). Read in full (23 pp. and references)
- **Model.** Multigraphs, i.e. (2, ∞) (their §1.3, p. 4, compares CFKS's and Kaviani et al.'s notations). General monotone valuations; EFX₀ (p. 5).
- **Results** (p. 3). A complete EFX₀ allocation exists when:
  - the multigraph is bipartite (Theorem 1);
  - every agent has at most ⌈n/4⌉ − 1 neighbours (Theorem 2; ⌊n/4⌋ when at most two parallel edges);
  - the shortest cycle of non-parallel edges has length ≥ 6 (Theorem 3).

  Termination is pseudo-polynomial (p. 10).
- **Techniques: three steps.**
  1. An initial EFX orientation with few or well-placed envied vertices. For Theorem 2 this is a maximum-weight matching between agents and their first- or second-choice bundles, which leaves at most ⌊n/2⌋ envied agents (Lemma 3.7).
  2. "Reducing envy" (Algorithms 4 and 8), a generalization of CFKS Algorithm 2. Each round makes one envied vertex non-envied, and no non-envied vertex becomes envied.
  3. Every unallocated bundle is *parked* at a non-envied vertex that is not an endpoint (Algorithms 5 and 9). The graph conditions exist to guarantee enough parking spots: Claim 3.13 counts non-envied non-neighbours.

  For many parallel edges it uses EFX-cuts (cut-and-choose) and a 3-partition when two agents have no common cut (Lemma 4.6).

### 2.6 Other bounded-regime existence results
- **p = 2, exact.**
  - Afshinmehr et al. 2606.18665 (EC 2026; earlier, full): exact EFX₀ on all multigraphs, cancelable valuations. This is the theorem behind T3 and K4.MC7, and it subsumes 2.1's Theorem 8.1, 2.2 and 2.4 for additive valuations.
  - Christodoulou–Mastrakouis–Sgouritsa–Sotiriou (EC 2026) [unverified]: by 2406.12413's §1.2.1, an independent proof of the same.
  - Abstract only: Bhaskar–Pandit 2412.06513 (bipartite multigraphs and more, cancelable); Afshinmehr–Danaei–Kazemi–Mehlhorn–Rathi 2410.17002 (bipartite multigraphs, monotone; journal version *AAMAS* 40:32, 2026, as cited by 2608.30203) [journal not read]; Afshinmehr–Ashuri–Mahmoudkhan–Mehlhorn 2512.21644 (triangle-free multigraphs, monotone).
- **q = 1 (girth ≥ 3), p unbounded.**
  - Lianeas–Sgouritsa–Sotiriou 2608.03171 (earlier, full): exact EFX₀ on hypergraphs of girth ≥ 4, monotone valuations, polynomial time (Theorem 1, p. 2). Theorem 2 (p. 3) adds multi-hypergraphs of girth ≥ 4 with a multiplicity condition at one vertex.
  - Kakatelis–Lianeas–Sgouritsa–Sotiriou 2606.26948 (earlier, full): on girth ≥ 3, EF2X for monotone valuations (Theorem 1, p. 7; a simpler, polynomial-time proof of 2.1's Theorem 5.7) and √2/2-EFX for subadditive valuations (Theorem 3, p. 16; reproves 2.1's Theorem 7.1). With multiplicity ≤ 2 (so q ≤ 2): EF3X for additive valuations (Theorem 2, p. 7) and 2/3-EFX for additive valuations (Theorem 4, p. 17).
- **Restricted additive, (∞, ∞).** Akrami–Rezvan–Seddighin 2202.13676 (abstract): complete EF2X, and EFX discarding at most ⌊n/2⌋ − 1 goods. It is the "symmetric" counterpart of 2.1's (∞, 1) results.

### 2.7 The landscape

Exact complete EFX₀, additive or wider valuations:

| | q = 1 | q = 2 | q = ∞ |
|---|---|---|---|
| p = 2 | yes (CFKS) | yes | yes (2606.18665, EC 2026; restricted additive: 2407.05139 Thm 8.1) |
| p ≥ 3 | only with girth ≥ 4 (2608.03171); otherwise EF2X, partial EFX, √2/2-EFX (2407.05139, 2606.26948) | multiplicity-2 hypergraphs: EF3X, 2/3-EFX (2606.26948) | open (general additive EFX) |

**Nothing exact is known for p ≥ 3 except girth ≥ 4.** That is exactly where this project's k-bound adds something (§3.1).

## 3. Relation to this project

### 3.1 Implications, overlaps, contradictions
- **TARGET and D (k = 3): not implied.**
  - Exact results need p ≤ 2 or girth ≥ 4. TARGET cores have goods with three or more valuers and short Berge cycles. Take the showcase core of `proofs/novelty.md` §1: good 0 has three valuers (p = 3), and agents 0 and 1 share goods 0 and 1 (q = 2, so it is not even (∞, 1)).
  - For q = 1 and p ≥ 3 only EF2X, partial or approximate results exist.
  - Nothing is said about the shape of the allocation, so D has no counterpart.
- **Overlap with T3/T5.**
  - T3's multigraph part (cores with every good of degree ≤ 2) is the (2, ∞) cell. 2606.18665 covers it, as T3 says. The (p, q) papers of §2.1–2.2 give only restricted-additive or approximate versions there and add nothing.
  - CFKS (refereed) independently covers a k = 3 core whose shared goods form a *simple* graph (q = 1), provided its private goods can be placed on distinct non-adjacent pairs (an edge to a non-neighbour that values it 0). That fails, for example, in a triangle.
  - 2608.03171 covers the k = 3 instances of girth ≥ 4, existence only (already noted in `proofs/citations.md`).
  - T5 extends the multigraph theorem to goods with three or more valuers under a popular-matching condition. No (p, q) paper has an exact result with p ≥ 3 and q ≥ 2, so T5's class is not covered by them.
- **What TARGET adds to the (p, q) picture.**
  - Read in (p, q) terms, TARGET is **exact EFX₀ for every additive instance with agent degree ≤ 3, for every p and q**.
  - On (∞, 1)-bounded additive instances with at most 3 relevant goods per agent, it upgrades 2.1's EF2X (Thm 5.7), partial EFX (Thm 5.6) and √2/2-EFX (Thm 7.1) to exact complete EFX₀. Their theorems hold for monotone or subadditive valuations; ours is for additive.
  - It gives the first exact results with p ≥ 3 and q ≥ 2 on that degree class.
- **Contradictions: none.** The only non-existence results in these papers are about orientations (CFKS Example 1 and Prop. 14; Sgouritsa–Sotiriou §1.3 cites more). They are consistent with our junk placement: EFX₀ needs goods placed with agents who value them 0 (L3).
- **K4.MC7.** It uses the multigraph theorem for 6 graphical all-P4 cores (n = 6, m = 15, `k4/MINCEX.md` §8). We checked their structure, from the lists in `k4/MINCEX.md` §8:
  - cores 4 (prism) and 5 (K₃,₃) are simple, so CFKS's Theorem 3 covers them. Each private good becomes an edge on a distinct complement edge; the complement is 2-regular, so orient each cycle.
  - cores 2, 5 and 6 are bipartite, so the bipartite-multigraph theorems cover them (Sgouritsa–Sotiriou Thm 1, read in full; Afshinmehr et al. 2410.17002, abstract). Each private good becomes an extra edge parallel to an existing edge of its agent, so neither the bipartition nor the underlying simple graph changes. Core 2's underlying simple graph has girth 6, so Sgouritsa–Sotiriou Thm 3 covers it too.
  - cores 1 and 3 contain triangles and parallel pairs and are not bipartite, so they still need the general multigraph theorem (2606.18665, or the unread EC 2026 paper).

  So the external dependency of K4.MC7 can be narrowed to 2 of the 6 cores; for the other four, an older and independent (partly refereed) theorem suffices. This is an observation for the k = 4 workstream, not a ledger change. The structural check is in the log (§7).
- **Instances with ≤ 4 goods per agent.** They are covered exactly in two cases: when p ≤ 2 (any k; the multigraph theorem, as K4.MC7 uses) and when the hypergraph has girth ≥ 4 (any k; 2608.03171). For q = 1 in general only EF2X/partial/approximate results are known. None of these is conditional on k.

### 3.2 Techniques for the open k = 4 step
`k4/c4.md` §7 (PR #33) shows that a proof of K4.D along LB₄ʳ's lines needs either a choice of the insertion sequence, or an unbounded sequence of rotations with a potential that guarantees termination and progress. The obvious potential has dead ends (`attempts/k4-c4-pareto-moves.md`, on PR #33's branch), and the level-sum maxima can be dead ends (K4.GM.*). The (p, q) papers bear on both routes. None of what follows is tested.
1. **Unbounded path rotations with a cardinal potential (2.1, §7).** The rankpath shift is a rotation along a path: every agent on the path takes its successor's bundle, the end agent takes a pool subset, and the first bundle returns to the pool. That is the shape of an LB₄ʳ need-chain rotation whose end releases its base to the junk. In 2.1 it can be repeated without bound. Nash welfare strictly increases (Lemma 7.6) while virtual values never decrease and the state stays "virtually EFX₀" and junk-free (Lemmas 7.3–7.5).
   - Caveats. In (∞, 1) the final step only reaches √2/2, because placing the pool fails; that is our Phase 2 problem too. The one exact result (Thm 8.1) needs p = 2 and restricted additive valuations. Rule 2 of §5 uses q = 1.
   - Relevance. Nash welfare is cardinal, and EFX₀ at k = 4 is not ordinal (K4.OT), so an ordinal potential is not forced on us. The refuted potentials (Σℓ, and the "every maximum" forms of Σ2^ℓ and leximax; K4.GM.*) are all functions of the agents' levels, that is, of each agent's order on its own subsets. NSW uses the values themselves.
   - Suggestion: try NSW, or "virtual value", as the potential for unbounded rotations in LB₄ʳ or LS4's Phase 1, and test it on H_t and on the GM₄ counterexamples.
2. **Chain reallocation with a monotone envied set (CFKS Alg. 2; Sgouritsa–Sotiriou Alg. 4/8).**
   - Each round moves bundles along a chain of envying agents until it reaches a non-envied one. The argument that no non-envied vertex becomes envied gives termination in at most n rounds of the outer loop. This is the same family as LB⁺'s rotation along a need chain (update to `proofs/novelty.md` §4 below).
   - Possible use: a Theorem B₄ that tracks "never re-frozen" agents instead of a single rotation.
3. **Choosing the start by a matching (Sgouritsa–Sotiriou, Lemma 3.7).**
   - A maximum-weight matching between agents and their first- and second-choice bundles makes at most ⌊n/2⌋ agents envied. Parking then succeeds by counting non-envied non-neighbours (Claim 3.13), which is structurally our slot count ω = |NA| − σ and the owner test.
   - `k4/c4.md` §7 says a proof may need a choice of the insertion sequence (LB₄'s search solves H₂ and H₃). A matching-based first round, each agent taking its top or second good so as to maximize the number of tops, is a concrete candidate rule to test.
4. **Minor.**
   - 2.1's Lemma 2.5 (Hall-based removal of an agent set with too few relevant goods) and Sgouritsa–Sotiriou's "degree ≥ 2 w.l.o.g." (p. 5) are special cases of our peeling (L2, K4.CORE).
   - "Most envious agent" (2.1, §5.4) is the usual Chaudhury et al. device.
   - Parking at safe sets (CFKS Lemma 13) is our junk placement.

### 3.3 Is (p, q) a sensible next direction?
Combining the bounds gives a two-parameter table (k = max goods per agent, p = max agents per good). Exact EFX₀ is known for k ≤ 3 with any p (TARGET, this project) and for p ≤ 2 with any k (the multigraph theorem). **The first open cell is (k, p) = (4, 3).** TARGET₄ is (4, ∞).
- **(4, 3) avoids the known obstruction.** Every H_t of `k4/c4.md` §7 has p = 4 (the goods g_j have four valuers) and q = 1. We computed this from the definition for t ≤ 5: H_t is a linear hypergraph with Berge 3-cycles. So:
  - restricting to q = 1 does not exclude H_t, and neither Kaviani et al.'s (∞, 1) results nor girth ≥ 4 help there;
  - p ≤ 3 excludes H_t.

  Whether LB₄ʳ with a bounded number of rotations suffices when p ≤ 3 is untested. The existing k = 4 enumerations can be filtered by maximum good degree to check it.
- **Other clean statements that fit the (p, q) literature's framing.**
  - "EFX₀ for agent degree ≤ 3 in the incidence graph, for all p, q": this is TARGET restated.
  - "EFX₀ for (4, 3)", as an intermediate target between TARGET and TARGET₄.
- **Recommendation.** Keep K4.D as the main target, since it implies TARGET₄. Record the (k, p) table in the proposal. Use (4, 3) as a test class: if bounded rotations work there, a proof with p ≤ 3 is a publishable intermediate result. The (∞, 1) regime (q = 1) is not easier for our route; H_t lives there.

## 4. Not read / [unverified]
- Christodoulou–Mastrakouis–Sgouritsa–Sotiriou, "EFX allocations on multigraphs", EC 2026 (known only from the EC 2026 program and 2406.12413 §1.2.1).
- Farhadi et al., AAAI 2021 (origin of rank).
- The journal version of 2410.17002.
- The full texts of 2412.06513 and 2512.21644 (abstracts only).
- The rest of 2406.12413 (the 3PA analysis and §5).
