# Novelty of TARGET and conjecture D: literature search

Workstream `proof/lit-search`, 2026-09-25. Search log (every query and source, with access notes): `results/lit_search_log.md`. Papers read here are also recorded in `proofs/citations.md` ("Other papers checked"). No ledger status is changed by this file.

Read levels: **full** (whole text read), **section** (named pages or sections read), **grep** (full text searched by pattern, every match read in context), **abstract**, **snippet** (search result or metadata only), **earlier** (read in full in an earlier session, recorded in `proofs/citations.md`, not re-read here). Anything not read at one of these levels is marked [unverified].

The claims checked:
- **TARGET**: every additive instance with nonnegative values in which each agent positively values at most 3 goods has a complete EFX₀ allocation (v_i(X_i) ≥ v_i(X_j ∖ {g}) for all i ≠ j and all g ∈ X_j, including goods i values at 0).
- **D**: if every agent values exactly 3 goods and is balanced, some EFX₀ allocation has at most one bundle with more than two goods.

## 1. Verdict

**Novel.** No published paper or preprint found proves TARGET, D, or anything that implies either. Confidence: high for TARGET (about 90 %), higher for D (about 95 %), since D's shape statement has no counterpart anywhere in the literature.

Why nothing found implies TARGET:
- **Viswanathan–Mehta** (AAMAS 2024, 3-page extended abstract; read in full) is the only work on few relevant goods per agent. It proves **ordinary EFX** (only goods the envier values positively may be removed) for agents with at most **4** relevant goods. It names EFX₀ in footnote 2 as a different, stronger notion, and its algorithm ends by giving the goods nobody values "to an arbitrary agent" (p. 2), a step that is harmless for EFX but can break EFX₀. No full version exists: not on arXiv, not in Ruta Mehta's 2026 CV (which lists it only as AAMAS 2024 paper C51), and the two NSF-PAR copies are the same extended abstract. It has no indexed citations (Google Scholar shows no "Cited by"; Crossref and OpenAlex count 0), and none of the 112 EFX papers posted to arXiv since April 2024 cites it (full-text search, log §4). TARGET and this result are **incomparable**: TARGET has the stronger notion, Viswanathan–Mehta the larger bound. TARGET implies their result for agents with at most three relevant goods, since EFX₀ implies EFX; theirs does not imply TARGET.
- The other existence results that contain parts of TARGET restrict something TARGET leaves free: the number of agents (n ≤ 3: Chaudhury–Garg–Mehlhorn; n = 4 with m ≤ 9: Alkassar–Fouz–Mehlhorn), the number of goods (m ≤ n + 3: Mahara), the number of valuers per good (at most two: the multigraph theorems), the hypergraph girth (≥ 4: Lianeas–Sgouritsa–Sotiriou), the number of valuation types (at most three), or the values themselves (binary, bivalued). A concrete instance outside all of them is the core of PROMPT.md §3, agents (a, b, c) = (1,0,6) (1,0,7) (2,0,8) (3,0,9) (2,4,5) (3,4,5), with generic balanced values. It has n = 6 and m = 10 = n + 4. Good 0 is valued by four agents. Agents 0 and 1 share two goods, a 2-cycle in the hypergraph where goods are hyperedges on agents. The six valuations are pairwise different. TARGET covers this instance; no earlier theorem does.
- TARGET would follow from the additive EFX conjecture, via the perturbation lemma L1 (Chaudhury–Garg–Mehlhorn's Lemma 1 is the same argument). That conjecture is still open for n ≥ 4: EconCSLib states it as an open problem (2606.16144, Fig. 5, p. 7), and Wang (2608.30203) and Alkassar–Fouz–Mehlhorn call it open.

**Counter-evidence (question 4): none.** No claimed counterexample to EFX₀ (or EFX) for additive valuations exists in anything found. The known non-existence results are for monotone, submodular or subadditive valuations (2604.18216, 2605.06451), for chores (2406.10752, 2606.08872, 2608.10572), and for EFX *orientations* on graphs (Christodoulou et al., Fig. 1). None of them applies to additive goods.

**Residual risks.**
1. *Work not visible to the searches.* The searches cover arXiv (92 queries, 290 papers), the open web (17 queries), Google Scholar (title level), Crossref, and the EC 2026 program. Proceedings-only 2025–2026 papers, theses and course notes could be missed. One unread item is on record: EC 2026 paper #136, "EFX allocations on multigraphs" (Christodoulou, Mastrakouis, Sgouritsa, Sotiriou), which is not on arXiv [unverified]. Its title restricts it to multigraphs, where each good has at most two valuers, so it cannot imply TARGET unless its content goes beyond its title.
2. *Citation lists.* Semantic Scholar was unreachable (HTTP 429) and OpenAlex over budget, so forward citations of Viswanathan–Mehta were checked only through Google Scholar (none), Crossref and OpenAlex counts (0), and the arXiv full-text sweep (none). A non-arXiv citing paper could be missed.
3. *Unpublished full version.* Viswanathan–Mehta's extended abstract gives only a proof sketch. An unpublished full version could handle EFX₀; nothing indicates it does. Ruta Mehta, the second author, is the natural person to ask.
4. *Folklore.* The k = 2 case (serial dictatorship; L2c, and the owner's evanlin23/mrd-efx) is elementary and may be folklore. Nothing found states k = 3 in any form.
5. *Later preprints.* This search ends on 2026-09-25.

## 2. What prior work covers, by restriction

| Restriction | Result | Notion | Covers TARGET instances with … | Source (read level) |
|---|---|---|---|---|
| ≤ 4 relevant goods per agent | EFX exists (polynomial-time algorithm, sketch only) | ordinary EFX | nothing, for EFX₀ | Viswanathan–Mehta (full) |
| n = 3 | EFX exists (additive) | EFX₀ (p. 5: "strongly envies S if X_i <_i S ∖ g for some g ∈ S") | n ≤ 3 | Chaudhury–Garg–Mehlhorn 2002.05119 (section: abstract, pp. 5–6) |
| n = 4, m ≤ 9 | EFX₀ exists (certified) | EFX₀ | n = 4, m ≤ 9 | Alkassar–Fouz–Mehlhorn 2608.08590 (earlier; grep) |
| m ≤ n + 3 | EFX exists, monotone valuations | EFX₀ | m ≤ n + 3 | Mahara 2107.09901 (earlier) |
| each good valued by ≤ 2 agents (multigraphs), cancelable | EFX exists | EFX₀ | no good with ≥ 3 valuers | Afshinmehr et al. 2606.18665 (earlier) |
| simple graphs, monotone | EFX exists | EFX₀ (p. 3) | subsumed by the row above | Christodoulou–Fiat–Koutsoupias–Sgouritsa (section: pp. 1–4) |
| hypergraphs of girth ≥ 4 (goods = hyperedges on agents) | EFX exists, monotone | EFX₀ | few cores (short cycles are common) | Lianeas–Sgouritsa–Sotiriou 2608.03171 (earlier) |
| ≤ 3 distinct additive valuations | EFX exists | not checked | ≤ 3 valuation types | Prakash HV–Ghosal–Nimbhorkar–Varma 2410.13580 (abstract) |
| binary marginals | EFX exists | not checked | 0/1 values only | Bu–Song–Yu 2308.05503 (abstract) |
| personalized bivalued {a_i, b_i} | EFX exists | not checked | two values per agent | Byrka–Malinka–Ponitka 2507.14957 (abstract) |
| ternary {0, a, b}, b ≤ 2a | EFX exists | ordinary EFX | nothing, for EFX₀ | Viswanathan–Mehta (full) |

For the TARGET class only the rows with an EFX₀ notion count, and each leaves out cores like the one in §1. None of the papers says anything about the shape of the allocation (D).

## 3. Relevant papers

"Implies?" means: implies TARGET or D. "Earlier" means read in full in an earlier session (`proofs/citations.md`) and not re-read here.

| Paper | Link | What it proves | Notion | Restriction | Implies? | Read |
|---|---|---|---|---|---|---|
| M. Viswanathan, R. Mehta, "On the existence of EFX under picky or non-differentiative agents", AAMAS 2024 (EA), pp. 2534–2536 | [ACM](https://dl.acm.org/doi/10.5555/3635637.3663218), [PAR](https://par.nsf.gov/biblio/10511105) | EFX for 4-limited instances and for ternary {0, a, b}, b ≤ 2a; sketches only | EFX (footnote 2 names EFX₀ as a different notion) | ≤ 4 relevant goods per agent | no | full |
| R. Mahara, arXiv 2107.09901 | [arXiv](https://arxiv.org/abs/2107.09901) | EFX for monotone valuations when m ≤ n + 3 (Thm 3) | EFX₀ | m ≤ n + 3 | no (subclass) | earlier |
| B. R. Chaudhury, J. Garg, K. Mehlhorn, "EFX exists for three agents", arXiv 2002.05119 | [arXiv](https://arxiv.org/abs/2002.05119) | EFX for 3 additive agents; Lemma 1 (pp. 5–6): reduction to non-degenerate instances by perturbation | EFX₀ | n = 3 | no (subclass) | section (abstract, pp. 5–6) |
| E. Alkassar, M. Fouz, K. Mehlhorn, arXiv 2608.08590 | [arXiv](https://arxiv.org/abs/2608.08590) | EFX₀ for 4 additive agents, m ≤ 9 (hand reductions and SMT certificates) | EFX₀ (Def. 1) | n = 4, m ≤ 9 | no (subclass) | earlier; grep |
| M. Afshinmehr, A. Ashuri, P. Mahmoudkhan, K. Mehlhorn, A. M. Shahrezaei, arXiv 2606.18665 (EC 2026) | [arXiv](https://arxiv.org/abs/2606.18665) | EFX on multigraphs, cancelable valuations | EFX₀ | each good valued by ≤ 2 agents | no (subclass) | earlier |
| G. Christodoulou, A. Fiat, E. Koutsoupias, A. Sgouritsa, "EFX allocations on graphs" (EC 2023; author PDF of 15 Mar 2025) | [PDF](https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/fair-allocations-on-graphs.pdf) | EFX on simple graphs, monotone valuations; EFX orientations may not exist (Fig. 1) and deciding them is NP-complete | EFX₀ (p. 3) | graphs | no | section (pp. 1–4) |
| T. Lianeas, A. Sgouritsa, M. M. Sotiriou, arXiv 2608.03171 (AAAI) | [arXiv](https://arxiv.org/abs/2608.03171) | EFX on (multi)hypergraphs of girth ≥ 4 | EFX₀ | girth ≥ 4 | no | earlier |
| I. Kakatelis, T. Lianeas, A. Sgouritsa, M. M. Sotiriou, arXiv 2606.26948 | [arXiv](https://arxiv.org/abs/2606.26948) | EF2X, EF3X, approximate EFX on hypergraphs | approximations | girth ≥ 3 | no | earlier; grep |
| U. Bhaskar, Y. Pandit, arXiv 2412.06513 | [arXiv](https://arxiv.org/abs/2412.06513) | EFX on bipartite multigraphs, multi-trees, multigraphs of girth 2t − 1 | EFX | multigraphs | no | abstract |
| A. Sgouritsa, M. M. Sotiriou, arXiv 2502.09777 | [arXiv](https://arxiv.org/abs/2502.09777) | EFX on multigraphs if bipartite, or max. neighbours ≤ ⌈n/4⌉ − 1, or girth (non-parallel) ≥ 6 | EFX | multigraphs | no | abstract |
| M. Afshinmehr, A. Ashuri, P. Mahmoudkhan, K. Mehlhorn, arXiv 2512.21644 | [arXiv](https://arxiv.org/abs/2512.21644) | EFX on triangle-free multigraphs | EFX | multigraphs | no | abstract |
| M. Afshinmehr, A. Danaei, M. Kazemi, K. Mehlhorn, N. Rathi, arXiv 2410.17002 | [arXiv](https://arxiv.org/abs/2410.17002) | EFX on bipartite multigraphs, multi-cycles; orientation characterization | EFX | multigraphs | no | abstract |
| B. Li, M. Li, T. Wei, Z. Wu, Y. Zhou, arXiv 2409.03594 | [arXiv](https://arxiv.org/abs/2409.03594) | EFX landscape on simple graphs for goods, chores, mixed manna | several variants | simple graphs | no | abstract |
| J. A. Zeng, R. Mehta, arXiv 2404.13527 | [arXiv](https://arxiv.org/abs/2404.13527) | "strongly EFX orientable" graphs (orientable for all values), via chromatic number | orientations | graphs | no; note the name clash: "strongly EFX" there is not EFX₀ | abstract |
| K. Hsu, "Fair Division of Indivisible Items" (thesis), arXiv 2510.12158 | [arXiv](https://arxiv.org/abs/2510.12158) | EFX orientations of multigraphs (NP-completeness, bi-valued cases), MMS for mixed manna | EFX₀ used | multigraphs | no | abstract |
| V. Prakash HV, P. Ghosal, P. Nimbhorkar, N. Varma, arXiv 2410.13580 (EC 2025) | [arXiv](https://arxiv.org/abs/2410.13580) | EFX for ≤ 3 distinct additive valuations | not checked | valuation types | no | abstract |
| X. Bu, J. Song, Z. Yu, arXiv 2308.05503 | [arXiv](https://arxiv.org/abs/2308.05503) | EFX for binary (0/1-marginal) valuations | not checked | binary | no | abstract |
| J. Byrka, F. Malinka, T. Ponitka, arXiv 2507.14957 (AAAI 2026) | [arXiv](https://arxiv.org/abs/2507.14957) | EFX for personalized bivalued; PMMS for pair-demand valuations | not checked | values | no | abstract |
| V. Livanos, R. Mehta, A. Murhekar, arXiv 2202.02672 | [arXiv](https://arxiv.org/abs/2202.02672) | EFX₀ for binary mixed goods (restricted mixed manna) | EFX₀ | values | no | abstract |
| J. Wang, arXiv 2608.30203 | [arXiv](https://arxiv.org/abs/2608.30203) | rival-injective EFX₀ certificates; says additive EFX₀ is open for n ≥ 4 | EFX₀ | – | no | earlier |
| T. Y. Neoh, N. Teh, arXiv 2504.03951 (AAAI 2025) | [arXiv](https://arxiv.org/abs/2504.03951) | minimum number of EFX allocations when m is slightly above n; EFX+ | EFX variants | m ≈ n | no | abstract |
| E. Lim, T. Y. Neoh, N. Teh, arXiv 2601.12849 | [arXiv](https://arxiv.org/abs/2601.12849) | welfare and complexity of EFX with ≤ 3 surplus goods | EFX and a stronger variant | m ≤ n + 3 | no | abstract |
| U. Kumar, S. Roy, arXiv 2507.09600 | [arXiv](https://arxiv.org/abs/2507.09600) | EFX when two agents are arbitrary and the rest size-monotonic | EFX | valuations | no | abstract |
| Q. Qin, arXiv 2608.30267 | [arXiv](https://arxiv.org/abs/2608.30267) | exact EFX → MMS factor 10/17; tight examples that are EFX₀ | EFX₀ used | – | no | abstract |
| N. Shah, P. Verma, arXiv 2608.29497 | [arXiv](https://arxiv.org/abs/2608.29497) | EF1/EFX variants for non-normalized Boolean valuations | variants | Boolean | no | abstract |
| S. J. Brams, D. M. Kilgour, C. Klamler, *Games* 17(1):4, 2026 | [DOI](https://doi.org/10.3390/g17010004) | small instances where EF, EFX, EFX₀ conflict with PO, maximin, MNW | EFX and EFX₀ | – | no | abstract (Crossref) |
| G. Amanatidis, G. Birmpas, A. Filos-Ratsikas, A. A. Voudouris, survey, arXiv 2202.07551 | [arXiv](https://arxiv.org/abs/2202.07551) | survey; p. 5: the stronger notion "is usually called EFX0" and, beyond binary valuations, its existence reduces to EFX existence | – | – | no | grep (p. 5) |
| G. Amanatidis et al., "Recent progress and open questions", arXiv 2208.08782 | [arXiv](https://arxiv.org/abs/2208.08782) | survey; p. 6: envy-cycle elimination gives goods to an agent of in-degree 0 in the envy graph | – | – | no | grep (p. 6) |
| K. N. Gowda et al., arXiv 2605.16791 | [arXiv](https://arxiv.org/abs/2605.16791) | parallel EF1 algorithms; cites CC-hardness of round robin even when each agent values ≤ 3 goods and each good ≤ 3 agents | EF1 | ≤ 3 goods per agent | no (EF1, complexity) | grep |
| A. Akrami, A. Mayorov, K. Mehlhorn, S. Srinivas, C. Weidenbach, arXiv 2604.18216 | [arXiv](https://arxiv.org/abs/2604.18216) | no EFX for monotone valuations with n ≥ 3, m ≥ n + 5; EFX for n = 3, m = 7 (SAT); §9 (pp. 17–20): Lean proof that the SAT encoding is sound | EFX (strictly monotone valuations) | monotone | no | section (abstract, §9) |
| S. Mackenzie, M. Suzuki, arXiv 2605.06451 | [arXiv](https://arxiv.org/abs/2605.06451) | no EFX for submodular or subadditive valuations (n = 3, m = 8) | EFX | not additive | no | earlier (abstract) |
| S. Brânzei, arXiv 2510.05429 | [arXiv](https://arxiv.org/abs/2510.05429) | simulated-annealing local search for EFX (empirical); potential-function existence proof for identical valuations | EFX | identical valuations | no | abstract |
| X. Bei, J. Ma, Z. Jing, H. Fu, Z. G. Tang, "EconCSLib", arXiv 2606.16144 | [arXiv](https://arxiv.org/abs/2606.16144) | Lean 4 library; lists "the existence of EFX allocations for two agents" as formalized (§2.2, p. 6); additive EFX stated as an open problem (Fig. 5, p. 7) | EFX (notion not stated in the paper) | n = 2 | no | full (10 pp.) |
| N. Garg, "EconCSLib", arXiv 2606.13306 | [arXiv](https://arxiv.org/abs/2606.13306) | Lean 4 library of 20 formalized papers; its fair-division content is Lipton–Markakis–Mossel–Saberi (EF1, envy cycles) (Table 1, p. 6); no EFX | – | – | no | grep |
| Z. Lin, S. Liu, B. Tao, S. Zhou, arXiv 2608.10572 | [arXiv](https://arxiv.org/abs/2608.10572) | no EFX for chores with binary-marginal XOS or supermodular costs; main results verified in Lean 4 | EFX (chores) | chores | no | abstract |
| Ruta Mehta, CV (2026 version) | [PDF](https://rutamehta.cs.illinois.edu/Mehta-CV.pdf) | lists Viswanathan–Mehta only as AAMAS 2024 (C51); no journal or working-paper version | – | – | – | full |

Checked and irrelevant (abstracts unless stated; search log §3–§4): binary-valuation rule characterizations (Brandl–Suksompong–Teh 2607.10064); chores (He–Tao 2606.08872, additive chores non-existence; Zhang 2609.10585, computer-assisted chores EFX₀ for n = 3, m ≤ 8); Etesami's fixed-point framework (2510.04915); approximate EFX (Amanatidis–Filos-Ratsikas–Sgouritsa 2406.12413; Kaviani et al. 2506.09288 and 2407.05139, which define (p, q)-bounded instances, each good relevant to ≤ p agents: the dual of our bound); α-EFX from ordinal information (2602.08714, 2308.04860); the UIUC CS 580 Fall 2023 student slides on EFX (full; a local-improvement map, no new existence result).

## 4. Method novelty

| Method (where) | Closest prior art found | Assessment |
|---|---|---|
| L1 perturbation (EFX₀ for a class of (n, m) ⟺ EFX for positive instances) | Chaudhury–Garg–Mehlhorn Lemma 1 (2002.05119, pp. 5–6): perturb v_i(g_j) by ε·2^j so strict comparisons are kept and no two sets tie; an EFX allocation of the perturbed instance is EFX₀ for the original. The survey 2202.07551 (p. 5) states the reduction in general | known; cite it |
| L2 peeling, R1 (a top-heavy agent, a ≥ b + c, takes its top good) | Viswanathan–Mehta Phase I (p. 2): agents that value their top object more than their second and third combined get a first choice by maximum matching (ordinary EFX, sketch only) | the same idea appears in Viswanathan–Mehta; R2, the peeling proof for EFX₀, and the notion of a core were not found |
| L3 junk at an envy-graph source, after removing envy cycles | standard envy-cycle elimination (Lipton et al. 2004 [unverified], described in 2208.08782, p. 6); goods given to a source of an (enhanced) envy graph in 2406.12413 (pp. 25, 35); Viswanathan–Mehta give each remaining positively-valued object to a source of their "EFX graph" (p. 2). That EFX₀ can force goods onto agents who value them at zero is Christodoulou et al.'s point (p. 2, Fig. 1) | known technique; its use for zero-valued goods under EFX₀ is routine |
| L5: EFX₀ in a core is ordinal (depends only on each agent's ranking of its 3 goods; cases T, P, B, C, E) | EFX in general depends only on each agent's comparisons between bundles (Chaudhury–Garg–Mehlhorn write S <_i T; Akrami et al. 2604.18216 encode "levelled" ordinal valuations for SAT). Alkassar–Fouz–Mehlhorn cover the valuation space by polytopes with fixed allocations. Ordinal-information EFX papers (2602.08714, 2308.04860) study approximations | the general principle is known; the reduction to rankings in cores and the safety cases were not found |
| L12: real values → natural numbers by order-pattern representatives | same comparison-only principle (above) | routine given L5-type reasoning; no specific prior statement |
| LB⁺: serial dictatorship with R1 priority and junk placement, then one rotation along a need chain, owner chosen by a minimum-hitting-set test | serial dictatorship and picking sequences are classical; Viswanathan–Mehta assign by rank with repeated maximum matchings; envy-*cycle* rotation is standard. In the full-text sweep, "need chain" occurs nowhere and "hitting set" only in hardness reductions (2608.30669) and communication bounds (2407.07641) | the combination (rotation along a path of needs, hitting-set owner test, the one-large-bundle shape) was not found; building blocks are standard |
| Two-phase local search (Pareto-improving moves with a level potential ≤ 7n; junk placed by a maximum matching via Hall's theorem; augmented envy cycles) | potential-function local search is the main existence technique: Chaudhury–Garg–Mehlhorn build sequences of Pareto-improving EFX allocations (p. 6, "Overall approach"); Mahara uses champion graphs and lexicographic potentials (as summarized in 2608.08590); Brânzei gives a local search and a potential for identical valuations (2510.05429); matching phases appear in Viswanathan–Mehta | the framework is standard; the specific moves, potential and matching-based junk placement were not found |
| Lean 4 formalization | EconCSLib (Bei et al.): EFX for two agents in Lean 4 (p. 6); Akrami et al.: Lean proof that their SAT encoding is sound (§9), so their n = 3, m = 7 existence result is machine-checked up to the SAT solver; Lin et al.: Lean 4 verification of EFX non-existence for chores; Isabelle AFP has no fair-division entry; evanlin23/mrd-efx (ours, k = 2) | **not the first machine-checked EFX existence theorem.** No machine-checked EFX or EFX₀ existence theorem for arbitrarily many agents was found, other than the owner's own k = 2 development |

## 5. Recommended wording (research proposal)

Suggested text:

> We prove that every fair-division instance with nonnegative additive valuations in which each agent positively values at most three goods admits a complete EFX₀ allocation (envy-freeness up to any good, where the removed good may be worthless to the envious agent). Moreover, when every agent values exactly three goods and is balanced, some EFX₀ allocation has at most one bundle of more than two goods. To our knowledge both results are new. The closest prior result, by Viswanathan and Mehta (AAMAS 2024, extended abstract), shows that ordinary EFX allocations exist when each agent values at most four goods. Their notion allows removing only goods the envious agent values positively, and their algorithm gives unvalued goods to an arbitrary agent, so it does not yield EFX₀; the two results are incomparable. Previously, EFX₀ was known on this class only in special cases: at most three agents (Chaudhury, Garg and Mehlhorn), four agents and at most nine goods (Alkassar, Fouz and Mehlhorn), at most n + 3 goods (Mahara), and goods valued by at most two agents (the multigraph theorems of Christodoulou et al. and Afshinmehr et al.). The theorem is machine-checked in Lean 4 (core Lean, standard axioms only) for natural-number valuations; the extension to real values is a short written reduction.

Wording to avoid:
- "the first machine-checked proof of an EFX existence theorem." EconCSLib (two agents) and Akrami et al. (the encoding behind their n = 3, m = 7 result) come first. If a formalization claim is wanted: "to our knowledge, the first machine-checked EFX₀ existence theorem for an unbounded number of agents, apart from our earlier two-goods development."
- "strengthens" or "extends" Viswanathan–Mehta. The results are incomparable (stronger notion, smaller bound).
- "resolves an open problem." Nothing found poses the three-goods EFX₀ question in print.
- "novel techniques" for the peeling rule R1, the envy-graph source placement, or the perturbation lemma. These have prior art (§4). The core reduction as a whole, the ordinal case analysis, LB⁺'s need-chain rotation with the hitting-set owner test, and the specific local search can be presented as new, with "to our knowledge".
- "machine-checked for real valuations", until PR #20 (L12 in Lean) is merged. Until then the Lean theorems are stated over natural numbers and the step to real values is the written reduction L12 (`proofs/real_values.md`).
