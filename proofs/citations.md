# Citations in PROMPT.md §2: verification status (Step 0)

**Result: no source could be read from this environment. Every statement attributed to the literature in PROMPT.md §2 stays [unverified].** R1 no longer depends on any of them: the cores that R1 delegated to Mahara (m ≤ n + 3) are now certified directly for n ≤ 6 (`proofs/lemmas.md`, last section).

## What was tried (2026-09-24, Claude Code on the web container)
- `curl` through the container's egress proxy got HTTP CONNECT 403, "policy denial", for arxiv.org, export.arxiv.org, ar5iv.org, ar5iv.labs.arxiv.org, alphaxiv.org, dblp.org, api.semanticscholar.org, www.semanticscholar.org, api.crossref.org, doi.org, api.openalex.org, pubsonline.informs.org (Math. Oper. Res.), drops.dagstuhl.de (LIPIcs/ESA), egres.elte.hu, dl.acm.org, link.springer.com, www.sciencedirect.com, ojs.aaai.org, www.ifaamas.org, www.researchgate.net, scholar.google.com, scholar.archive.org, web.archive.org, core.ac.uk and huggingface.co. Only GitHub was reachable.
- The WebFetch tool returned "EGRESS_BLOCKED" for arxiv.org, egres.elte.hu, api.semanticscholar.org and api.crossref.org.
- A web-search tool worked, but it returns result titles and URLs plus a machine-written summary, not the documents. Those listings are recorded below as **leads** (bibliographic data to check), not as citations.

To verify: open the URLs below from a machine with normal network access, or allow these hosts in the environment's network settings.

## Per citation

1. **Mahara (m ≤ n + 3), cited as [Mah23] by Alkassar–Fouz–Mehlhorn.** [unverified]
   - Lead: R. Mahara, "Extension of Additive Valuations to General Valuations on the Existence of EFX", arXiv:2107.09901 (https://arxiv.org/abs/2107.09901); a journal version with the same title in *Mathematics of Operations Research*, DOI 10.1287/moor.2022.0044 (https://pubsonline.informs.org/doi/10.1287/moor.2022.0044). [Mah23] is probably the journal version; that could not be checked.
   - The search tool's summary says an EFX allocation always exists when the number of items is at most n + 3. That is a machine summary, not the paper: [unverified].
   - Also listed, content unknown: EGRES Quick-Proof 2022-01, "A note on the existence of EFX allocations" (https://egres.elte.hu/qp/egresqp-22-01.pdf).
   - To check in the paper: (a) the valuation class (general monotone, or additive only); (b) the EFX notion (every good removed, or only positively valued ones); (c) the exact bound. For the use in R1, (b) does not matter: by L1, any version covering strictly positive additive valuations gives EFX₀. R1 no longer uses it.
2. **Viswanathan–Mehta (AAMAS 2024).** [unverified] Lead: M. Viswanathan and R. Mehta, "On the existence of EFX under picky or non-differentiative agents", Proc. AAMAS 2024, https://dl.acm.org/doi/10.5555/3635637.3663218. That this paper proves EFX when every agent positively values at most four goods, and how it treats zero-valued goods, could not be checked. Whatever it proves for ordinary EFX, L1 does not transfer it to EFX₀ (Note (scope) under L1 in `proofs/lemmas.md`).
3. **Christodoulou–Fiat–Koutsoupias–Sgouritsa (EC 2023).** [unverified] Lead: "Fair allocation in graphs", Proc. 24th ACM EC (EC '23), pp. 473–488 (page numbers from the search summary); a PDF titled "EFX Allocations on Graphs" is listed at https://www.cs.ox.ac.uk/people/elias.koutsoupias/Personal/Papers/fair-allocations-on-graphs.pdf. The statement for general monotone valuations and whether it is EFX or EFX₀ could not be checked.
4. **Afshinmehr–Ashuri–Mahmoudkhan–Mehlhorn–Shahrezaei, arXiv 2606.18665.** [unverified] Lead: "EFX Allocations Exist on Multi-Graphs", https://arxiv.org/abs/2606.18665; the listing names these five authors, and its summary mentions cancelable valuations. Not read.
5. **Chaudhury–Garg–Mehlhorn (JACM 2024).** [unverified] Lead: "EFX Exists for Three Agents", *Journal of the ACM* 71(1), 2024, DOI 10.1145/3616009 (https://dl.acm.org/doi/full/10.1145/3616009). Not read; the EFX notion used could not be checked.
6. **Alkassar–Fouz–Mehlhorn, arXiv 2608.08590.** [unverified] Lead: "Complete EFX Allocations Exist for Four Additive Agents and Up to Nine Goods", https://arxiv.org/pdf/2608.08590. The title says EFX; PROMPT.md says EFX₀. Which notion the paper proves, and the [Mah23] entry in its bibliography, could not be checked.
7. **Akrami et al., arXiv 2604.18216.** [unverified] Lead: H. Akrami, A. Mayorov, K. Mehlhorn, S. Srinivas, C. Weidenbach, "A Counterexample to EFX n ≥ 3 Agents, m ≥ n + 5 Items, Submodular Valuations via SAT-Solving" (another listed version of the title says "Monotone Valuations"), https://arxiv.org/abs/2604.18216. The title's m ≥ n + 5 would sit just above a general-valuation m ≤ n + 3 theorem; not read.
8. **Mackenzie–Suzuki, arXiv 2605.06451.** [unverified] Lead: "Counterexamples to EFX for Submodular and Subadditive Valuations", https://arxiv.org/pdf/2605.06451. Not read.

## Possibly relevant, not in PROMPT.md (leads only, not read)
These titles showed up in the same searches. PROMPT.md §5 rule 5 says to check that new results do not follow from known ones, so these should be read once the hosts are reachable:
- T. Lianeas, A. Sgouritsa, M. M. Sotiriou, "EFX Allocation In (Multi)Hypergraphs", arXiv 2608.03171 (listed as AAAI 2026). The listing's summary: EFX for hypergraphs of girth ≥ 4 with general monotone valuations, where agents are vertices and goods are edges. In our setting agents are 3-sets of goods, which is the dual picture; any relation is unverified.
- "Rival-Injective Allocations: Support-List Structure and Maximum-Anchor EFX_0 Certificates", arXiv 2608.30203 (https://arxiv.org/html/2608.30203v1).
- "Almost EFX in Hypergraphs", arXiv 2606.26948; "EFX Allocations on Some Multi-graph Classes", arXiv 2412.06513; "On the existence of EFX allocations in multigraphs", arXiv 2502.09777; "A Simple Polynomial-Time EFX Repair for Cancelable Valuations", arXiv 2608.08864.
