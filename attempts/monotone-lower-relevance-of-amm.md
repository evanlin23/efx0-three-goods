# Lowering the relevance of the monotone counterexample (failed)

Workstream `proof/monotone-k`. Goal: modify the three-agent, eight-good instance of Akrami et al. (arXiv
2604.18216v4, §3.1; every agent values all 8 goods) so that some agent ignores a good and there is still no EFX₀
allocation. That would be a monotone counterexample with lower relevance.

## What was tried

1. **Delete or merge goods.** Deleting any one good, or merging any two goods into one, leaves 7 goods. Every
   such instance has an EFX₀ allocation (`monotone/amm_check.py`), as the paper's Theorem 1.2 (m ≤ 7 at n = 3)
   predicts.
2. **One agent ignores one good, the other two unchanged.** Pin agents a, b to the paper's valuations. Let agent c
   be an *arbitrary* monotone valuation on the 7 goods other than d. Is there one with no EFX₀ allocation? By the
   symmetry of the instance it suffices to try d ∈ {A1, B1, C1, x, y}.
   **UNSAT in all five cases** (CEGAR, order encoding, 28–44 allocations each, < 1 s;
   `results/monotone/amm_modify.jsonl`). Control: with c free on all 8 goods the same search returns a
   counterexample (verified by brute force).
3. **Two agents ignore one good each, the third unchanged.** Pin a; b ignores d_b, c ignores d_c, both
   arbitrary monotone on their 7 goods. There are 17 cases up to the symmetries fixing a (swapping the two
   goods of a type; swapping (b, B) with (c, C)), written d_b/d_c: A1/A1, A1/A2, A1/B1, A1/C1, A1/x, A1/y, B1/B1,
   B1/B2, B1/C1, B1/x, B1/y, C1/B1, C1/x, C1/y, x/x, x/y, y/y. **UNSAT in all 17** (314–405 allocations each,
   ≤ 24 s; `results/monotone/amm_modify_level2.jsonl`).
4. **No agent pinned, every agent ignores a good** (k = 7 on 8 goods): this is the general n = 3, m = 8, k = 7
   search of `monotone/threshold.md`.

## Smallest failing configuration

Item 2: agents a, b as in the paper (eqs. (2)–(3)), agent c with R_c = M ∖ {d} for any single good d. Every monotone
v_c on R_c leaves an EFX₀ allocation. So, given the other two agents, every agent's full relevance is necessary.
This restricts the paper's instance only. Instances with other valuations for all three agents are the subject of
the general search (`monotone/threshold.md`).

Reproduce: `python3 monotone/amm_modify.py` (item 2), `python3 monotone/amm_modify.py --level2` (item 3).
