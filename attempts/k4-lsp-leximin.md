# Leximin of the levels as the potential

Workstream `proof/k4-ls-plus` (`k4/ls4plus.md` §2, §4).

**Approach.** Allow non-Pareto moves under a potential other than the level sum: the *leximin* order of the level vector (sorted ascending, compared lexicographically). A local search with arbitrary leximin-raising moves stops only at a leximin-maximal junk-free EFX₀ partial allocation. The hope was that such maxima always admit a placement, the leximin analogue of conjecture GM₄.

**Where it breaks (smallest found: n = 4, m = 7): the profile of Proposition 7 of `k4/local_search4.md`.** Leximin was searched only on the 19 logged LS4 failure profiles, at n = 2 (exhaustive) and on 102,000 random n = 3 profiles. Agents and values:
- agent 0: goods 0:8, 2:10, 5:6, 6:3;
- agent 1: goods 0:5, 3:2, 4:4, 6:8;
- agent 2: goods 1:1, 2:8, 4:6, 6:4;
- agent 3: goods 1:2, 3:3, 5:6, 6:10.

Its unique leximin-maximal junk-free EFX₀ partial allocation is the dead end itself: {2} | {6} | {1, 4} | {3, 5} with pool {0}, and sorted levels (5, 5, 6, 6). It has no completion. The balanced level vector of the dead end is what leximin rewards. LS4 really gets there under leximin moves. Its 15 moves are single-agent rebundles, each raising one agent's level and keeping the others, so each raises the sorted level vector. LS4 with leximin-raising moves therefore reaches this unique leximin maximum.

Count (`k4/ls4_gm.c -DPOT=1`, `results/k4_lsp_variants_19.log`): of the 19 LS4 failure profiles, this is the only one whose leximin maximum lacks a placement. At n = 2 (exhaustive) and on 102,000 random n = 3 profiles leximin had no failure (`results/k4_gm_pot1_2.log`, `results/k4_gm_pot1_3_sample.log`). The level sum (`-DPOT=0`) and the fixed-priority order (`-DPOT=2`) have no failure on them.

Reproduce: `python3 k4/lsp_attempts.py` (brute force over all junk-free EFX₀ partial allocations of the profile).
