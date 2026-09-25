# k = 4 two-phase local search with single-agent rebundles and rotations only

Workstream `proof/k4-localsearch` (`k4/local_search4.md`, Algorithm LS4 and its variants).

**Approach.** The k = 3 Algorithm LS2 (`proofs/local_search.md`) carried to k = 4 cores without its cycle moves. Phase 1 keeps a junk-free EFX₀ partial allocation Y and applies, while one exists:
- M1, a valued single-agent rebundle: an agent h replaces Y_h by a set Z of its own goods drawn from Y_h and the pool U, with v_h(Z) > v_h(Y_h) and the result EFX₀ (this contains LS2's swap, bottom-pair, add and source-add steps);
- R, the rotation of an envy cycle.

Phase 2 places U as junk.

**Where it breaks (n = 2, m = 4, the smallest k = 4 core size).** The core with two agents on the same four goods 0, 1, 2, 3. Values: agent 0 (0:4, 1:1, 2:6, 3:8), agent 1 (0:2, 1:3, 2:4, 3:8). Both are strictly balanced.
- Phase 1 reaches Y = {3} | {1, 2}, U = {0}: agent 0 holds 8, agent 1 holds 7.
- No M1 or R move improves Y. Agent 1 taking {0, 1, 2} (value 9) is strongly envied by agent 0, who values {0, 1, 2} minus its least good at 10 > 8. Agent 0 taking {0, 3} (12) is strongly envied by agent 1, who values {0, 3} minus good 0 at 8 > 7.
- No complete EFX₀ allocation extends Y. Good 0 at agent 1 gives {0, 1, 2}; good 0 at agent 0 gives {0, 3} (both strongly envied as above).
- The exchange cycle 0 → 1 → 0 repairs it: agent 0 takes {0, 2} (10 > 8), agent 1 takes {3} (8 > 7), and good 1 goes to the pool. Then {0, 2} | {1, 3} is EFX₀.

Count: in `k4/ls4.c` without exchange cycles, 648 of the 189,216 strict profiles of the five n = 2 cores fail (single implementation). With the exchange cycles of LS4 none fails (`results/k4_ls4_2_ties.log`). The same example is the `-DNOX` sensitivity test of `k4/ls4alg.c` (`results/k4_ls4_sensitivity.log`).

So at k = 4 cycle moves are needed already at n = 2. At k = 3 they are needed first at n = 6 (`attempts/local-search-twophase-m1m2.md`).

Reproduce: `python3 k4/ls4_attempts.py` (independent brute force from the raw definition: Y is junk-free and EFX₀, no M1 or R move exists, no completion exists, the exchange cycle exists).
