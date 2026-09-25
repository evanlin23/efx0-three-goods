# k = 4 two-phase local search whose Phase 2 is a single dump

Workstream `proof/k4-localsearch` (`k4/local_search4.md`).

**Approach.** Phase 1 applies Pareto moves to a junk-free EFX₀ partial allocation: M1, R and the exchange cycles with keep of LS4, and even every *coalition move* G. In G, any set of agents re-divides their bundles and the pool so that each of them takes only goods it values and strictly improves, and the result is EFX₀. Phase 2 then gives the whole pool U to one bundle: an empty one, or a source whose bundle plus U nobody strongly envies. At k = 3 no single dump suffices after LS2's steps either; LS2 uses a matching. The question was whether stronger Phase-1 moves make one dump enough at k = 4.

**Where it breaks (n = 4, m = 7).** Agents and values:
- agent 0: goods 0:1, 2:6, 5:4, 6:8;
- agent 1: goods 1:4, 2:6, 3:8, 4:1;
- agent 2: goods 1:7, 4:2, 5:6, 6:10;
- agent 3: goods 3:10, 4:4, 5:7, 6:2.

`k4/ls4.c -x -k -g` reaches Y = {6} | {3} | {1, 4} | {5} with U = {0, 2}. The values are 8, 8, 9, 7; the sources are agents 2 and 3.
- No M1, R, exchange-cycle or coalition move improves Y (brute force).
- No single dump works:
  - at agent 2, agent 1 values {0, 1, 2, 4} at 11 > 8;
  - at agent 3, agent 0 values {0, 2, 5} minus good 0 at 10 > 8.
- The only complete EFX₀ allocation in which every agent is at least as well off as in Y is the split {6} | {3} | {0, 1, 4} | {2, 5}: good 0 alone at agent 2, good 2 alone at agent 3 (brute force over all 4⁷ allocations). So *no* Phase 1 made of Pareto moves can avoid a split here, once it reaches Y.

**Consequence.** Phase 2 must be able to split the pool. LS4 uses the k = 3 shape: a dump s* takes a set J ⊆ U, and every other pool good goes alone to a distinct other source (DM). DM held in every state where it was needed (`results/k4_ls4_*.log`, column `dm`).

Counts (single implementation, `k4/ls4.c`, random strict profiles):
- n = 3: in 5,100,000 profiles with M1, R and G, every stable state had a single dump.
- n = 4: 2 of 657,000 pure-core profiles have no single dump after M1, R, keep-cycles and G.
- n = 5, two 4-good agents: 352 of 8,202,000.

The smallest n with such a state is 3 or 4. The exhaustive n = 3 run of LS4 (`results/k4_ls4_3_ties.log`) counts the states where LS4 itself needed DM, but LS4 applies exchange cycles lazily, so that count does not settle it.

Reproduce: `python3 k4/ls4_attempts.py` (independent brute force from the raw definition).
