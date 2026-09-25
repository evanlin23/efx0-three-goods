# k = 4 local search with exchange cycles of length at most 2

Workstream `proof/k4-localsearch` (`k4/local_search4.md` §6).

**Approach.** LS4 with its exchange cycles (move X: agents may keep part of their own bundle and take part of the next agent's bundle and the pool) restricted to cycles of two agents. Cycles of bounded length would make the search for X polynomial.

**Counts** (single implementation, `k4/ls4.c -x -k -L 2`, eager order, random strict profiles). The run fails when it ends in a state that no move improves and no placement completes:
- n = 3: 6,432 failures in 5,100,000 profiles (100,000 per core);
- pure n = 4: 302 in 219,000.

With cycles of every length, LS4 did not fail at n = 3 (exhaustive, `results/k4_ls4_3_ties.log`). Cycles of length 3 occur there 278,848 times, and of length 5 at n = 5.

**Where it breaks (smallest found: n = 3, m = 5).** Agents and values:
- agent 0: goods 0:1, 1:4, 2:6, 4:8;
- agent 1: goods 1:2, 3:3, 4:4;
- agent 2: goods 2:3, 3:4, 4:2.

`k4/ls4.c -x -k -L 2` reaches Y = {4} | {3} | {2} with the pool U = {0, 1}.
- No single-agent rebundle, rotation or two-agent exchange cycle improves Y.
- No complete EFX₀ allocation extends Y, even if pool goods may go to agents that value them.
- A three-agent exchange cycle repairs it: agent 0 takes {1, 2}, agent 2 takes {3}, agent 1 takes {4}.

Cores with m = 4 had no failure in the sample; that is not a proof that m = 5 is smallest.

Reproduce: `python3 k4/ls4_attempts.py`, an independent brute force from the raw definition (family XK2 = cycles of two agents). The failing runs: `python3 k4/ls4_run.py results/k4_certs_3.json.gz --sample=100000 --flags="-x -k -L 2" --v`.
