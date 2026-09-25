# k = 4 local search whose exchange cycles let at most one agent take pool goods

Workstream `proof/k4-localsearch` (`k4/local_search4.md` §6, §7).

**Approach.** LS4's exchange cycles (move X), restricted so that at most one agent on the cycle takes goods from the pool. Then the pool goods used by different agents need not be kept disjoint, the only non-local constraint of X (§7). With edge-local validity, X would become a cycle search in a product graph.

**Counts** (single implementation, `k4/ls4.c -x -k -l -1`, eager order, random strict profiles). There were 3 failures in 5,468,000 profiles of the n = 5 cores with two 4-good agents (1,000 per core; m = 8, 8 and 9). None were found in 51,000 random n = 3 and 219,000 random pure n = 4 profiles.

**Where it breaks (smallest found: n = 5, m = 8).** Agents and values:
- agent 0: goods 0:2, 2:4, 6:7, 7:8;
- agent 1: goods 1:3, 2:2, 5:4;
- agent 2: goods 1:3, 6:2, 7:4;
- agent 3: goods 3:2, 4:3, 5:4;
- agent 4: goods 3:2, 4:8, 6:5, 7:4.

The run reaches Y = {7} | {5} | {1} | {4} | {3, 6} with U = {0, 2}.
- No single-agent rebundle, rotation, or exchange cycle with at most one pool-using agent improves Y.
- No complete EFX₀ allocation extends Y.
- An exchange cycle in which two agents take pool goods repairs it:
  - agent 0 takes {0, 6} (pool good 0, and good 6 from agent 4);
  - agent 4 takes {4};
  - agent 3 takes {5};
  - agent 1 takes {1, 2} (good 1 from agent 2, and pool good 2);
  - agent 2 takes {7}.

Reproduce: `python3 k4/ls4_attempts.py` (independent brute force; family XK1P). The failing runs: `python3 k4/ls4_run.py results/k4_certs_5_n4_2.json.gz --sample=1000 --flags="-x -k -l -1" --v`.
