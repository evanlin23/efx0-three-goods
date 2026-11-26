# LSS's Algorithm 2 (unrepaired) followed by dynamic parking

Workstream `proof/k4-girth` (`k4/girth.md` §5). **Approach:** run LSS's Algorithm 2 as written, for some vertex 0 and
labeling, then place the leftover goods one at a time on agents that are non-envied at that moment (dynamic parking).

**Result: fails at n = 4.** On random strict profiles of the k = 4 cores with n = 2 and n = 3 some run always completes,
but 38 of about 85,000 sampled n = 4 core profiles have no completing run (`results/k4_girth_dyn_cores4_plain.log`).
On the first one, agent: {good: value}:

    0: {0: 4, 2: 2, 3: 3}    1: {1: 4, 4: 8, 5: 2, 6: 3}    2: {2: 4, 4: 8, 5: 2, 6: 3}    3: {3: 6, 4: 8, 5: 4, 6: 5}

every one of the 16 labelings breaks EFX₀ inside Algorithm 2, at line 4 (girth use G1). Agents 1, 2 and 3 all value
the goods 4, 5, 6 (three pairwise 2-cycles on the same three goods): an envied agent i takes all of U_i, which contains
two of these goods, and another of the three agents strongly envies it.

**Repair (G1):** line 4 gives i the most valuable subset T ⊆ U_i with v_i(T) > v_i(X_i) that keeps EFX₀, and skips i
when there is none (`lss.Run.alg2_safe`). With it, all 16 labelings of this instance complete, and so do all 38
instances (some labeling). Conjecture DYN (`k4/girth.md` §5) is stated for the repaired version.

**Reproduce:** `python3 attempts/k4_girth_attempts.py` (part 5).
