# LS4 with the alternative choice rule -DALT

Workstream `proof/k4-localsearch` (`k4/local_search4.md` §4, §5).

**Approach.** LS4 with other choices, to see whether the dead ends of `attempts/k4-ls-dead-end.md` are an artifact of the default rule. The default rule takes, in move M1, the first agent and its least valuable improving set, and shorter exchange cycles first. `-DALT` changes three things:
- in M1 it takes the most valuable improving set;
- it scans agents from a start that rotates with every step;
- it tries longer exchange cycles first.

On the dead-end profile of `attempts/k4-ls-dead-end.md` it succeeds, in 5 steps.

**Counts** (`k4/ls4alg.c -DALT`, `results/k4_ls4_4_pure_alt_sample.log`). There were 23 failures in 21,900,000 random profiles of the 219 pure n = 4 cores (12 cores), against 20 for the default rule on the same profiles.

**Where it breaks (smallest found: n = 4, m = 7).** Agents and values:
- agent 0: goods 0:3, 1:6, 2:10, 3:8;
- agent 1: goods 0:2, 2:8, 5:4, 6:3;
- agent 2: goods 1:4, 4:2, 5:5, 6:8;
- agent 3: goods 3:4, 4:3, 5:2, 6:8.

`-DALT` makes 5 single-agent rebundles and reaches Y = {2} | {0, 5} | {6} | {3, 4} with U = {1}. (The default rule also fails on this profile, at the same final state: line 2 of `results/k4_ls4_4_sample.log`.)
- No single-agent rebundle, rotation or exchange cycle improves Y.
- No complete EFX₀ allocation extends Y.

Y is *not* a dead end. Coalition moves (three agents or more re-dividing their bundles) still improve it, and complete EFX₀ allocations weakly better for everyone exist. So a richer move set would continue here; the default and alternative rules both lack a proof that such states are avoided.

Reproduce: `python3 k4/ls4_attempts.py` (independent replay of the 5 steps and of the claims). The failing run: `python3 k4/ls4alg_run.py results/k4_certs_4_pure.json.gz --sample=100000 --defs=-DALT`.
