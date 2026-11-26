# Conjecture LR (static parking): LSS-ROT's final state on a linear instance completes by parking

Workstream `proof/k4-girth` (`k4/girth.md` §4). **Approach:** on a linear instance run LSS-ROT (LSS's Algorithm 2 with
the Pareto-improving F5/F6 rotations) for *any* labeling, then give every leftover good to an agent that is non-envied
in that final state (static parking, exhaustive search).

**Result: false.** It survived 531,400 runs on random linear instances (`results/k4_girth_lssrot_d4.log`), 133,800 runs on
every linear k = 4 core with n ≤ 6 (`results/k4_girth_lssrot_cores.log`) and the adversarial climbs, but the search
grown around the trap of `attempts/k4-girth-linear-pl.md` found (`results/k4_girth_lssrot_trap.log`, seed 41) a linear
instance, n = 4, m = 8: K₄ plus one private good each for agents 0 and 3. Agent: {good: value}:

    0: {0: 23, 1: 28, 4: 8, 7: 22}    1: {0: 19, 2: 25, 3: 12}    2: {1: 28, 3: 8, 6: 24}    3: {2: 29, 4: 11, 5: 5, 6: 13}

(goods 0 = {0,1}, 1 = {0,2}, 2 = {1,3}, 3 = {1,2}, 4 = {0,3}, 6 = {2,3}; 5 and 7 private). With labels (1, 2, 3, 0)
(agent 3 is vertex 0) LSS-ROT stops at X = ({0}, {2}, {1}, {6}), values (23, 25, 28, 13), leftovers {3, 4, 5, 7}; agents 1
and 2 are envied (by 3 and 0), and no assignment of the four leftovers to agents 0 and 3 is EFX₀. 6 of the 24 labelings
end in such a state. The instance has EFX₀ allocations, and 18 labelings complete statically.

**What survives:** *dynamic* parking (receivers non-envied at the moment they receive) completes all 24 labelings. Here:
agent 0 takes good 3 (now envied by agent 1, but only with slack: 31 − 12 ≤ 25); agent 3 takes goods 4 and 5, reaching
29 = v_3(good 2), so it stops envying agent 1; agent 1, now non-envied, takes agent 0's private good 7 (agent 0 sees
22 ≤ 23). Result X = ({0, 3}, {2, 7}, {1}, {4, 5, 6}). Static parking cannot do this, because agent 1 is envied in the
state LSS-ROT stops in. So the conjecture is restated with dynamic parking (Conjecture LR-dyn, `k4/girth.md` §4), and
Conjecture DYN (some labeling) holds here.

**Reproduce:** `python3 attempts/k4_girth_attempts.py` (part 6).
