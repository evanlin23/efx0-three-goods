# "Every Pareto-maximal partial EFX₀ orientation of a linear instance satisfies Lemma PARK's hypothesis"

Workstream `proof/k4-girth` (`k4/girth.md` §4). **Approach:** in a linear hypergraph (two agents share at most one good),
take a partial EFX₀ orientation whose value vector is Pareto-maximal among all partial EFX₀ orientations; hope that
every leftover good has a common safe vertex (CFKS's Lemma 13 condition), so that Lemma PARK completes it.

**Result: false**, already for graphs. Smallest counterexample found (n = 4, m = 5; a graph, K₄ minus an edge),
agent: {good: value}:

    0: {0: 12, 3: 11}    1: {0: 16, 2: 15, 4: 15}    2: {1: 13, 3: 12, 4: 12}    3: {1: 11, 2: 10}

The state X = ({3}, {0}, {1}, {2}), good 4 = {1, 2} unallocated, value vector (11, 16, 13, 10), is Pareto-maximal.
Agents 1 and 2 are envied (by 0 and 3); S_1 = {0}, S_2 = {3}: agent 0 holds good 3, which agent 2 values
(12 + 12 > 13), and agent 3 holds good 2, which agent 1 values (15 + 15 > 16). This is exactly the second scenario of
CFKS's Lemma 11 (r receives (r, j) and s receives (s, i)). The state is completable: give good 4 to agent 0. Agent 2
values both goods of {3, 4} and 13 ≥ max(12, 12) (Lemma SLACK, `k4/girth.md` §4).

Over 100,000 Pareto-maximal states of random linear instances (n ≤ 7, degree ≤ 4 and ≤ 6) only 15 fail PARK, and every
one of them is completed by PARK plus slack absorbers (`results/k4_girth_linear_pm_*.log`). All potentials tested
(welfare, leximin, Nash welfare, Pareto-maximal + most non-envied, Pareto-maximal + welfare) had every maximum satisfy
PARK.

**Reproduce:** `python3 attempts/k4_girth_attempts.py` (part 2).
