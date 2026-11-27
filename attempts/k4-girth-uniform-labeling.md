# Attempt: one labeling per hypergraph (DYN with a structural labeling rule)

Workstream `proof/k4-girth` (k4/girth.md §6). REFUTED.

**Idea.** Conjecture DYN (k4/girth.md §5) lets the labeling (vertex 0 and the two orders) depend on the profile. A
proof would be much simpler if the labeling could be read off the hypergraph alone: for every k = 4 core hypergraph H
there is ONE labeling with which LSS's Algorithm 2 (G1 repair) followed by dynamic parking with envy-cycle rotation
completes on every strict profile of H.

**Exhaustive test** (`python3 k4/girth/dyncert.py 3 --family=uniform`, `results/k4_girth_dyncert_3_uniform.log`): for
each n = 3 core and each labeling, the covering of `dyncert.py` with that labeling alone, stopping at its first failing
class. True for 45 of the 51 n = 3 cores (for 43 of them labeling #0, vertex 0 = agent 0 with the default order, works
everywhere); false for 6 cores, all with three 4-good agents (m6#8, m6#13, m6#14, m6#17, m7#10, m7#11).

**Smallest failing configuration.** n = 3, m = 6, every pair of agents shares two goods and no good is private:
R_0 = {0, 1, 2, 3}, R_1 = {0, 1, 4, 5}, R_2 = {2, 3, 4, 5} (`results/k4_certs_3.json.gz`, m = 6, core 17). Two
strict core profiles:

| | agent 0 | agent 1 | agent 2 |
|---|---|---|---|
| P1 | 0: 2, 1: 3, 2: 4, 3: 8 | 0: 4, 1: 6, 4: 1, 5: 8 | 2: 2, 3: 8, 4: 7, 5: 4 |
| P2 | 0: 3, 1: 5, 2: 6, 3: 7 | 0: 1, 1: 8, 4: 4, 5: 6 | 2: 4, 3: 8, 4: 2, 5: 3 |

Writing a labeling as (label of agent 0, of agent 1, of agent 2): (0, 1, 2), (0, 2, 1) and (1, 0, 2) fail on P1
and complete P2; (2, 0, 1), (1, 2, 0) and (2, 1, 0) fail on P2 and complete P1. So the labeling must depend on the values, and DYN∃ (some labeling per
profile) is the right form.

**Reproduce** (independent of `dyncert.py`; uses `lss.py` with numeric values and checks strictness and balance):
```
python3 attempts/k4_girth_uniform.py
```
