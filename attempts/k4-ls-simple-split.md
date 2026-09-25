# k = 4 Phase 2 by the simplest polynomial split

Workstream `proof/k4-localsearch` (`k4/local_search4.md` §7).

**Approach.** A polynomial version of LS4's Phase 2 (c), the dump plus solo goods:
- for each source s*, the dump keeps every pool good that is individually harmless there (Y_{s*} ∪ {u} threat-free, u not valued by s*);
- the other pool goods are matched, one each, to distinct other sources where they are threat-free alone.

This is one bipartite matching per candidate dump.

**Counts** (single implementation, `k4/ls4.c -x -k`, counter dm1). In states where no single dump works but a dump plus solo goods does:
- 0 of the 79 such states on 1,640,400 random n = 5 profiles (two 4-good agents, 300 per core) are completed by the simple split.
- The instance below comes from a run on the n = 4 cores with three or four 4-good agents (20,000 random profiles per core), which printed 46 such states.

The reason is Lemma 6 of `k4/local_search4.md`: pool goods that are harmless one at a time at the dump can be harmful together (pair constraints).

**Where it breaks (smallest found: n = 4, m = 6).** Agents and values:
- agent 0: goods 0:1, 1:6, 3:8, 4:4;
- agent 1: goods 1:3, 2:2, 5:4;
- agent 2: goods 2:5, 3:3, 4:6, 5:7;
- agent 3: goods 2:7, 3:10, 4:4, 5:2.

A stable state: Y = {3} | {5} | {4} | {2}, U = {0, 1}. No single-agent rebundle, rotation or exchange cycle improves it.
- No single dump works.
- The simple split fails.
- Dump-plus-solo placements exist, for example {3} | {5} | {0, 4} | {1, 2}: each pool good alone at a different source.

At n = 3 the eager engine never needed a split.

Reproduce: `python3 k4/ls4_attempts.py` (independent brute force). The states: `python3 k4/ls4_run.py results/k4_certs_4_pure.json.gz results/k4_certs_4_n4_3.json.gz --sample=20000 --flags="-x -k" --v` (lines DM1FAIL).
