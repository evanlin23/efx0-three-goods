# k = 4 Phase 2 by "clean" placement, ignoring values

Workstream `proof/k4-localsearch` (`k4/local_search4.md` §6).

**Approach.** A polynomial Phase 2 that looks only at structure, not values.
- A source s is *clean* for a pool good u if s does not value u and no unsatisfied valuer h ≠ s of u values a good of Y_s (Y_s ∩ R_h ≠ ∅). Here h is unsatisfied if v_h(Y_h) < v_h(R_h ∖ Y_h).
- Clean placements never conflict. So:
  - goods with a clean source go to one;
  - "dirty" goods, with no clean source, go alone to distinct sources where Y_s ∪ {u} is threat-free;
  - these sources receive nothing else.

This is LS2's Phase 2 read structurally.

**Counts** (single implementation, `k4/ls4.c -x -k`, eager order). The rule fails in 8,821 of the 304,901 stable states reached on 2,550,000 random n = 3 profiles. In every one of them a single dump works; that run had no stable state without one. The dump is allowed by the value slack v_h(Y_s ∩ R_h) + v_h(J ∩ R_h) ≤ v_h(Y_h), which can hold although h is unsatisfied.

**Where it breaks (smallest found: n = 3, m = 5).** Agents and values:
- agent 0: goods 0:1, 2:8, 3:6, 4:4;
- agent 1: goods 1:2, 2:4, 3:10, 4:7;
- agent 2: goods 2:4, 3:3, 4:2.

A stable state: Y = {2} | {3} | {4}, U = {0, 1}. No single-agent rebundle, rotation or exchange cycle improves it.
- The clean rule finds no placement.
- LS4's Phase 2 completes it: agent 2 takes both pool goods, giving {2} | {3} | {0, 1, 4}.

Reproduce: `python3 k4/ls4_attempts.py` (independent brute force: stability, the clean rule, and the dump-plus-solo placements). The failing states: `python3 k4/ls4_run.py results/k4_certs_3.json.gz --sample=20000 --flags="-x -k" --v` (lines NOSTRUCT).
