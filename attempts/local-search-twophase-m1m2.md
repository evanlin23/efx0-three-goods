# Two-phase local search whose Phase 1 has only rebundles and champion paths (no augmented cycles)

Workstream `proof/local-search` (`proofs/local_search.md` §6.2, "The n = 6 failure without M3").

**Approach.** Phase 1 applies valued single-agent rebundles (M1) and champion paths (M2) to junk-free EFX₀ partial allocations until none applies. Phase 2 places the unallocated goods as junk into source bundles.

No failure occurs for any connected core with n ≤ 5: 5,751,498 stable states for n = 5 (`results/ls_twophase_2_5.log`).

**Where it breaks (n = 6, m = 9).** Over all 3,093 connected cores with n = 6 there are 707,475,902 stable states. Placement fails in exactly one core, core 687 of genbg's list, in 64 profiles (`results/ls_twophase_6_m1m2.log`).

The core has goods (1,6,7) (4,5,8) (0,1,5) (0,3,6) (2,3,5) (2,4,6). An example profile, as rankings (a, b, c): (1,6,7) (4,5,8) (0,1,5) (0,3,6) (2,3,5) (2,4,6).
- Y = {1} {4} {5} {0} {2} {6}, U = {3, 7, 8}.
- The sources are agent 2 ({5}) and agent 5 ({6}).
- Good 7 is dirty at agent 5, because {6, 7} is agent 0's bottom pair.
- Good 8 is dirty at agent 2, because {5, 8} is agent 1's bottom pair.
- Good 3 is dirty at both sources, because {3, 6} is agent 3's bottom pair and {3, 5} is agent 4's.
- By Lemma 7, good 3 must sit alone next to one source's good. Then 7 or 8 has nowhere to go.

The repair is the augmented envy cycle 0 → 5 → 1 → 2 → 0:
- agent 0 takes {6, 7};
- agent 5 takes {4};
- agent 1 takes {5, 8};
- agent 2 takes {1}.

This is move M3. Afterwards good 3 fits with agent 2, and {6,7} {5,8} {1,3} {0} {2} {4} is EFX₀. With M3 in Phase 1, core 687 has no failure (`results/ls_twophase_6.log`).

Reproduce: `echo "6 9 1 6 7 4 5 8 0 1 5 0 3 6 2 3 5 2 4 6" | <build>/ls_twophase -l 3`. Without -x the placement fails; with -x it does not. The driver builds the binary: `python src/local_search.py twophase 6 9 --flags="-l 3"`, which runs all n = 6, m = 9 cores.
