# One-phase local search with seven move types: stuck at n = 6

Workstream `proof/local-search` (`proofs/local_search.md` §6.1, Refutation 6.2).

**Approach.** Keep an arbitrary EFX₀ partial allocation of a core; junk (goods held by agents that do not value them) is part of the state. The potential is (sum of levels, number of allocated goods). Seven move types:
- E fill, S swap, R rotate, A add;
- U single-agent rebundle, using pool goods and goods other agents hold as junk;
- C champion along an envy path;
- X augmented envy cycle, where each agent on a cycle takes some of its own goods from the next bundle, the pool and junk.

With E, S, R, A, U, C alone, no EFX₀ partial state of any connected core with n ≤ 5 is stuck (`results/ls_allstates_2_5.log`).

**Where it breaks (n = 6, m = 9).** The core K with agent sets (1,6,7) (4,5,8) (0,1,5) (0,3,6) (2,3,5) (2,4,6), entry 562 of the (6, 9) list of `cores_nauty.py` (file names call it core687); goods 7, 8 are private.

Profile, as rankings (a, b, c): (1,6,7) (4,5,8) (1,5,0) (6,0,3) (5,2,3) (4,6,2).

From the empty allocation, the following moves each keep EFX₀ and raise the potential:
- E six times: goods 1, 4, 0, 6, 5, 2 to agents 0, 1, 2, 3, 4, 5;
- A: good 8 to agent 2;
- A: good 7 to agent 5.

They reach the state

  {1} {4} {0, 8} {6} {5} {2, 7}, pool {3},

which is EFX₀ and has no move of any of the seven types.

Why nothing works:
- Good 3 is the c of agents 3 and 4, which hold their tops 6 and 5.
- Adding 3 to agent 2's {0, 8} breaks agent 3 (its b 0 and c 3 would sit in a bundle of three goods).
- Adding 3 to agent 5's {2, 7} breaks agent 4 in the same way.
- Every singleton holds a good that somebody needs alone.

A complete EFX₀ allocation with the same levels exists: {1} {4} {0, 3} {6} {5} {2, 7, 8}. It moves the junk good 8 from agent 2 to agent 5, which no move above does.

**Counts.**
- On this core, over all profiles: 192 stuck states with E, S, R, A, U, C.
- 128 stuck states with X added (64 profiles). A champion move that may also take junk (K) removes none (`results/ls_allstates_core687.log`).
- All 128 are reachable from the empty allocation under E, S, R, A, U, C, X (`results/ls_reach_core687.log`).
- Other n = 6 cores were not searched in this mode (40 million partial allocations per core at m = 9).

**Lesson.** Junk placement has to be revisable. Hence the two-phase version: drop all junk, improve the valued part, and place the junk afresh at the end. That version is Algorithm LS2 (`proofs/local_search.md` §4), which never gets stuck (Theorem C).

Reproduce:
- `python src/local_search.py stuck6` (independent Python replay: every move valid and raising the potential, final state stuck)
- `python src/local_search.py allstates 6 9 --flags="-O -m ESRAUCX -l 5"` restricted to core K: `echo "6 9 1 6 7 4 5 8 0 1 5 0 3 6 2 3 5 2 4 6" | ls_check -O -m ESRAUCX`
