# Pareto-improving moves with a potential (a local-search proof of C₄)

**Idea.** Replace LB₄ʳ's bounded nested rotations by a potential argument: allow *upgrades* (a free agent adds one of
its junk goods to its base) and *rotations in which the rotated agent strictly gains* (v_k(O) > v_k(B_k)). Every
such move raises every participant's value, so Σ_i v_i(B_i) rises and the search terminates. If every reachable state
where no owner is valid admitted such a move, the construction could never fail.

**Evidence for it.** From the Phase 1 state, some sequence of these moves reaches a state with a valid owner on every
sampled profile (200,000 random n = 3 runs, 30,000 n = 4 runs; paths of up to 4 moves at n = 3 and 5 at n = 4), and on
all 548 n = 3 runs where no owner and no single rotation works (with no upgrades), a path of at most 2 moves exists.

**Where it breaks: dead ends exist** (n = 3, m = 6). Agents 0 = {0, 1, 2, 3} with values (8, 6, 4, 1),
1 = {0, 1, 4, 5} with (4, 2, 8, 5), 2 = {2, 3, 4, 5} with (4, 6, 8, 3); insertion choices (2, 6, 0), no upgrades in
Phase 1: agent 2 takes 4; agent 1 (lost 4) takes 5; agent 0 is inserted in a second block and takes its top 0. Of the
14 states reachable by these moves, 7 have a valid owner and 1 is a dead end: after the upgrades "agent 1 adds 1" and
"agent 0 adds 3" no owner is valid and no move applies (junk {2}, ω = 1; agent 1 still needs 4). So a proof along these
lines needs a rule that avoids dead ends, as for LS4 (`k4/local_search4.md`), and the 60,000 sampled n = 3 runs have
dead ends in 99 of 1,484 runs that need a move.

**Smallest failing configuration**: the one above (n = 3, m = 6).
Reproduce: `python3 attempts/k4_c4_attempts.py pareto-moves`.
