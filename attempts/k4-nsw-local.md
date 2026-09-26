# Attempt: Nash social welfare as a local potential for LB₄ʳ's rotations (compute/k4-nsw)

**Statement tried (the local form).** Run LB₄ʳ's Phase 1 with index insertion, then one upgrade policy (`k4/lb4.md`
§5). Call a state *stuck* if no owner (or no owner at all, when ω ≤ 0) gives a completion satisfying (OC₄), with the
owner's needs taken from its bundle. The lemma tried: in every stuck state reached this way, some RotStep strictly
raises the potential Φ. A RotStep is a frozen start, a need chain and a set O, with LB₄ʳ's validity checks. The
potential is Φ = (z, Π v_i(B_i)): z is the number of agents with a nonempty base, the product runs over those agents,
and pairs are compared lexicographically. The lemma would make "rotate while Φ grows" terminate with an output, as
Nash social welfare does for the rankpath shifts of Kaviani et al. (arXiv 2407.05139 §7, per `proofs/pq_bounded.md`;
[unverified here]).

**It fails at n = 3, m = 5.** Take the pure core with agents {0, 1, 3, 4}, {0, 2, 3, 4} and {1, 2, 3, 4}, and these
values:
- agent 0: 0:8, 1:4, 3:5, 4:6;
- agent 1: 0:10, 2:3, 3:4, 4:8;
- agent 2: 1:2, 2:3, 3:4, 4:8.

The run, with policy u1 (need-shrinking; no upgrade applies):
- **Phase 1** gives bases 0:{0}, 1:{4}, 2:{3}, so Φ = (3, 8·8·4 = 256).
- **Move 1:** the chain (1, 2) with O = {2, 3}, which raises Φ.
- **Move 2:** the chain (2, 1) with O = {1, 2, 3}, reaching the state S: bases 0:{0}, 1:{4}, 2:{1, 2, 3} (agent 2
  rotated), no junk, Φ = (3, 8·8·9 = 576).

S is stuck. Agent 2's base has three goods, so agent 2 must be the owner, and that completion fails (OC₄). S has
exactly one RotStep successor, and its Φ is (3, 540) < (3, 576). So no rotation raises Φ at S, and the local form
fails. The same dead state is reached under policies u2 (envy-free) and u0 (none).

**What survives on this profile (the existence form).** From Phase 1, other Φ-increasing paths reach an output. The
steepest-ascent walk (largest Φ first) succeeds after one rotation, as does the search over all Φ-increasing paths.
The first-improvement walk, however, dead-ends under all three policies. On every profile with n ≤ 3, some
Φ-increasing path reaches an output (`results/k4_nsw_n23_N5P0.log`). But the walks can get stuck:

| Walk | Profiles with n = 3 where all three policies get stuck | Of which with a stuck state that has rotations |
|---|---|---|
| Steepest (`k4/lb4_nsw.c -N1`) | 478,880 | 33,480 |
| First-improvement (`-N2`) | 30,726 | 8,519 |

The other stuck states have no valid rotation at all. Both counts are out of 299,837,376 profiles
(`results/k4_nsw_n23_N1P0.log`, `results/k4_nsw_n23_N2P0.log`). So a proof cannot take any Φ-increasing rotation; it
must choose which one, or use Φ only in the existence form.

**Smallest.** The census `k4/lb4_nsw.c -N6` (`results/k4_nsw_census_n23.log`) visits every state reachable from Phase 1
by strictly Φ-increasing moves through states without an output. It flags a profile if one of those states has no
output, has a RotStep, and has none that raises Φ. Its counts:
- n = 2: 0 of 189,216 profiles;
- n = 3, m = 4: 0 of 24,406,272;
- n = 3, m = 5: 46,992 of 49,813,056, under each policy.

So n = 3, m = 5, as here, is the smallest size. The census reproduces the counts of the #40 reviewer's own run.

**Checked twice, independently.**
1. `k4/lb4_nsw.c` (LB₄ʳ of `k4/lb4.c`, 64-bit, plus the NSW walk): `-N2` stops at S under each policy.
2. `k4/nsw_verify.py` runs on `k4/c4_verify_H/lb4r.py` (on main since #33; git blob 6726d25), an independent
   transcription of LB₄ʳ from its Lean definition (PR #35, by the C₄ verifier). It explores every Φ-increasing path and finds S stuck (no output by SAT, one RotStep
   successor with smaller Φ). It also finds 2 reachable states with an output.

**Reproduce.**
```
printf "3 5\n4 0 1 3 4 1\n8 4 5 6\n4 0 2 3 4 1\n10 3 4 8\n4 1 2 3 4 1\n2 3 4 8\n" > p.txt
gcc -O2 -o lb4_nsw k4/lb4_nsw.c && ./lb4_nsw -i0 -w1 -c1 -N2 -P0 -v < p.txt      # DEADEND(no improving rotation) x 3
python3 k4/nsw_verify.py '[{"0":8,"1":4,"3":5,"4":6},{"0":10,"2":3,"3":4,"4":8},{"1":2,"2":3,"3":4,"4":8}]' shrink
```
The second command's log is `results/k4_nsw_local_verify.log`.
