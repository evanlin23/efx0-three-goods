# Attempt: some strictly NSW-increasing rotation path always reaches an output (compute/k4-nsw)

**Statement tried (the existence form, strict).** Run LB₄ʳ's Phase 1 with index insertion, then one upgrade policy
(`k4/lb4.md` §5). The claim tried: for some policy, some sequence of RotSteps, each strictly raising
Φ = (z, Π v_i(B_i)), reaches a state that has an output. Here z is the number of agents with a nonempty base, the
product runs over those agents, and pairs are compared lexicographically. The output is a completion satisfying (OC₄),
with the owner's needs from its bundle. This is weaker than the local form (`attempts/k4-nsw-local.md`, false at
n = 3). It holds on every profile with n ≤ 3 (exhaustive, `results/k4_nsw_n23_N5P0.log`).

**It fails at n = 4, m = 8** (three 4-good agents). The core has agents {0, 3, 5, 7}, {1, 4, 5, 6}, {2, 4, 6, 7} and
{3, 6, 7}. The values:
- agent 0: 0:2, 3:8, 5:4, 7:7;
- agent 1: 1:2, 4:8, 5:3, 6:4;
- agent 2: 2:2, 4:10, 6:6, 7:7;
- agent 3: 3:4, 6:3, 7:2.

Phase 1 (insertion order 0, 3, 1, 2) gives bases 0:{3}, 1:{4}, 2:{7}, 3:{6}, and Φ = (4, 8·8·7·3 = 1344). No upgrade
applies under any of the three policies, so all three start from this state. It has no output. It has 4 RotStep
successors, and none has a larger Φ: the best ties at (4, 1344). So no strictly increasing path leaves Phase 1.

A second instance (n = 4, m = 9) behaves the same way: every successor of its Phase 1 state ties or lowers Φ. The core
has agents {0, 4, 5, 6}, {1, 4, 6, 8}, {2, 5, 7, 8} and {3, 7, 8}. The values:
- agent 0: 0:3, 4:4, 5:10, 6:8;
- agent 1: 1:3, 4:2, 6:4, 8:8;
- agent 2: 2:1, 5:8, 7:6, 8:4;
- agent 3: 3:2, 7:3, 8:4.

These are the only two failures among 10,020,000 random draws of n = 4 profiles, 10,000 per core (with replacement)
(`results/k4_nsw_n4_N5P0.log`). Both have three 4-good agents. They are the smallest found; smaller m at n = 4 was
not searched exhaustively.

**What survives.**
- Bounded LB₄ʳ (`k4/lb4.c -i0 -u3 -r3 -w1 -c1`) succeeds on both: one rotation on the first, two on the second.
- The weak form succeeds on both, and on every sampled n = 4 profile and every n ≤ 3 profile
  (`results/k4_nsw_n4_N3P0.log`, `results/k4_nsw_n23_N3P0.log`). The weak form allows moves that keep Φ, visiting no
  state twice.
- So Φ must be refined by a tie-break that strictly increases on the equal-Φ moves. Tried, with the search over
  strictly increasing paths (`-N5`):
  - P4, the number of rotated agents, solves both;
  - P2, the number of goods in bases, and P3, leximin of the base values, solve only the first
    (`results/k4_nsw_n4_N5P*.log`).

**Checked twice, independently.**
1. `k4/lb4_nsw.c -N5` finds both profiles failing under all three policies.
2. `k4/nsw_verify.py` explores every Φ-increasing path in `k4/c4_verify_H/lb4r.py`'s model (on main since #33; git
   blob 6726d25), an independent transcription of the Lean definition (PR #35). Under each policy it finds only the Phase 1 state, with no output
   and no successor of larger Φ. It reports "existence form FAILS" 6 times (2 profiles × 3 policies,
   `results/k4_nsw_strict_verify.log`).

**Reproduce.**
```
printf "4 8\n4 0 3 5 7 1\n2 8 4 7\n4 1 4 5 6 1\n2 8 3 4\n4 2 4 6 7 1\n2 10 6 7\n3 3 6 7 1\n4 3 2\n" > p.txt
gcc -O2 -o lb4_nsw k4/lb4_nsw.c && ./lb4_nsw -i0 -w1 -c1 -N5 -P0 < p.txt   # all_policies_fail 1
./lb4_nsw -i0 -w1 -c1 -N3 -P0 < p.txt                                       # weak search: all_policies_fail 0
python3 k4/nsw_verify.py '[{"0":2,"3":8,"5":4,"7":7},{"1":2,"4":8,"5":3,"6":4},{"2":2,"4":10,"6":6,"7":7},{"3":4,"6":3,"7":2}]' shrink
```
