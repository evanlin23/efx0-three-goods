# Two absorbers instead of one (and instead of the rotation)

Workstream `proof/k3-simplify` (`proofs/k3_simple.md` §4).

**Idea 1.** Serial dictatorship gives everyone one good. The leftovers are then split between two absorbers instead
of one.

**Idea 2.** Run K3ALG up to its owner test. When r is not a valid owner (the bad case), do not rotate: let a second
free agent t absorb part of the leftovers, so that the goods protecting the exposed agents need no extra slot.

**Where both break.** In the failing instances the picks themselves are wrong, so no way of handing out the leftovers
works. In the smallest one, every EFX₀ allocation gives the contested top to a different agent than serial
dictatorship does. K3ALG's rotation changes the picks, which is what these instances need.

**Smallest failing configuration (idea 1)**, at n = 3, m = 5. Agent 0 ranks 0 ≻ 1 ≻ 2, agents 1 and 2 rank 0 ≻ 3 ≻ 1,
and good 4 is worthless. Serial dictatorship gives agent 0 good 0, agent 1 good 3 and agent 2 good 1, with
leftovers {2, 4}.
- Agent 2 holds its c, so it needs 0 and 3 alone. Agents 0 and 1 can therefore receive nothing.
- So 2 and 4 both go to agent 2, giving {1, 2, 4}. That bundle holds agent 0's b and c together, so agent 0 is
  unsafe.
- All 9 placements of the leftovers, to any agents, fail.
- The instance has 8 EFX₀ allocations, and none gives good 0 to agent 0.
- K3ALG rotates here: agent 1 takes 0, agent 2 takes 3, agent 0 takes {1, 2}, and good 4 goes to agent 2.

Counts for idea 1, with the best split over any two agents and agent order 0, …, n − 1: 270 of 3,600 profiles fail
at n = 3, m = 5; 816 of 14,400 at m = 6; 1,900 of 44,100 at m = 7.

**Idea 2, counts** (`k3/simplify/exp_two_owners.py`: exhaustive search over leftover placements with absorbers r and
t). A two-absorber completion of the same picks exists in:
- 0 of the 14 bad cases at n = 3;
- 40 of the 636 bad cases at n = 4 (every profile of every core);
- 44 of the 538 bad cases in a sample at n = 5.

The smallest bad case without one is the instance above, as a core: rankings (2, 0, 3), (1, 2, 4), (1, 2, 0), m = 5.

**The shape itself.** "At most two bundles with two or more goods" was never infeasible in these tests, with any
singletons, not only serial dictatorship's:
- every profile with n = 3, m ≤ 6;
- 860 random profiles with n = 4, 5 (`k3/simplify/exp_shape_two_absorbers.py`).

Whether that shape always exists is open. It does not give an algorithm, because the difficulty is choosing the
picks.

Reproduce:
- `python3 k3/simplify/exp_shapes.py index`
- `python3 k3/simplify/exp_two_owners.py 4`
- `python3 k3/simplify/exp_two_owners.py 5 300 5`
