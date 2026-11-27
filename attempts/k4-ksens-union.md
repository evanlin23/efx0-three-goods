# Two absorbers from a disjoint union (k = 4): fails

Workstream `proof/k4-ksens` (`k4/ksens.md` §5). Idea: OC₁ allows one absorber for the whole instance, so two disjoint
copies of an instance that needs its own absorber after every chain should need two, refuting OC₁ at k = 4 with
n = 6, beyond the n ≤ 5 data of `k4/sdc.md` §29.

The copy: K4.SDC.DICH (`k4/sdc.md` §29), the n = 3 instance on which the picks of order (0, 2, 1) have no
one-absorber completion and no chain removes the need for an absorber.

**Why it fails.** An absorber can take junk from the other component.
- Agents of one component value nothing in the other, so a foreign absorber's bundle meets the other copy's agents
  only in that junk.
- It threatens them only if it contains one of their danger sets. Here the second copy's junk {7, 11, 12} contains
  none.

The union satisfies OC₁. Agent 0 trades its pick for {0, 2}, agent 1 takes good 3, and agent 2 absorbs its own junk
{4, 5} and the other copy's {7, 11, 12}.

**Smallest failing configuration:** the union itself, n = 6, m = 14, order (0, 2, 1, 3, 5, 4). The picks have no
one-absorber completion; one chain repairs them (`results/k4_ksens/union.log`).

**What would be needed instead:** junk that no foreign bundle can take, e.g. a shared pool in which every pair is a
danger set. That is the mechanism of PW5 (`k4/ksens.md` §1). It works at k = 5 and, by the leftover count of
`k4/ksens.md` §2, not at k = 4.

Reproduce: `python3 k4/ksens/union.py`.
