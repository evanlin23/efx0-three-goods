# V-M's rank-greedy matching as the base of an EFX₀ allocation (k = 4)

Workstream proof/k4-vm (`k4/vm.md` §5). The approach: run Viswanathan–Mehta's Phases I–II and keep the one-good
matching they produce, then complete it to an EFX₀ allocation in any way at all. The completion is not restricted to
V-M's Phase III or its EFX graph. Under the main reading (`k4/vm.md` §3), these matchings are exactly the
serial-dictatorship outcomes of the rank-greedy orders (Lemma PO, `k4/vm.md` §2.1).

**It fails.** On 21 of the 168 screen instances, *no* resolution of the matchings' choices extends to an EFX₀
allocation (`results/k4_vm/vm_extend_screen_II.log`). On the suite the count is 21 of 164 (`vm_extend_suite_II.log`).
On random general 4-limited instances with n = 3 and m ≤ 6 it is 56 of 20,000, and on n = 2 it is 0 of 20,000
(`vm_extend_gen{3,2}_II.log`). Every one of these instances has an EFX₀ allocation.

## Smallest failing configuration: n = 3, m = 5 (a connected k = 4 core)

Screen instance `c4-exposure-nonleader-n3m5`; in the random runs no failure has n ≤ 2 or m ≤ 4.

| agent | ranking (good: value) |
|---|---|
| 0 | 3: 8 > 1: 6 > 4: 4 > 0: 3 |
| 1 | 4: 4 > 3: 3 > 2: 2 |
| 2 | 4: 4 > 3: 3 > 2: 2 |

- No agent strongly prefers its top (8 < 6 + 4, and 4 < 3 + 2), so Phase I does nothing.
- Step 1 of Phase II gives good 3 to agent 0 (nobody else's first choice) and good 4 to agent 1 or 2.
- The loser's second choice, 3, is gone, so step 3 gives it good 2.
- The matchings are ({3}, {4}, {2}) and ({3}, {2}, {4}).

The four EFX₀ allocations (brute force over all 3⁵ allocations) are ({0,1,2}, {3}, {4}), ({0,1,2}, {4}, {3}),
({0,1}, {2,3}, {4}) and ({0,1}, {4}, {2,3}). **None gives good 3 to agent 0.**

Why no completion works, by hand. After the matching, the holder of good 2 (value 2) envies both {3} and {4}. Goods 0
and 1 are valued only by agent 0, so they cannot join {3} or {4}: the holder of 2 would envy a bundle containing a good
worthless to it. They cannot both join {2} either: agent 0 would see {0, 1, 2} minus good 2 (worthless to it) worth
9 > 8. Splitting them, one into {2} and one into {3}, again puts a good worthless to the holder of 2 into a bundle it
envies.

Agent 0 has to give up its uncontested top for the pair {0, 1} worth 9 (an *upper set*), and V-M's matching never
does that.

Reproduce:
- `python3 attempts/k4_vm_skeleton.py`: an independent replay from the definitions, sharing no code with `k4/vm/`;
- `python3 k4/vm/vm_extend.py screen --stop=II`;
- `python3 k4/vm/vm_smallest.py screen`.

What survives: SD-C (K4.SDC) does not claim that every order works. This instance has other SD orders whose picks
extend, e.g. agents 1 and 2 first. So the repair must change the order or let agents take upper sets (`k4/vm.md` §6,
F4).
