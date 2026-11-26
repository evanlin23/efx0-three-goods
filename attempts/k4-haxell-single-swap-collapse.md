# Haxell/AKS alternating trees with single-move collapses: they get stuck at n = 2

Workstream `proof/k4-haxell` (`k4/haxell.md` §2–§3).

**Approach.** Translate the alternating trees of Haxell's hypergraph Hall theorem, in the form of Annamalai (arXiv
1509.07007, Def. 2.3–2.4, Lemma 5.1) and Annamalai–Kalaitzis–Svensson (arXiv 1409.0607, §3.5–§3.6), to EFX₀:
- the state is a partial EFX₀ allocation; the unmatched units are the unallocated goods (Model G of
  `k4/haxell/ht_lib.py`), or the unhappy agents of a complete allocation (Model A);
- an edge is a local move (a junk transfer, an improving chain of `k4/sdc.md` §29, a re-base), its blocking set the
  agents it would make unhappy (its victims);
- a layer holds the edges added for the newest blockers and their victims; an edge without victims is swapped in, and
  the layers above it are discarded, so the signature (−|X₁|, |Y₁|, …, ∞) falls lexicographically; values may drop at
  any step, so P1 (K4.SDC.P1) does not apply.

Every swap such a tree makes keeps every matched unit matched: in AKS a collapse is one player switching to an edge
that nothing blocks. The hope was that, as under Haxell's condition, every reachable state can be augmented.

**Why it fails.** EFX₀ blocking is not resource overlap. A blocker that vacates resources in Santa Claus hurts nobody,
but here the move that would protect a victim is often itself unsafe unless the parent move is made *at the same
time*. Then no single-move collapse order exists, and the tree is stuck although an EFX₀ allocation is two goods
away.

## Smallest failing configuration found

n = 2, m = 5 (screen instance c4x-n2m5-base-needs). Both agents value the shared goods 2, 3, 4 at 3, 4, 8; agent 0
also values its private good 0 at 2, and agent 1 its private good 1 at 2.

| state | agent 0 | agent 1 | pool |
|---|---|---|---|
| trap X | {0, 2} (5) | {1, 3} (6) | {4} |

- X is a partial EFX₀ allocation: agent 0 sees {1, 3} minus 1, worth 4 ≤ 5; agent 1 sees {0, 2} minus 0, worth 3 ≤ 6.
- Every single local move breaks EFX₀ or leads to the symmetric state ({0, 3}, {1, 2}): moving any one good (4 to
  either agent, 2 or 3 across), swapping any two goods (the pool included), or trading the bundles. Good 4 is worth 8,
  more than either holding, so whoever gets it is envied, and a lone middle good cannot compensate the other agent.
- Two transfers made together complete it: 4 to agent 0 and 2 to agent 1 give ({0, 4}, {1, 2, 3}) (agent 0: 10 ≥ 7;
  agent 1: 9 ≥ 8). The only other complete EFX₀ allocation is the mirror ({0, 2, 3}, {1, 4}).

So the graph G* of partial EFX₀ allocations under single local moves (pool never growing) has a component with no
complete allocation, already at n = 2. Any tree whose collapses are single local moves fails if it reaches X.

**Traps exist at k = 3 too, but later** (g834, n = 4, m = 7, found by the C census `k4/haxell/gstar.c` among 1,000 random
instances with three goods per agent, `results/k4_haxell/gstarc_gen_n4m7k3.log`; confirmed by the Python census):
agent 0 values goods 0, 5, 6 at 22, 9, 24; agent 1 values 2, 5, 6 at 9, 40, 29; agent 2 values 0, 4, 5 at 6, 40, 28;
agent 3 values 1, 3, 4 at 11, 20, 21. The state ({0, 3}, {1, 2}, {5}, {4}) with good 6 pooled is partial EFX₀ and a trap
(it and one other state are its whole component). Agent 1 holds only 9 but values 6 at 29, so every bundle that
receives 6 with another good is strongly envied by agent 1 or agent 0. Two moves at once (good 6 swaps through the pool with agent 0's
good 3, and agent 0's good 0 moves to agent 1) leave ({6}, {0, 1, 2}, {5}, {4}) with 3 pooled, from which single moves
complete; after the swap alone, agent 1 would see {0, 6} minus 0, worth 29 > 9. No k = 3 trap was found with n ≤ 3: every n = 2 instance on a value grid (472,860), and
random samples at n = 2, 3 (over 40,000).

**The tree reaches such dead ends from serial-dictatorship starts.** C127 (screen set, n = 4, m = 7), order
(0, 1, 3, 2): the picks are 2, 4, 5, 6. The tree's first two augmentations place goods 0 and 1 with agent 2, both
victim-free, giving ({2}, {4}, {0, 1, 5}, {6}) with good 3 in the pool. No single-good move keeps EFX₀ there (agents 0,
1, 3 hold picks that agent 2 or 3 wants, and good 3 next to agent 2's goods 0 and 5 is worth 11 > 8 to agent 0), and
neither does any chain or re-base (`k4/haxell/ht_bfs.py`). Two transfers together (0 to agent 0, 3 to agent 2) give
the complete EFX₀ allocation ({0, 2}, {4}, {1, 3, 5}, {6}). This C127 state is a dead end of the tree's catalogue, not of
G* (a swap or a bundle trade escapes it).

**Counts** (screen set, every order, n ≤ 5, 4,069 starts; logs in `results/k4_haxell/`):
- the literal tree: stuck from 101 starts in Model A (`tree_screen_TC.log`), 38 in Model G (`tree_screen_G.log`);
- the complete search over victim-free move sequences: 3 in Model A (one instance, one absorber; `bfs_screen_TC.log`),
  0 in Model G (`bfs_screen_G.log`). The tree's own choices walk into dead ends that the search avoids;
- G* traps (`gstar_*.log`): on 5 of 134 screen instances with n ≤ 4, m ≤ 8, 5 of 119 suite instances, 6 of 1,469
  random core profiles with n ≤ 3; on random instances, 9 of 3,000 (n = 2, m = 5, k = 4), 5 of 3,000 (n = 2, m = 5,
  every good relevant), none at k = 3 with n ≤ 3, and one at k = 3 with n = 4 (g834 above). None is a
  serial-dictatorship start.
- **No trap survives composite moves of two local moves** (radius 2), on any of these instances.

**What survives.** Collapsing a branch as one composite move (`k4/haxell/ht_ctree.py`, `k4/haxell.md` §3.3), and the
statement that G* with composite moves of radius 2 has no trap (`k4/haxell.md` §3.4).

**Reproduce:** `python3 attempts/k4_haxell_trap.py` (raw EFX₀ definition, no shared code): the n = 2 trap and the
k = 3 trap with their two-move escapes, and the C127 dead end reached from the serial-dictatorship picks.
