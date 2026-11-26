# Conjecture W (one-step welfare lemma with two moves): false at n = 2, k = 4

Workstream `proof/k4-haxell` (`k4/haxell.md` §6).

**The statement.** From every partial EFX₀ allocation with a nonempty pool, a composite of at most two moves leads to
a partial EFX₀ allocation with a smaller pool, or with the same pool and strictly larger welfare Σᵢ vᵢ(Xᵢ). A move
gives one good to another agent (a pooled good may be placed), swaps the holders of two goods (the pool counting as a
holder), or rotates the bundles along a cycle of agents. Since (|pool|, −welfare) is well-founded, W would give EFX₀
existence. It had no stuck state on about 48 million partial EFX₀ states: every set of §6, random instances up to
k = 7, B< and B> at n = 6, and the n = 2 grid at k ≤ 3.

**Why it fails.** An agent may have to give away all of its other goods at once. Both agents value a pooled good g
above everything else they could hold, so whoever receives g must receive it alone, and must give away its three
other goods. One swap through the pool removes one of them; the other two need two more moves. So the step needs
three moves (`n2w_grid_k4.log`: 576 of the 1,540,944 n = 2 grid instances with k ≤ 4 and values in {1, 2, 4, 7}
have such a state; welfare and leximin alike).

## Smallest failing configuration found

n = 2, m = 7, k = 4, strict values:
| agent | goods (value) |
|---|---|
| 0 | 0 (40), 1 (10), 2 (11), 3 (12) |
| 1 | 0 (70), 4 (10), 5 (40), 6 (11) |

The state ({1, 2, 3}, {4, 5, 6}) with good 0 pooled is partial EFX₀: neither agent values a good of the other's
bundle.
- Good 0 in a bundle of two or more goods is strongly envied by the other agent. Agent 1 can hold at most 61 without
  good 0, against 70. Agent 0 can hold at most 33, against 40.
- So good 0 must end up alone. Its receiver must lose all three of its other goods, and no two-move composite raises
  welfare either: no step within two moves.
- Within three moves there is a step: swap good 0 with agent 1's good 4 through the pool, then move goods 5 and 6 to
  agent 0. That gives ({1, 2, 3, 5, 6}, {0}) with good 4 pooled, welfare 103 > 94.
- If giving a set of goods to one agent counts as one move, two moves suffice: agent 1 gives {4, 5, 6} to agent 0 and
  takes good 0, giving the complete EFX₀ allocation ({1, …, 6}, {0}).

**At k = 5 the three-move form fails too** (W5: agent 0 values goods 0, 1, 2, 3, 4 at 50, 10, 11, 12, 13; agent 1
values goods 0, 5, 6, 7, 8 at 90, 10, 40, 11, 1; state ({1, 2, 3, 4}, {5, 6, 7, 8}) with good 0 pooled). The same
mechanism needs k − 1 single moves, so with plain moves the radius of the lemma must grow with k. This is a place
where k really enters.

**What survives** (`k4/haxell.md` §6):
- **W₃** (three moves) at k = 4: see `n2w_grid_k4_r3.log`.
- **W^sub** (two moves, a set transfer counting as one move): k-independent in form. It adds moves to W, so it holds
  wherever W held; on the n = 2, k ≤ 4 grid see `n2w_grid_k4_sub.log`.

**Reproduce:** `python3 attempts/k4_haxell_w.py` (raw EFX₀ definition, no shared code).
