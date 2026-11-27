# W^sub with welfare (the one-step lemma with set moves): false at n = 4, k = 4

Workstream `proof/k4-haxell` (`k4/haxell.md` §6).

**The statement** ("W^sub stated precisely", `k4/haxell.md` §6). Let X be a partial EFX₀ allocation with a nonempty
pool. Then a composite of at most two moves reaches a partial EFX₀ allocation with a smaller pool, or with the same pool
and strictly larger welfare Σᵢ vᵢ(Xᵢ). The moves are:
- give a nonempty set of one holder's goods (an agent's, or pooled goods) to an agent;
- swap the holders of two goods, the pool counting as a holder;
- rotate the bundles along a cycle of two or more agents.

**What held before this.** It had no stuck state on:
- the whole n = 2 grid with k ≤ 4 (470.5 million states);
- the n = 3 grid with k ≤ 3 and m ≤ 5 (742 million);
- every type profile of the small n = 4 cores (two runs, 223.5 and 115.4 million states);
- the skewed random sets at k = 4–6.

## Smallest failing configuration found

n = 4, m = 7. Every agent values three or four goods, all values are strict (no two subsets of an agent's goods have
equal value) and balanced (each agent's largest value is less than the sum of the others). The relevant sets form a
k = 4 core in the sense of `k4/search4.py`: connected, and at most one private good per agent.
| agent | goods (value) |
|---|---|
| 0 | 4 (9), 5 (47), 6 (39) |
| 1 | 1 (8), 2 (3), 4 (2), 5 (4) |
| 2 | 0 (7), 1 (4), 3 (1), 5 (9) |
| 3 | 0 (38), 4 (7), 6 (32) |

The state is ({5}, {2, 3, 4}, {1}, {0}) with good 6 pooled; the own values are 47, 5, 4, 38 and the welfare is 94.

- *Every placement of good 6 is blocked by strong envy* (τ, the value of a bundle minus its least good, against the
  envier's own value):
  - at agent 0 by agent 2 (9 > 4: it wants good 5);
  - at agent 1 by agents 0 and 3 (48 > 47, 39 > 38);
  - at agent 2 by agent 1 (8 > 5);
  - at agent 3 by agent 2 (7 > 4).
- *No composite of at most two moves helps.* Among the 1,557 allocations within two moves, none is partial EFX₀ with
  an empty pool, and none has the same pool and welfare above 94. This was checked by the C checker (`gstar_measure.c`)
  and by two independent Python enumerations (`k4/haxell/ht_wexplain.py` and the script below).
- *Two repaired forms have steps here.*
  - **Leximin** in place of welfare: 19 steps. One is swapping good 6 for good 0 through the pool, then good 0 for
    good 1. That gives ({5}, {2, 3, 4}, {0}, {6}) with good 1 pooled. Welfare falls to 91, but the least value rises
    from 4 to 5 (leximin [4, 5, 38, 47] → [5, 7, 32, 47]).
  - **Three single-good moves** (W₃): 48 steps, e.g. the complete EFX₀ allocation ({3, 6}, {1, 2, 4}, {5}, {0}).

**How it was found.** The adversarial climb `k4/haxell/ht_wclimb.py` started from the tightest state of the
move-kind ablation (a state with exactly one W^sub step; `k4/haxell.md` §6). It found 36 failing instances, all with
this state shape (`results/k4_haxell/wclimb_tight_n4m7k4.log`). Of these, 33 are balanced cores and 17 are strict
balanced cores. This one was then shrunk by lowering values while keeping it a strict balanced core.

**What it means.** Welfare cannot be the measure of a two-move lemma, even with set moves, at n = 4 and k = 4. The two
repaired forms survive every one of the 36 failing instances:
- **W^sub with leximin** (k-independent in form);
- **W₃** (welfare, three single moves; refuted at k = 5 by W5, `attempts/k4-haxell-conjecture-w.md`).

The welfare evidence above stays valid for welfare at n ≤ 3 and on the small cores. The leximin form is being
re-tested on the same sets.

**Reproduce:** `python3 attempts/k4_haxell_wsub.py` (raw EFX₀ definition, no shared code; under a second).
