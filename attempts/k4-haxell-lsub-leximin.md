# L^sub (the two-move set-move lemma with leximin): false at n = 4, k = 4

Workstream `proof/k4-haxell` (`k4/haxell.md` §6). Companion of `attempts/k4-haxell-wsub-welfare.md`.

**The statement.** The moves are those of W^sub ("W^sub stated precisely", `k4/haxell.md` §6): give a nonempty set of
one holder's goods to an agent; swap two goods' holders, the pool counting as a holder; rotate bundles along a cycle
of agents. The measure is **leximin**: λ(X) is the vector of the agents' values vᵢ(Xᵢ), sorted increasingly and
compared lexicographically. Lemma L^sub: from every partial EFX₀ allocation with a nonempty pool, at most two moves
reach a partial EFX₀ allocation with a smaller pool, or with the same pool and a larger λ.

L^sub was proposed when W^sub with welfare failed, because it had a step at all 36 welfare failures. It is false too.

## Smallest failing configuration found

n = 4, m = 7. This is a k = 4 core (`k4/search4.py`): agent 3 has one private good. Every agent's values are strict
and balanced.
| agent | goods (value) |
|---|---|
| 0 | 3 (30), 4 (20), 5 (55), 6 (57) |
| 1 | 1 (31), 3 (12), 4 (5), 5 (39) |
| 2 | 0 (44), 1 (32), 3 (29) |
| 3 | 0 (60), 1 (31), 2 (7), 6 (43) |

The state is ({2, 3, 4}, {5}, {0}, {6}) with good 1 pooled. Own values are 50, 39, 44, 43, so λ = [39, 43, 44, 50].
Agent 0 holds good 2, which it values at 0.
- *Every placement of good 1 is blocked by strong envy* (τ against own value):
  - at agent 0 by agents 1 and 2 (48 > 39, 61 > 44);
  - at agent 1 by agent 0 (55 > 50);
  - at agent 2 by agent 3 (60 > 43);
  - at agent 3 by agent 0 (57 > 50).
- *No composite of at most two moves raises λ or shrinks the pool* among the 1,557 allocations within two moves. This
  was checked by `gstar_measure.c` and by the script below.
- *Other forms do have a step here.*
  - **Welfare** within two moves: 11 steps, e.g. ({2, 4, 6}, {5}, {3}, {0}) with good 1 pooled. Welfare goes from 176
    to 205, but the least value falls from 39 to 29, so leximin rejects it.
  - **Three moves**: leximin has 18 steps, single-good or set moves alike.

**How it was found.** The leximin climb (`k4/haxell/ht_wclimb.py MEASURE=2`) was started from the first W^sub
failure (`results/k4_haxell/lclimb_seed1_n4m7k4.log`).

**What it means.**
- At n = 4, k = 4, **neither welfare nor leximin supports a two-move lemma**, even with set moves. The two fail at
  different states.
- Three moves give a step at all 37 known failures, for both measures and for single-good moves as well as set moves.
  So the candidates move to three moves.
- With single-good moves, three moves already fail at k = 5 (W5, `attempts/k4-haxell-conjecture-w.md`). The
  k-independent candidate is therefore **three set moves** (with welfare or with leximin).
- The radius had to grow from two, which sufficed on every n ≤ 3 instance tested, to three at n = 4. That is a
  warning: it may keep growing with n.

**Reproduce:** `python3 attempts/k4_haxell_wsub.py` (both witnesses; raw EFX₀ definition, no shared code; about two
seconds).
