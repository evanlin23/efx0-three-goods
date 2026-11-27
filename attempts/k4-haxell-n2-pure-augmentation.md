# Pure augmentation at n = 2 (Claim A2): false even with strict values

Workstream `proof/k4-haxell` (`k4/haxell.md` §6, "The n = 2 case").

**The idea.** For a proof of W^sub at n = 2, one would like the measure to be unnecessary. Claim A2: with two agents and
strict values, every partial EFX₀ allocation with a nonempty pool has a composite of at most two moves (§6: set
transfers, swaps, the trade) that reaches a partial EFX₀ allocation with a smaller pool. With ties it was already known
to fail (`results/k4_haxell/n2aug_grid_k4.log`). Random strict states supported it: no failure in 1,067,080 of them
(`n2claim_*.log`).

**Why it fails.** Pool-shrinking is ordinal: it depends only on each agent's order type. So it was checked on every
strict type profile with at most four valued goods per agent and every good valued by someone
(`k4/haxell/ht_n2types.py`, 45,999 classes up to interchangeable goods; `results/k4_haxell/n2types_k4.log`). It fails
in **20 classes**, one state each, all of one shape:
- m = 5, and each agent holds two goods;
- one of each agent's goods is *misplaced*: worthless to its holder, valued by the other agent;
- one good, valued highly by both agents, is pooled.

The random tests missed these classes because their types are rare in random values.

## Smallest failing configuration

| good | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| A | 3 | 2 | 4 | 8 | 0 |
| B | 0 | 4 | 2 | 8 | 3 |

The state is ({2, 4}, {0, 1}) with good 3 pooled. The values are strict, every good is valued by someone, and each
agent values four goods.
- No composite of at most two moves gives a partial EFX₀ allocation with a smaller pool (88 allocations within two
  moves).
- Swapping goods 4 and 0 gives ({0, 2}, {1, 4}). It is partial EFX₀, and both agents gain 3. So W^sub, L^sub, and the
  lemma with any measure that rises when both agents gain, all have a step here.

**What survives.** At all 20 failing states, the swap of the two misplaced goods keeps EFX₀ and raises both agents.
That is type-determined, so it holds for every realization of the types. This gives the computer-verified n = 2
statement in `k4/haxell.md` §6 (Theorem N2). The measure is needed at n = 2, but only for this one shape.

**Reproduce:** `python3 attempts/k4_haxell_n2aug.py` (raw EFX₀ definition, no shared code; under a second).
