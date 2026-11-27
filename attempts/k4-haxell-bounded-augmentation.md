# Bounded one-step augmentation of partial EFX₀ allocations (AUG_r): false for r ≤ 3

Workstream `proof/k4-haxell` (`k4/haxell.md` §3.5).

**Approach.** The simplest possible non-value proof of EFX₀ existence: show that every partial EFX₀ allocation with a
nonempty pool becomes a partial EFX₀ allocation with a smaller pool after one composite of at most r local moves
(move one good to an agent; swap the holders of two goods, the pool counting as a holder; trade two bundles; the
intermediate states need not be EFX₀, and nothing returns to the pool). Call this AUG_r. Induction on the pool from the
empty allocation would then give a complete EFX₀ allocation, with no potential and no tree. An alternating tree whose
collapse is a single composite of r moves needs exactly AUG_r.

**Why it fails.** Some states need several moves at once before any pooled good can be placed, already at n = 2
and k = 3.
| data (`results/k4_haxell/mrad_*.log`) | states needing 3 moves | needing 4 |
|---|---|---|
| 3,000 random instances, n = 2, m = 5, k = 3 | 198 | 0 |
| 3,000 random instances, n = 2, m = 5, k = 4 | 56 | 0 |
| 3,000 random instances, n = 2, m = 5, every good relevant | 11 | 0 |
| 800 random instances, n = 3, m = 6, k = 3 | 1,172 | 0 |
| 800 random instances, n = 3, m = 6, k = 4 | 4,760 | 1 |
| screen set, n ≤ 3, m ≤ 7 | 355 | 7 (c4min-tlam-n3-m6, c4x-n3m6-onefour-a, induct-pot-nash, …) |

(Every state whose Hamming radius exceeds 2 was checked; a Hamming radius of 2 means two single-good moves suffice.)

## Smallest failing configuration found

**AUG₂, at k = 3** (g12, n = 2, m = 5, from `gen:3000:13:2:5:3`): agent 0 values goods 0, 2, 3 at 12, 39, 7; agent 1
values 1, 2, 4 at 4, 35, 10. The state ({0, 1}, {3, 4}) with good 2 unallocated is partial EFX₀ (agent 0: 12 ≥ 7;
agent 1: 10 ≥ 4). Good 2 is worth more than either holding. The only complete EFX₀ allocations are ({2}, {0, 1, 3, 4})
and ({0, 1, 3, 4}, {2}) (brute force): one agent must give away both its goods and take good 2 alone, three moves at
once. (k = 3 has no
trap of G₁, so a path of single moves through partial EFX₀ allocations exists here too.)

**AUG₃, at k = 4**

(g372, n = 3, m = 6, from `gen:800:34:3:6:4`):

| agent | goods (value) |
|---|---|
| 0 | 1 (4), 2 (35), 3 (16), 5 (10) |
| 1 | 0 (21), 2 (18), 3 (14), 4 (9) |
| 2 | 0 (39), 2 (34), 3 (18), 5 (9) |

The state ({1, 4, 5}, {0}, {3}) with good 2 unallocated is partial EFX₀. No composite of 1, 2 or 3 local moves gives a
partial EFX₀ allocation with an empty pool; a composite of 4 gives ({2, 5}, {3, 4}, {0, 1}).

**It is not a trap.** Two steps through partial EFX₀ allocations, each a composite of two moves, complete it:
({1, 4, 5}, {0}, {3}) with 2 pooled → ({2}, {1, 4, 5}, {3}) with 0 pooled (agents 0 and 1 trade, and good 2 swaps with
good 0 through the pool) → ({2}, {1, 3, 4}, {0, 5}). So augmentation has to be a *sequence* of local steps, kept
inside the partial EFX₀ allocations, which is what an alternating tree organizes. No state of any instance tested is
a trap for radius-2 steps (`k4/haxell.md` §3.4, CONN₂).

**Reproduce:** `python3 attempts/k4_haxell_aug.py` (raw EFX₀ definition, no shared code): no augmentation within 3
moves, one with 4, and the two-step path above.
