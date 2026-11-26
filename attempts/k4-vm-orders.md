# Canonical starts and stripping: fair or rank-maximal SD outcomes, and V-M's EFX output stripped (k = 4)

Workstream proof/k4-vm (`k4/vm.md` §6.3). V-M's rank-greedy matching is a bad start for EFX₀
(`attempts/k4-vm-skeleton.md`). These approaches keep a canonical start or a canonical repair, so that no search over
orders is needed. Each fails.

## 1. Choose the SD outcome by its rank vector

Every serial-dictatorship outcome Y has a rank vector: the rank of Y_i in i's ranking, or 5 for no good.
- **fair**: lexicographically fewest agents with no good, then with rank 4, rank 3, rank 2 (leximin on ranks).
- **rmax**: lexicographically most agents with rank 1, then rank 2, and so on (rank-maximal; V-M's greedy approximates
  it).

Then the repair runs from the selected outcome: Phase III with F2, then F1 with rotation, then F3
(`k4/vm/vm0_fair.py`, `results/k4_vm/vm0_fair_screen.log`).

| rule | some selected outcome extends | repair succeeds from some selected outcome | from every selected outcome |
|---|---|---|---|
| V-M's matchings | 147 / 168 | 154 | 120 |
| rmax | 154 | 162 | 131 |
| fair | 163 | 165 | 141 |

Fair is the best of the three and still fails. The smallest failure has n = 3, m = 5 (`induct-g-r2`):

| agent | ranking (good: value) |
|---|---|
| 0 | 3: 7 > 4: 6 > 0: 5 > 1: 3 |
| 1 | 4: 4 > 3: 3 > 2: 2 |
| 2 | 4: 4 > 3: 3 > 2: 2 |

The four SD outcomes:
- (3, 2, 4) and (3, 4, 2), rank vectors (1, 3, 1) and (1, 1, 3), are fair-best and V-M's. Neither extends.
- (0, 3, 4) and (0, 4, 3), rank vectors (3, 2, 1) and (3, 1, 2), extend. They are exactly the outcomes in which
  agent 0 picks last.

Every EFX₀ allocation gives agent 0 the pair {0, 1} (8 > 7) or {0, 1, 2}. It is an upper set of goods nobody else
values, and leximin on ranks prefers giving agent 0 its top.

So no rule that only looks at ranks can see it. What the extending orders share is that the agent owning a private
upper set goes last, as in peeling rule R2 (L2) but without R2's robustness condition. The same holds in the other
two fair failures, `lb4-no-rotation-n3m5` and `nsw-local-n3m5`. In the latter the upper set {1, 3} of agent 0 is not
private, so "private" is not the whole rule either.

## 2. F5: run V-M to an EFX allocation, strip the zero goods, refill

Run V-M to its complete *ordinary* EFX allocation. While some agent i envies a bundle X_j that contains a good z with
v_i(z) = 0, remove z. Then re-place the stripped goods by F1 with rotation (`vmlib.vm_strip_run`,
`results/k4_vm/vm_strip_screen.log`). This is the only repair tried whose steps lower values.

| variant | some run EFX₀ (screen, 168) | every run |
|---|---|---|
| strip, no rotation | 146 | 84 |
| strip + rotation (stripped good chosen freely) | 154 | 88 |
| strip + rotation, first violation stripped | 154 | 88 |

- The 14 failures are V-M's matching-stage failures, smallest `c4-exposure-nonleader-n3m5` (n = 3, m = 5).
  Stripping removes the goods that hurt, but it never makes agent 0 give up its top for its upper set. So it does no
  better than F1–F3 with rotation (154).
- Stripping zero goods can also leave a violation by a *positive* good, which is not a zero-good violation (33 runs).
  F5 then has nothing to strip.

Reproduce:
- `python3 attempts/k4_vm_orders.py`: an independent replay of §1's facts on `induct-g-r2`;
- `python3 k4/vm/vm0_fair.py screen`;
- `python3 k4/vm/vm_strip_test.py screen`.
