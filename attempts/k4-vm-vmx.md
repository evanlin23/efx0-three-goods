# Conjecture VMX: some run of VMˣ never gets stuck (k = 4)

Workstream proof/k4-vm (`k4/vm.md` §7). VMˣ runs:
1. V-M's Phases I–II;
2. Phase III with the EFX₀ filter F2;
3. a loop, while a valued good is unassigned: rotate envy cycles, then apply one F6x move (a pool upgrade, or a
   two-agent exchange with pool goods) or place a pool good where its bundle stays EFX₀-unenvied (F1);
4. junk by L3.

Every choice is free. VMX said that for every 4-limited instance some run ends EFX₀. Some run did end EFX₀ on every
instance of the screen set, the suite, SPECIAL, the logged profiles and 9,300 random instances (`k4/vm.md` §6.4).
**It is false.** Hill-climbing over strict profiles of certified cores (`k4/vm/vmx_climb.py`, minimizing the fraction
of successful runs) found two counterexamples:

| log | instance | runs | how confirmed |
|---|---|---|---|
| `results/k4_vm/vmx_climb_n3.log` | n = 3, m = 6 | 4, none EFX₀ | exhaustive |
| `vmx_climb_n4.log` | n = 4, m = 8 | 10, none EFX₀ | exhaustive |

The n = 5 climb (`vmx_climb_n5.log`) also reports fraction 0, but that is an artifact of its cap: its first 200 DFS
runs fail, while 2,255 of the first 3,000 succeed. It is not a counterexample.

## Smallest: n = 3, m = 6 (a connected k = 4 core, every agent with four goods)

| agent | ranking (good: value) |
|---|---|
| 0 | 5: 8 > 0: 4 > 1: 3 > 2: 2 |
| 1 | 5: 8 > 3: 7 > 1: 4 > 4: 2 |
| 2 | 5: 10 > 3: 8 > 2: 4 > 4: 3 |

- **Every EFX₀ allocation (10 of them, brute force) gives good 5 to agent 1 or agent 2, never to agent 0.** Agent 0
  takes its lower triple {0, 1, 2}, worth 9 > 8.
- **V-M:** agent 0 is the only agent that strongly prefers its top (8 > 4 + 3), so Phase I gives it good 5.
  - Agents 1 and 2 both claim good 3 at step 2. The loser takes its 3rd choice at step 3 (1 or 2).
  - Phase III gives the N₃ agent its 4th choice, good 4 (EFX₀-safe at that point).
  - The two states are ({5}, {3}, {2, 4}) and ({5}, {1, 4}, {3}).
- **From both, nothing moves.** The needed exchange gives good 5 to agent 2 and goods {2, 0, 1} to agent 0, or the
  same with agent 1. After it, agent 1 sees {4, 5} minus 4 (worth 2 to it) as 8 > 7, and symmetrically. Phase III's
  good 4 sits in the wrong bundle, and no F6x move returns it to the pool.
- The independent replay `attempts/k4_vm_vmx.py` searches a *superset* of VMˣ's moves breadth-first from both
  states: any rotation, any safe placement, any (also non-minimal) upgrade, any two-agent exchange with pool goods.
  It reaches only 3 states from each, none complete.

Two features of V-M meet here. Both are harmless for ordinary EFX (Theorem VM) and both are fatal for EFX₀:
- Phase I's priority for agents that strongly prefer their top. Agent 0's top beats its 2nd and 3rd goods together
  (8 > 7) but not its lower triple (8 < 9).
- Phase III's early second goods.

## What survives

**Conjecture VMX₂.** VMX₂ is VMX with Phase III dropped: Phase III's goods go to the pool, where the F1/F6x loop
places them. It completes both counterexamples:
- n = 3: 18 of 26 runs end EFX₀;
- n = 4: 559 of 595 runs.

Exchanges in which the partner also returns goods to the pool (`xret`) rescue the n = 3 instance but not the n = 4
one. VMX₂ is tested in `k4/vm.md` §7.

Reproduce:
- `python3 attempts/k4_vm_vmx.py`: an independent replay, sharing no code with `k4/vm/`;
- `python3 k4/vm/vmx_climb.py 3 64 80 2` and `python3 k4/vm/vmx_climb.py 4 48 60 3 --limit=300`: the climbs that found
  them.
