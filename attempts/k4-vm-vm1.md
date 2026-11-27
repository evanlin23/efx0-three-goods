# Conjecture VM1 with narrow exchanges: one move, then placement (k = 4)

Workstream proof/k4-vm (`k4/vm.md` §7.3). Conjecture VM1 says: from some V-M matching (Phases I–II), at most one
move, then EFX₀-safe placements with envy-cycle rotation, give a complete EFX₀ allocation. A move is one of:
- a pool upgrade: i holding a single good y takes a set S of pool goods with v_i(S) > v_i(y), and y returns to the
  pool;
- a two-agent exchange: i holding a single good y takes a good z from X_j plus pool goods S, j takes y, and both
  strictly gain.

In both, the state must stay EFX₀. On the screen set, the named instances and 2,700 random cores, VM1 held, mostly
with no move at all (`k4/vm.md` §7.3).

**With narrow exchanges it is false.** Narrow means that z must be a good the taker i values, as in
`vmlib.exchanges` by default. Climbing against VM1 (`k4/vm/vmx2_climb.py --obj=vm1`, with is_core4 checked after
every mutation) found strict connected cores where neither a V-M matching nor any state one narrow move away can be
completed:
- n = 3, m = 7 (`results/k4_vm/vm1_climb3.log`);
- n = 4, m = 7 (`vm1_climb4.log`).

Both need two narrow moves (`vmx2_phases.py`), and full VMX₂ completes both.

**With unrestricted exchanges** (z may be worthless to i; `vmlib.FREE_Z`, `--freez=1`) **both satisfy VM1, with one
move.** So the narrow restriction was the cause, and VM1 is stated with unrestricted exchanges from here on
(`k4/vm.md` §7.3).

## The n = 3, m = 7 core

| agent | ranking (good: value) |
|---|---|
| 0 | 1: 8 > 4: 6 > 0: 4 > 5: 1 |
| 1 | 1: 4 > 4: 3 > 6: 2 |
| 2 | 1: 10 > 2: 6 > 3: 3 > 5: 2 (strongly top: 10 > 9) |

What happens:
- Phase I gives good 1, the top of all three agents, to agent 2. Agents 0 and 1 then both claim good 4. The V-M
  matchings are ({4}, {6}, {1}) and ({0}, {4}, {1}).
- 20 EFX₀ allocations exist. None of the 4 states within one narrow move can be completed by placements and
  rotations.
- The completing move is agent 2 giving its top 1 to agent 1, taking agent 1's good 6 (worthless to agent 2) and the
  pool goods {2, 3, 5} (11 > 10). From ({4}, {1}, {6, 2, 3, 5}) the rest is placed.

Reproduce:
- `python3 attempts/k4_vm_vm1.py`: an independent replay. It enumerates every state within one move, for both move
  sets, and runs an exhaustive placement-and-rotation search;
- `python3 k4/vm/vmx2_climb.py 3 48 150 31 --obj=vm1`: the climb that found it.
