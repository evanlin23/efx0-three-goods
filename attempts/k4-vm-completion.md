# Conjecture VC: V-M's matching extends ⟹ F1–F3 with rotation complete it (k = 4)

Workstream proof/k4-vm (`k4/vm.md` §6.1). The conjecture: whenever some EFX₀ allocation contains a Phases I–II
matching of Viswanathan–Mehta, the following completes it for some resolution of the choices, from some V-M matching:
1. Phase III with F2: EFX₀-safe 4th/3rd/4th-choice matchings;
2. then F1 with rotation: each pool good goes to an agent whose bundle stays EFX₀-unenvied, after envy cycles are
   rotated away;
3. then F3: junk by L3.

It held on the screen set (147 of 147 instances where a matching extends), the logged hard profiles (34/34), SPECIAL
(3/3) and 3,000 random core profiles with n = 3 (2,977/2,977).

**It is false.** It fails on 1 of the 2,992 random n = 4 core profiles where a matching extends
(`results/k4_vm/vm0_cores4.log`, instance `core4:1615`).

## Smallest failing configuration found: n = 4, m = 8 (a connected k = 4 core)

| agent | ranking (good: value) |
|---|---|
| 0 | 7: 8 > 0: 6 > 5: 5 > 2: 4 |
| 1 | 7: 8 > 3: 6 > 6: 5 > 1: 4 |
| 2 | 4: 10 > 7: 8 > 5: 4 > 6: 3 |
| 3 | 4: 8 > 6: 4 > 7: 3 > 5: 2 |

V-M, step by step:
- Agent 3 is the only agent of A (8 > 4 + 3), so Phase I gives it good 4.
- Phase II step 1: agents 0 and 1 both claim 7, and one of them wins.
- Step 2: the loser takes its 2nd choice (0 for agent 0, 3 for agent 1).
- Step 3: agent 2 takes 5, its 3rd choice; its top 4 and its 2nd, 7, are gone.

There are two matchings, ({7}, {3}, {5}, {4}) and ({0}, {7}, {5}, {4}). The first extends, to
({7}, {0,1,3,6}, {2,5}, {4}) and ({7}, {1,2,3,6}, {0,5}, {4}); these are the only two of the 98 EFX₀ allocations that
contain it.

Phase III (F2 approves every step):
- N₃ = {2} first, so agent 2 gets its 4th choice 6.
- Then the loser of 7 in N₂ would get its 3rd choice, but that is 6 (agent 1) or 5 (agent 0), both gone. So it gets
  its 4th: 1 or 2.

The states are ({7}, {3,1}, {5,6}, {4}) with pool {0, 2}, and ({0,2}, {7}, {5,6}, {4}) with pool {1, 3}.
- From either state, every sequence of EFX₀-safe placements gets stuck.
- No reachable state has an envy cycle, so rotation changes nothing.

Both extensions need good 6 with agent 1, as its 3rd choice. V-M's "starting with those that have low-ranked objects"
hands it to agent 2 as a 4th choice first. F2 checks safety, not extendability.

**What survives.** F6x (exchanges) completes this instance in every mode. For example, after good 0 goes to agent 1,
agent 0 gives its top 7 to agent 2 and takes agent 2's good 5 plus the pool good 2 (5 + 4 = 9 > 8). Agent 2 then holds
{6, 7} (11 > 7), and the result ({5, 2}, {3, 1, 0}, {6, 7}, {4}) is EFX₀ (`vmlib.vm6x_run(..., mode='stuck')`). So the repair needs moves that undo Phase III's choices, or a Phase III that looks ahead.

Reproduce:
- `python3 attempts/k4_vm_completion.py`: an independent replay from the definitions (brute force, every placement
  sequence, an envy-cycle check), sharing no code with `k4/vm/`;
- `python3 k4/vm/vm0_test.py cores:4:3000:12 --variants=f2,f2rot`: the run that found it.
