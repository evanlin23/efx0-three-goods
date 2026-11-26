# VMˣ from every serial-dictatorship outcome (a path form of Conjecture MD)

Workstream proof/k4-vm (`k4/vm.md` §7). The approach: start VMˣ from *any* SD outcome Y, not only V-M's rank-greedy
matching. VMˣ is Phase III with F2, then rotation, F6x moves (pool upgrades, two-agent exchanges with pool goods) and
F1 placements, then F3. No step of VMˣ lowers a value, so a successful run would value-dominate Y. "Some run from
every Y ends EFX₀" would therefore be a constructive form of Conjecture MD (K4.SDC.MD).

**It fails at n = 4, m = 7**, on `r4253` of `k4/sdc/nof_var.SPECIAL` (`results/k4_vm/vm6_sd_special.log`).

| agent | ranking (good: value) | pick in Y |
|---|---|---|
| 0 | 5: 10 > 6: 7 > 2: 4 > 0: 2 | 2 |
| 1 | 4: 4 > 6: 3 > 1: 2 | 6 |
| 2 | 4: 8 > 3: 5 > 2: 4 > 5: 2 | 4 |
| 3 | 5: 10 > 6: 7 > 4: 6 > 3: 2 | 5 |

Y = SD(3, 2, 1, 0) = ({2}, {6}, {4}, {5}).
- Brute force over all 4⁷ allocations: 23 EFX₀ allocations, none containing Y. Eight of them value-dominate Y, so MD
  holds here.
- All eight give good 6 to agent 0 and good 4 to agent 1. From Y that needs a three-agent cycle with a pool good:
  agent 0 takes 6 from agent 1, agent 1 takes 4 from agent 2, and agent 2 takes 2 from agent 0 plus pool good 3.
- F6x has only two-agent exchanges, so both runs of VMˣ from Y get stuck.

From V-M's own matching, VMˣ succeeds on this instance (`vm6_special.log`). So the failure is the start's, and
starting from V-M's matching is not a restriction without content.

Reproduce:
- `python3 k4/vm/vm6_sd.py special`;
- `python3 attempts/k4_vm_every_start.py`: an independent replay of the brute-force facts.
