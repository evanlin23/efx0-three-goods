# Attempt: local validity of the chain's result decides whether it repairs (k = 4)

Workstream `proof/k4-ttc` (`k4/ttc.md` §6). Status: **fails both ways**: local validity is neither necessary nor
sufficient for a chain to repair. The smallest failing configuration is T3 for both, replayed by brute force.

## The idea

At k = 3, Draft and Exchange keeps a *valid* state (every wanted good is held alone) and finishes by a counting
test. The candidate proof shape for OC₁ was:
1. some improving chain leads to a locally valid state;
2. every locally valid state reached by an improving chain has a one-absorber completion.

The filters tested on the chain's result B′ (`k4/ttc/local_rule.py`):
- V: valid;
- T: no base threatens another agent;
- N: no frozen agent values its junk above its base, Lemma GDT's (G4) without the absorber's pick;
- X0: x₀ is no longer dangerous.

## What happens

`results/k4_ttc/local_rule.log`. Of the 194 distinct hard screen starts:

| filter | some chain passes | a passing chain repairs | every passing chain repairs |
|---|---|---|---|
| none | 194 | 194 | 0 |
| V | 194 | 187 | 71 |
| T | 194 | 187 | 83 |
| V+T | 194 | 187 | 89 |
| V+T+N | 193 | 186 | 135 |

The filters raise the repairing fraction of chains from 34% to 80–92%. But:
- on 7 starts no valid chain repairs, so validity is not necessary;
- on 105 starts some valid, threat-free chain does not repair, so it is not sufficient.

## Smallest failing configuration

T3 (n = 3, m = 6; `k4/sdc/nof_var.py` SPECIAL): sets [[5, 0, 4, 2], [3, 1, 4], [4, 1, 3, 0]], values
[[1, 38, 36, 6], [12, 22, 30], [28, 20, 12, 38]].
- *Not necessary.* From the picks (0, 1, 4) the only repairing chains give agent 0 the bundle {2, 4} or {2, 4, 5}
  while agent 2 holds {0}. Agent 1 then wants 4 (worth 30 to it, above its base 1 worth 22), which is not held alone,
  so the result is invalid. Every valid chain result fails to repair.
- *Not sufficient.* From the picks (0, 4, 1) the valid, threat-free results [[0], [1, 3], [4]] and [[0], [4], [1, 3]]
  have no one-absorber completion.

Reproduce: `python3 k4/ttc/repro_attempts.py` (part (b); brute-force completions from the raw EFX₀ definition; log
`results/k4_ttc/repro_attempts.log`).

## Lesson

The repairing state can leave a wanted good inside a pair, as in the start (0, 1, 4) above. The completion then
compensates the wanter. A proof of OC₁ cannot run through a local validity invariant alone; the completion test has to
see the wanters' compensation, as §29's two-good analysis says.
