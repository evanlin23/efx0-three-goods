# Attempt: the big-top owner step BTCYC is false at n = 4 (compute/k4-gap)

**Statement tried.** Conjecture K4.HALL.BTCYC of `k4/hall_bt.md` §2 (PR #52):
- Take a Pareto-maximal pre-allocation P at the fewest frozen agents, with ω ≥ 1 and no removal-only owner, that has
  an exposed frozen big-top agent x (four goods, holding its top a, with a > b + c).
- Then some cycle of #41's exchange digraph through x gives a removal-only completable pre-allocation.
- The cycle move lets every receiver of a threat edge keep part of its own holding and tries every admissible choice.

The move stays at the fewest frozen agents (rigidity, `k4/c4min.md` §1). #52 checked it on every such maximum with n ≤ 3
and on samples at n = 4.

**It fails on a pure n = 4 profile, m = 8.** The profile was found by the hunt over 400,000 random profiles per pure
n = 4 core (`results/k4_gap_hunt_n4_pure_s400k.log`); its record is in `results/k4_gap/hard_hunt.json.gz`.

| agent | goods and values | in P |
|---|---|---|
| 0 | 0:3, 2:10, 5:2, 6:6 (big-top: 10 > 6 + 3) | frozen on 2 (its top); U_0 = {0, 5, 6} worth 11 > 10, exposed |
| 1 | 0:2, 3:10, 4:3, 6:6 (big-top: 10 > 6 + 3) | frozen on 3 (its top); U_1 = {0, 4, 6} worth 11 > 10, exposed |
| 2 | 1:2, 2:10, 4:3, 7:6 | free, base {4, 7}; needs 2 |
| 3 | 1:2, 3:8, 5:3, 7:4 | free, base {1, 5}; needs 3 |

- **The pre-allocation.** J = {0, 6}, there are no slots, f = 2 and ω = 2.
- **No owner.** Owner 2 (X = {4, 7, 0, 6}) threatens agent 1: goods 0, 4 and 6 are worth 11 > 10. Owner 3
  (X = {1, 5, 0, 6}) threatens agent 0: goods 0, 5 and 6 are worth 11 > 10. Both threats are local (class L).
- **Pareto-maximal.** P is Pareto-maximal among all configurations of the profile, and it is not removal-only
  completable.
- **The only cycle.** The exchange digraph has the edges:
  - need edges 0 → 2 and 1 → 3 (agents 2 and 3 need the tops of 0 and 1);
  - threat edges 2 → 1 and 3 → 0.

  Its only cycle is (0, 2, 1, 3), through both big-top agents.
- **Moving it fails.** Moving it makes agents 2 and 3 frozen on goods 2 and 3, and agents 0 and 1 free. Each free agent
  needs good 6 in its base: agent 0's base must beat 0, 5 and 6, and agent 1's must beat 0, 4 and 6 (value 6). So the
  result is not a valid pre-allocation at the fewest frozen agents, whatever pairs the receivers take. The profile's
  keys (frozen agents and their goods) are {0 → 2, 1 → 3}, {0 → 2, 3 → 3} and {1 → 3, 2 → 2}.

**What repairs it.** #52's downgrade swap. For example, agent 0 gives 2 to agent 2 and takes a pair of L ∪ Q_2; each of
the 6 downgrade swaps gives a configuration with a valid owner. So the reachability form (bench statement REACH_EACH:
exchange cycles and downgrade swaps reach a completable pre-allocation from every non-completable Pareto-maximum) holds
here, and it holds on every profile tested (`k4/gap.md` §4).

**Checked twice, independently.** `results/k4_gap_btcyc_replay.log`:
1. `k4/gap.c`: the profile is in the gap with f = 2 and ω = 2. Its key list has no key with agents 2 and 3 frozen. The
   configuration P has no valid owner.
2. `k4/gap_model.py` (independent of gap.c) confirms all of this. It also finds:
   - P's pre-allocation is not removal-only completable;
   - P is Pareto-maximal;
   - the only cycle through the big-top agents is (0, 2, 1, 3);
   - no cycle move has a result at the fewest frozen agents, whether with best pairs in every order, any pairs, or
     receivers keeping part of their pair;
   - all 6 downgrade swaps complete.

**Smallest known.** n = 4, m = 8. BTCYC holds on every such maximum with n ≤ 3 (#52, and bench BTCYC on the n = 3
catalog). It also holds on the n = 4 and n = 5 samples of `k4/gap.md` §4. The pure n = 4 class was sampled, not searched
exhaustively.

**Reproduce.**
```
python3 attempts/k4_gap_btcyc.py        # gap.c and gap_model; exit status 0 if every check passes
python3 k4/gap_bench.py --profile='{"sets": [[0,2,5,6],[0,3,4,6],[1,2,4,7],[1,3,5,7]], "vals": [[3,10,2,6],[2,10,3,6],[2,10,3,6],[2,8,3,4]], "m": 8}' --only=BTCYC,REACH_EACH,REACH_EACH_CYC
```
