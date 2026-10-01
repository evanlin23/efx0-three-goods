# DL_RT4 and DL on the key graph fail at n = 5: a role swap must pass through a frozen agent

Workstream `compute/k4-rt4-n5`, which merges the shard branches `compute/k4-rt4-n5b` and `compute/k4-rt4-n5c`
whose runs found the failures. Ledger rows K4.DL2.RT4 and K4.DL13.KEY (REFUTED by this file), K4.DL2.RT4E (the
n ≤ 4 evidence, unchanged) and K4.DL2.RC (the successor, CONJECTURE). Definitions: `k4/dl2.md` §3 (moves T1, T2, T3),
`k4/dlrt4.c`'s header (T4 and RT4 = T1 ∪ T2 ∪ T3 ∪ T4), `k4/dl13.md` §2.3 Remark (keys and the key graph),
`k4/c4x.md` §1 (𝒫 and the removal-only deficit).

**Statements refuted.**
- **DL_RT4**: for every strict profile of every connected k = 4 core whose fewest frozen agents is f ≥ 1, with ω ≥ 1,
  every min-frozen P with def(P) > 0 has a min-frozen P′ with def(P′) < def(P) reached by (T1) a re-base of one free
  agent, (T2) a rotation of free agents, (T3) a role swap with a needer and at most one helper giving up a good, or
  (T4) a permutation of the frozen goods among frozen agents. All four keep the needed set NA.
- **DL on the key graph with single (T3)/(T4) edges** (`k4/dl13.md` §2.3 Remark): every key κ (needed set, frozen
  agents, their goods) with def*(κ) > 0 (the least deficit of a min-frozen P of key κ) has a key κ′ with
  def*(κ′) < def*(κ) reached by one (T3) or (T4) move from some state of κ. DL_RT4 implies it, and it implies TARGET₄.
  It is weaker than DL_RT4, but it fails on the same profiles.

## The instance `rt4-n5m9-chain`

Core pos 3206 (m = 9, idx 364) of `results/k4_certs_5_n4_4.json.gz` (n = 5, four 4-good agents and one 3-good agent),
profile 108,86,1,108,27 (indices into `check4.core_domains(sets, m, False)`). Found by run n5b_4 of
compute/k4-rt4-n5b: 16,000 random profiles per core, seed 1 (`results/k4_rt4/n5b_4.log`, `n5b_FAILURES.md`).

| agent | goods : values |
|---|---|
| 0 | 0:6, 2:3, 4:5, 7:7 |
| 1 | 1:4, 4:2, 7:8, 8:7 |
| 2 | 3:2, 6:4, 8:3 |
| 3 | 5:4, 6:8, 7:1, 8:6 |
| 4 | 5:2, 6:7, 7:8, 8:4 |

The hypergraph is a connected k = 4 core and the profile is strict (`k4/suite/model.py`: `core_violations` is empty,
`strict` holds). σ = 2n − m = 1.

**P = ({7}, {8}, {3}, {5}, {6})**, J = {0, 1, 2, 4}. Needs: N_0 = ∅ (7 is agent 0's top), N_1 = {7}, N_2 = {6, 8},
N_3 = {6, 8}, N_4 = {7}, so NA = {6, 7, 8}. Agents 0, 1 and 4 are frozen (on 7, 8 and 6); 2 and 3 are free. f = 3 (every
min-frozen P of the profile has three frozen agents), so ω = 2. The profile has 58 min-frozen P, 14 of them with def > 0.

def(P) = 1. Only the free agents 2 and 3 can own. Their bundle B_o ∪ J threatens agent 0, which is frozen on 7 (worth 7)
and values 0, 2, 4 at 6, 3, 5. A safe bundle can hold good 4 but neither 0 nor 2, and leaving out both junk goods 0
and 2 needs two slots. Only one is free: the other free agent's second slot.

**No RT4 move lowers the deficit.** Every min-frozen P′ with a smaller deficit changes at least three bases. All 16 at
distance 3 have one shape, a **frozen chain**:
- x = agent 0 (frozen) gives up its good g = 7 and takes junk ({0}, {0, 2}, {0, 4} or {2, 4}), becoming free;
- a frozen agent w takes 7 and gives up its own good h (w = 4 with h = 6, or w = 1 with h = 8) and stays frozen;
- a free agent z that needs h takes it and freezes (agent 3, or agent 2).

NA = {6, 7, 8} is kept. For example, **P′ = ({0}, {8}, {3}, {6}, {7})** with def(P′) = −1. Agent 4 holds its top 7,
agent 3 its top 6, and agent 0 is a free owner of {0, 1, 2, 4, 5}, which threatens nobody.

Neither T3 nor T4 makes this move. Agent 0's good 7 is needed only by the frozen agents 1 and 4, so no free agent can
take it in a role swap: T3 needs P′(z) = P(x) with z free. T4 moves only agents that stay frozen. T1 and T2 keep the
key, and P has the least deficit of its key. So **DL_RT4 fails at P**. In key-graph terms, P's key (NA = {6, 7, 8};
agents 0, 1, 4 frozen on 7, 8, 6) has def* = 1 and no (T3) or (T4) neighbour with a smaller def*, so DL on the key
graph fails too. The chain reaches the key (NA = {6, 7, 8}; agents 1, 3, 4 frozen on 8, 6, 7), whose def* is at most
−1.

The chain is a role swap of x and z with the frozen good passed through w. Formally it is a role swap in which z
takes g, followed by an exchange of g and h between z and w. But z need not need g (agent 3 values 7 at 1), and no
intermediate state is a better min-frozen state: there is none within distance 2. The successor relation adds exactly
this move. In **(T3⁺) frozen-chain role swap**, NA′ = NA;
exactly one changed agent x goes frozen → free; exactly one changed agent z goes free → frozen, and z needs its new good
in P; W, the changed agents frozen in both, pass the frozen goods along; at most one helper, free in both, gives up a
good; and the bases of W ∪ {z} in P′ are exactly the bases of W ∪ {x} in P. T3 is the case W = ∅. Every failure below
is repaired by a T3⁺ move with |W| = 1 (K4.DL2.RC).

## The second family `rt4-n5m10-chain`

Pure core pos 2614 (m = 10, idx 568) of `results/k4_certs_5_pure.json.gz`, profile 6,9,43,24,24 of the big-top domains
(`dlrt4_run.py --bt=all`: every 4-good agent restricted to types with top > second + third). Found by run n5c_purebt of
compute/k4-rt4-n5c: 5,000 big-top profiles per pure n = 5 core, seed 2 (`results/k4_rt4/n5c_FAILURES.md`).

Values: agent 0 0:2, 2:6, 4:3, 8:10; agent 1 1:2, 3:8, 8:4, 9:3; agent 2 3:10, 4:2, 8:6, 9:3; agents 3 and 4 (twins)
5:4, 6:2, 7:3, 9:8. P = ({8}, {9}, {3}, {5}, {6, 7}), NA = {3, 8, 9}, agents 0, 1, 2 frozen, f = 3, ω = 3, def(P) = 1.
Agent 0's good 8 is needed only by the frozen agent 1. All 8 better states at distance 3 are frozen chains: agent 0
frees 8, agent 1 moves from 9 to 8, and a twin z ∈ {3, 4} takes 9, e.g. P′ = ({2}, {8}, {3}, {9}, {6, 7}) with
def(P′) = −1. DL_RT4 fails at P and at its image under the twin swap.

## All failures found

| run (branch) | core file, pos (idx, m) | failing profiles | failing states |
|---|---|---:|---:|
| n5b_4 (compute/k4-rt4-n5b; still running when merged) | `k4_certs_5_n4_4`, 3206 (364, 9) | 1 | 1 |
| | `k4_certs_5_n4_4`, 3521 (679, 9) | 1 | 2 |
| n5c_purebt (compute/k4-rt4-n5c) | `k4_certs_5_pure`, 2614 (568, 10) | 3 | 8 |
| | `k4_certs_5_pure`, 4170 (25, 12) | 3 | 32 |
| | `k4_certs_5_pure`, 4214 (69, 12) | 2 | 24 |
| **total** | 5 cores | **10** | **67** |

Every failure has f = 3, def(P) = 1 and nearest distance 3. Every one of the 692 better states at distance 3 is a
frozen chain (48 at n5b, 644 at n5c), and one T3⁺ move repairs each. The unrestricted sample `n5c_pure` (5,000 random
profiles per pure core, 23,370,000 profiles) found none, and n5b's other runs found none
(`results/k4_rt4/n5b_3.log`, `n5b_3bt.log`). Three implementations agree at all 67 states:
- `k4/dlrt4.c` (sha256 fcde494a…, the runs);
- `k4/dlrt4_ref.py` on `k4/suite/model.py` (`results/k4_rt4/ref_n5b_failures.log`, `ref_n5c_fails.log`: every state
  of the 10 profiles, 0 mismatches);
- `k4/rt4_n5_xcheck.py` on main's `k4/c4x_check.py`, through `k4/dl134_xcheck.py`, without model.py or dlrt4.c
  (`results/k4_rt4/xcheck_n5_failures.log`).

The last tool also gives the key-graph verdicts: DL with single T3/T4 edges fails at 10 of the 41 keys with def* > 0
(one per profile). With T3⁺ ∪ T4 edges it fails at none, and DL_RC holds at all 168 def > 0 states of the 10 profiles.

## Smallest failing configuration and reproduction

`rt4-n5m9-chain` (`k4/suite/instances/rt4-n5m9-chain.json`): n = 5, m = 9, f = 3, ω = 2, the state P above. It is
the smallest failure found. At n ≤ 4 DL_RT4 holds on every profile tested (K4.DL2.RT4E), exhaustively for the n = 4
cores with one and two 4-good agents and for cores 0–227 of the 339 with three. Whether some n = 5 core with
m < 9 fails is not known: the n = 5 runs are samples.

```
python3 k4/rt4_n5_xcheck.py results/k4_rt4/n5b_failures_inst.json results/k4_rt4/n5c_fail_inst.json   # ~3 min, one process
python3 k4/dlrt4_ref.py inst results/k4_rt4/n5b_failures_inst.json        # dlrt4.c against the model.py reference, seconds
python3 k4/suite/run.py --only=rt4-n5m9-chain,rt4-n5m10-chain --pred=k4/rt4_pred.py:rt4_c --pred=k4/rt4_pred.py:rt4_x \
    --pred=k4/rt4_pred.py:key_x --pred=k4/rt4_pred.py:rc_x                # FAILS, FAILS, FAILS, holds
```
