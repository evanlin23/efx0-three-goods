# Receiver-first does not restore the k = 3 fact (DE-a)

Workstream `proof/k4-k3-oc1` (`k4/k3_oc1.md` §13), at the coordinator's request (Conjecture RF, `k4/sdc.md` §31 end;
ledger K4.SDC.RF).

**The idea tried.** The one-move machinery at k = 3 (Lemma 1, Theorem 1′, B\*'s step (e), and kgen-n3's
Proposition A) rests on **(DE-a)**. Only an agent holding its top good can be threatened by a bundle of junk, so only
such an agent takes junk in a repairing move. At k = 4 a b-holder with junk {c, d}, c + d > b, is threatened and gains
from {c, d}. Both n = 4 counterexamples to OC₁^max use this (`attempts/k4-k3oc1-de-trades.md`, `k4/k3_oc1.md` §7,
§10). The hope: receiver-first (RF) restores (DE-a), so that at every RF start that needs a move some repairing move
has only top-holders taking junk, and the k = 3 proof lifts.

**Result** (exact: every official improving chain of `k4/sdc.md` §29, and a brute-force one-absorber completion after
each). Data are the n = 5 RF starts of girth's build of the certifier's exports, classes DEMOTE-0 and (1, 3)
(`k4/k3oc1/rf/rf_dea_full.py`, `results/k4_k3oc1/rf_dea_full_n5.log`):

| class | starts | complete at the picks | need a move, some repair satisfies (DE-a) | need a move, **every** repair violates (DE-a) |
|---|---|---|---|---|
| DEMOTE-0 (one receiver, no truly dangerous agent) | 113,484 | 113,210 | 274 | 0 |
| (1, 3) (one receiver, three truly dangerous agents) | 7,733 | 0 | 5,857 | **1,876** |

Hall adds DEMOTE-2 at n = 4 (`k4/oc1_hall.md` §24.8, fact (U-c), `results/k4_oc1_hall/rf_b_u.log` on
`claude/k4-oc1-hall`; [unverified] here). At all 43,520 starts the repairing agent k wants another truly dangerous
agent's pick, so it does not hold its top.

**Smallest failing configuration** (n = 5, m = 9; the core 5_pure#778, sets
[[0,2,6,7],[1,5,6,8],[2,5,6,7],[3,4,5,8],[3,4,7,8]]; values [[2,4,5,8],[1,6,4,8],[1,6,4,8],[3,5,6,7],[6,3,10,8]]).
- The order (0, 4, 3, 1, 2) gives the picks (7, 6, 2, 5, 8). Agent 2 is the receiver.
- RF gives the picks (6, 1, 7, 5, 8), with junk {0, 2, 3, 4}, and these have no one-absorber completion.
- 48 improving chains exist; 9 repair. In every one of the 9, an agent that held less than its top good takes junk.
  For example, agent 0 holds its second good and takes its two lowest goods {0, 2}, and the receiver 1 takes back
  6. With other values on the same core (the second instance of the replay), 3 of the 9 repairs satisfy (DE-a).

**What survives.** The *shape* of the k = 3 proof survives, but not its key fact:
- Every DEMOTE move is a length-one rotation into the unique receiver d: a chain k → d, or a ring d → p → d.
- The SINK completion of girth and Hall is the k = 3 completion LE: owner d (or k), and one slot for the rotated
  agent.
- The k = 4 completion half must allow rotated agents that hold their b and take their two lowest goods.

Replay (no repository code, raw EFX₀, every official chain, brute-force completion):
`python3 attempts/k4_k3oc1_rf_dea.py` (log `results/k4_k3oc1/rf_dea_replay.log`).
