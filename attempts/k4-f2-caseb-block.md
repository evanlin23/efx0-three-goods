# T3 stage at f ≥ 2: "the owner of every frozen-needers-only block is a free end"

Workstream `proof/k4-f2` (`k4/f2.md` §1, §4, §6). Ledger row K4.F2.X (REFUTED).

**Candidate.** At every T3-stage state with f ≥ 2, take a single block (o, X, c, x): o a best owner, X optimal, c ∈ J ∖ X,
and x the only agent other than o that X ∪ {c} threatens. If x is frozen and every agent that needs g_x is frozen, then
o is the free end of a need path to x (`k4/f2.md` §3.1). With θ-ok along that path, Corollary 9.1⁺ would then repair
every such block by a (T3⁺) move. This is the block-level form of the case-B observation of `k4/f2.md` §1.

**Smallest failing configuration** (the smallest by (n, m) in the scan of `results/k4_f2/caseb.log`):
n = 5, m = 9, f = 2, a strict profile of a core (k4/suite/model.py's checks),
- sets [[0,1,4,7],[2,3,4],[2,3,8],[5,6,7,8],[5,6,7,8]], values [[2,3,8,4],[2,3,4],[2,4,3],[3,2,8,4],[2,3,8,4]];
- P = ({7}, {4}, {3}, {8}, {5,6}), def(P) = 1, at the T3 stage; agents 0 and 1 frozen (on 7 and 4).
- Owner 2 has a single block by agent 1. Every needer of good 4 is frozen. The free ends of need paths to agent 1 are
  agents 3 and 4, not 2.
- DL_{R_C} holds there: (T3) and (T3⁺) moves lower the deficit.

**Frequency.** At the 33,816 T3-stage states of `k4/f2.md` §1 there are 27,652 single blocks by a frozen agent whose
needers are all frozen. At 2,339 of them the owner is not a free end of a need path to the blocker
(`results/k4_f2/caseb.log`). What survives on the data is the state-level form: every case-B state, in which every
single frozen blocker has frozen needers only, has some block whose owner is a free end (`k4/f2.md` §1, §7). That form
is not proved.

**Reproduce.** `python3 attempts/k4_f2_attempts.py` (case "n = 5, m = 9 (case B, block level)"). Implementation A
(k4/f2_lib.py and k4/f2_shapes.py on k4/suite/model.py) and implementation B (main's k4/dl134_xcheck.py with the
script's own single blocks and need-path ends) both confirm the T3 stage, the block, the frozen needers and the free
ends {3, 4}. The scan itself: `python3 k4/f2_lemmas.py --caseb results/k4_f2/shapes_[0-7]*.jsonl.gz ...` (k4/f2_post.sh,
step (f)).
