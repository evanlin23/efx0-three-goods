# Single-step DL_RC fails at n = 5 (f = 1 and f = 2), even with an unrestricted helper; the key-graph form holds

Workstream `compute/k4-rc-refute`, which merges `compute/k4-rc` (the checkers `k4/dlrc.c`, `k4/dlrc_ref.py`, the hunt
`k4/dlrc_hunt.py`, the logs in `results/k4_rc/`, where `FAILURES.md` and `SUMMARY.md` have the full account). Ledger
rows K4.DL2.RC and K4.DL2.RCY (REFUTED by this file) and K4.DL2.RCKEY (EVIDENCE). Definitions: `k4/dl2.md` §3 (moves
T1, T2, T3), `k4/dlrc.c`'s header and the row K4.DL2.RC (T3⁺, T4, R_C), `k4/dl13.md` §2.3 Remark (keys and the key
graph), `k4/c4x.md` §1 (𝒫 and the removal-only deficit). EVIDENCE tooling throughout; the refutations are single
instances, each checked by several implementations.

**Statements refuted.**
- **DL_RC** (K4.DL2.RC): for every strict profile of every connected k = 4 core whose fewest frozen agents is f ≥ 1,
  with ω ≥ 1, every min-frozen P with def(P) > 0 has a min-frozen P′ with def(P′) < def(P) reached by one move of
  R_C = (T1) ∪ (T2) ∪ (T3⁺) ∪ (T4). (T3⁺), the frozen-chain role swap: NA kept; exactly one changed agent x goes
  frozen → free and exactly one z goes free → frozen, z needing its new good in P; W = the changed agents frozen in
  both; at most one helper, free in both, giving up a good of its base; the bases of W ∪ {z} in P′ are exactly those
  of W ∪ {x} in P.
- **DL_RC with an unrestricted helper** (K4.DL2.RCY; compute/k4-portfolio's predicate RC_Yfree): the same with
  (T3⁺)'s helper (still at most one) allowed to keep or grow its base.
- Both instances are also new failures of **DL_RT4** (K4.DL2.RT4, already refuted at f = 3 by frozen chains): here
  at f = 1 and f = 2, and not chain states.

## The instance `rc-n5m13-f1` (core 4604, f = 1)

Pure core pos 4604 (m = 13, idx 58) of `results/k4_certs_5_pure.json.gz`, profile 44,118,8,8,158 (indices into
`check4.core_domains(sets, 13, False)`). Found by compute/k4-rc's hunt `ranked_pure`. The simplest of the 369 failing
profiles found (largest value 8, value sum 97, tied with 44,118,36,36,158).

| agent | goods : values |
|---|---|
| 0 | 0:3, 2:5, 9:6, 11:7 |
| 1 | 1:6, 6:5, 10:4, 12:8 |
| 2 | 3:2, 7:3, 11:8, 12:4 (big-top) |
| 3 | 4:2, 8:3, 11:8, 12:4 (big-top) |
| 4 | 5:6, 9:4, 10:1, 12:8 |

A connected k = 4 core, strict profile (`k4/suite/model.py`). σ = 2n − m = −3, f = 1, ω = 4. The min-frozen class has
129 states in three keys (agent 0, 2 or 3 frozen on 11, NA = {11}); def* is 1 for agent 0's key and −1 for the others.
45 states have def > 0.

**P = ({11}, {12}, {3,7}, {4,8}, {5,9})**, J = {0, 1, 2, 6, 10}. Agent 0 holds its top 11 and is frozen (agents 2
and 3, on pairs worth 5, need 11). **def(P) = 1**: the free agents 2, 3, 4 hold pairs and have no slot, so only agent
1's second slot is free. With owner 1, the bundle {12} ∪ J threatens agent 0 (frozen on 11, worth 7) unless it leaves
out 0 or 2 (3 + 5 > 7), and the left-out good has no slot: deficit 1. Every other owner does worse (deficit 2 for
owners 2 and 3, 3 for owner 4): its bundle must also leave out goods of agent 1, whose base {12} is worth 8.

**No R_C move lowers the deficit.** P has 84 better min-frozen states (def ≤ 0, all with NA = {11}), none within
distance 2:
- the 6 nearest (distance 3), shape (|U|, |Z|, |W|, |Y|) = (1, 1, 0, 1): **a role swap whose one helper grows**, e.g.
  **P′ = ({0,2}, {1,12}, {3,7}, {11}, {5,9})**, def 0: x = 0 releases 11 for {0, 2}, z = 3 takes {11} and freezes,
  and helper 1 grows {12} → {1, 12}. (T3⁺) requires the helper to give up a good;
- the 78 others (distance 4), shape (1, 1, 0, 2): **role swaps with two helpers**, e.g. ({9}, {1,6}, {3,7}, {11},
  {12}), def −1 (agents 1 and 4 both give up goods).

With f = 1 there is no second frozen agent, so (T3⁺) with W ≠ ∅ and (T4) are impossible and R_C = RT4 here. The 8
(T3⁺) moves from P (all with W = ∅) reach states with def 1. DL_RC fails at P. With the helper unrestricted (RCY) the
nearest move above is allowed, so RCY holds here.

**The key form holds.** Another state of P's key, ({11}, {6,10}, {12}, {4,8}, {5,9}) with def 1, has the (T3) move
x = 0 → {9}, z = 2 → {11}, helper 4 {5,9} → {12} to ({9}, {6,10}, {11}, {4,8}, {12}) with def −1, a key with
def* = −1. Of the 35 states of P's key, 31 have def 1 and 4 have def 2 (e.g. ({11}, {1,6}, {3,7}, {4,8}, {5,12})), so
def* = def(P) = 1, and P is stuck only because no (T1)/(T2) move inside the key lowers the deficit.

## The instance `rc-n5m12-f2` (core 4515, f = 2)

Pure core pos 4515 (m = 12, idx 370) of `results/k4_certs_5_pure.json.gz`, profile 74,153,112,227,80. Found by
compute/k4-rc's hunt `certs_pure_x` (1,500 random pure cores), extended by the run `core4515` to 1,076 failing
profiles (4,304 states). The simplest found (largest value 8, value sum 89).

| agent | goods : values |
|---|---|
| 0 | 0:4, 2:3, 4:8, 8:2 (big-top) |
| 1 | 1:6, 8:3, 10:7, 11:5 |
| 2 | 3:4, 9:8, 10:3, 11:2 (big-top) |
| 3 | 4:8, 5:4, 6:2, 7:3 (big-top) |
| 4 | 5:4, 6:2, 7:3, 9:8 (big-top) |

A connected k = 4 core, strict profile. σ = −2, f = 2, ω = 4. 206 min-frozen states in 4 keys, 114 with def > 0.

**P = ({4}, {1,8}, {10,11}, B₃, {9})** with B₃ = {5}, {5,6}, {5,7} or {6,7} (four states). Agents 0 and 4 are frozen
(on 4 and 9), NA = {4, 9}, def(P) = 1 (owners 1 and 3 each leave out one junk good that no slot takes). Each has 92
better min-frozen states, all with NA = {4, 9} and none within distance 3 (for B₃ = {5,6}: 28 at distance 4, 64 at
distance 5):
- the nearest (distance 4), shape (1, 1, 0, 2): **a role swap with two helpers**, e.g. from B₃ = {5,6} to
  **P′ = ({0}, {1,10}, {3}, {4}, {9})**, def −1: x = 0 releases 4 for {0}, z = 3 takes {4} and freezes, and helpers 1
  ({1,8} → {1,10}) and 2 ({10,11} → {3}) both give up goods;
- the others (distance 5), shape (2, 2, 0, 1): **a double role swap**, e.g. ({0}, {1,10}, {9}, {4}, {5}), def −1
  (agents 0 and 4 out, 2 and 3 in, helper 1).

No better state has |U| = |Z| = 1 and at most one helper, so **DL_RC fails, and so does RCY** (at all four states).
DL_RC with any number of helpers, each giving up a good (portfolio RC_Yany), holds.

**The key form holds.** All 60 states of P's key have def 1. From those where agent 2 holds {3}, e.g.
({4}, {10}, {3}, {5}, {9}), a (T3) move (x = 0 → {0}, z = 3 → {4}, no helper) reaches ({0}, {10}, {3}, {4}, {9}),
def 0, in a key with def* = −1 (992 such witnesses, `results/k4_rc/rc_failures_4515_keyform.log`).

## Confirmation

| check | core 4604 | core 4515 |
|---|---|---|
| `k4/dlrc.c` (sha256 f1cf4cc1…) and `k4/dlrc_ref.py` (`dl134_xcheck.py` / `c4x_check.py`), 0 mismatches | 369 profiles, DL_RC fails at 369 of 16,605 states (`ref_rc_fail_all.log`) | 1,076 profiles, fails at 4,304 of 99,583 (`ref_rc_fail_4515_all.log`) |
| `k4/dlrt4_ref.py` (model.py; = DL_RC at f = 1) | 369 DL_RT4 failures (`ref_rt4_rc_fail_all.log`) | 324 on the first 81 profiles (`ref_rt4_rc_fail_4515.log`) |
| `k4/rt4_n5_indep.py` (repo-free, PR #86 audit) | 2 + 6 profiles: RCfail 1 each (`indep_check.log`, `indep_check6.log`) | 2 profiles: RCfail 4 each |
| `k4/rcy_indep.py` (on rt4_n5_indep's model): RC / RCY failures | 45 profiles: 45 / 0 (`rcy_indep.log`) | 81 profiles: 324 / 324 |
| `k4/dlrc.c`'s complete better-state lists (`k4/dlrc_failures.py`): shapes (U, Z, W, Y sizes) | all (1, 1, 0, 1) or (1, 1, 0, 2) (`rc_failures_n5_all.log`) | all (1, 1, 0, 2) or (2, 2, 0, 1) at the 4,304 states, so RCY fails (`rc_failures_4515_all.log`) |
| on branch compute/k4-portfolio at 6a8353b (not merged), fast path, RC / RC_Yfree | 45 profiles: 45 / 0 (coordinator, `portfolio_rc45.log`); 369: 369 / 0 (`portfolio_rc_all.log`) | 81: 324 / 324 (`portfolio_rc4515.log`); 1,076: 4,304 / 4,304 |
| the same branch's reference (`portfolio_ref.py` on `c4x_check.py`) | | every 8th of the 81 (11 profiles, 1,080 states): 0 mismatches, RC_Yfree fails at 44 (`portfolio_ref_rc4515.log`) |
| key-graph form (T3⁺ ∪ T4 edges) | 0 failures (dlrc.c, dlrc_ref.py, rt4_n5_indep.py, portfolio K2) | 0 failures |

On the 1,445 profiles the portfolio also finds: NA3 and D3 fail at core 4515 (4,304 states); RC_Yany, NA1, NAall,
U1Z1, D4, FR3 and every key-graph form (K1–K5, KU1) hold at both cores (`portfolio_rc_all.log`). On the whole suite
(159 complete instances, `results/k4_rc/suite_rc_pred_all.log`) the predicates of `k4/rc_pred.py` fail only at the two
new records: rc_c holds at the other 92 where it applies, rc_indep at 88, rcy_indep at 89 (FAILS at rc-n5m12-f2 only),
and keyplus_c at all 94; 0 disagreements.

**Smaller instances.** Deleting one or two goods from the failing profiles (values kept) and climbing on the smaller
cores (m = 10–12) finds no DL_RC failure (`rc_shrink*.log`, `hunt_shrink_cores*.log`); no n = 4 failure in the hunts
over the n = 4 cores with three or four 4-good agents (16.3 M profiles), and none at n ≤ 4 where DL_RT4 holds
(K4.DL2.RT4E; R_T4 ⊆ R_C). EVIDENCE only: n = 4 is not exhausted for three or four 4-good agents.

## What this says

A single move from every state is too much to ask: at both cores the stuck state has the least deficit of its key, and
the improvement exists only from another state of the same key (the key-graph form). The single-step repairs that do
exist need two helpers or a growing helper (core 4604) or two helpers or a double role swap (core 4515), and those
relations (RC_Yany, NA1, NAall) are not local in the sense the proofs of `k4/dl13.md` and `k4/f2.md` use. The live
statements are on the key graph: K4.SX.COVER (f = 1), K4.F2.COVER (f ≥ 2, PR #82) and the uniform Theorem ZMOVE
(proof/k4-zmove-hall, proof/k4-zmove-pot), with the data of K4.DL2.RCKEY.

## Smallest failing configurations and how to reproduce

- DL_RC at f = 1: `k4/suite/instances/rc-n5m13-f1.json` (n = 5, m = 13), P = ({11}, {12}, {3,7}, {4,8}, {5,9}).
- DL_RC and RCY at f = 2: `k4/suite/instances/rc-n5m12-f2.json` (n = 5, m = 12), P = ({4}, {1,8}, {10,11}, {5,6}, {9}).

```
python3 k4/suite/run.py --pred=k4/rc_pred.py:rc_c --pred=k4/rc_pred.py:rc_indep --pred=k4/rc_pred.py:rcy_indep \
    --pred=k4/rc_pred.py:keyplus_c --only=rc-n5m13-f1,rc-n5m12-f2      # results/k4_rc/suite_rc_pred.log, seconds
python3 k4/rt4_n5_indep.py results/k4_rc/indep_check_inst.json        # results/k4_rc/indep_check.log, about 1 min
python3 k4/rcy_indep.py results/k4_rc/rc_fail_hunt_ranked_pure_inst.json results/k4_rc/rc_fail_4515_inst.json
                                                                       # results/k4_rc/rcy_indep.log, about 2 min
python3 k4/dlrc_ref.py inst results/k4_rc/rc_fail_hunt_ranked_pure_inst.json   # dlrc.c against its reference
```
The portfolio runs use compute/k4-portfolio's harness at 6a8353b (`k4/portfolio.py`, `portfolio_preds.py`,
`portfolio_dump.c`, `portfolio_ref.py`; not merged here), e.g. on that branch with the inst file copied:
`python3 k4/portfolio.py inst results/k4_rc/rc_fail_4515_inst.json --name=rc4515 --jobs=1` and
`python3 k4/portfolio_ref.py compare results/k4_rc/rc_fail_4515_inst.json --every=8`.
