# The T3 stage at f = 1: "at every T3-stage state with two needers, some (T3) move lowers the deficit"

Workstream `proof/k4-thetab` (`k4/thetab.md` §5). Ledger row K4.TB.X (REFUTED).

**Candidate (Conjecture PS, single-step form).** At f = 1, at every T3-stage state P whose frozen good has two or more
needers, some (T3) move with at most one helper (giving up a good) lowers the deficit, and Corollary G1 of
`k4/thetab.md` certifies one. A T3-stage state is one where no (T1), (T2) or (T4) move lowers the deficit; at f = 1
these are the deficit-minimal states of their key. It held at every one of the 1,223 f = 1 targets of PR #75's dumps
and at every T3-stage state of this workstream's scans.

**It fails** (found by the cloud session compute/k4-rc, `results/k4_rc/FAILURES.md` on origin/compute/k4-rc, 45
profiles of one core; reported by the coordinator). Smallest configuration known (n = 5, m = 13): core pos 4604
(idx 58) of `results/k4_certs_5_pure.json.gz`, profile 44,118,8,8,158.
- Agents and values:
  - agent 0: goods 0:3, 2:5, 9:6, 11:7;
  - agent 1: goods 1:6, 6:5, 10:4, 12:8;
  - agents 2 and 3: goods 3:2, 7:3, 11:8, 12:4 and 4:2, 8:3, 11:8, 12:4 (both big-top on 11);
  - agent 4: goods 5:6, 9:4, 10:1, 12:8.
- P = ({11}, {12}, {3, 7}, {4, 8}, {5, 9}), J = {0, 1, 2, 6, 10}. Agent 0 is frozen on 11, needed by agents 2 and 3
  (setting (H) of `k4/thetab.md` §3). f = 1, def(P) = 1, and P is at the T3 stage. It is a target in the sense of
  `k4/thetab.md` §1 (no S1 shape; C1, C2, C3 do not apply).
- P has 8 (T3) moves, and each leads to a state of deficit 1. So no (T3) move lowers the deficit, with or without
  helper. The better states need a helper that grows its base, or two helpers (compute/k4-rc's analysis).

**The key form holds there.** P's key (agent 0 frozen on 11) has 35 states, all of deficit def* = 1. From other
states of the key, 936 (T3) moves reach a key of smaller least deficit, and 756 of them reach a state of deficit
below 1. Corollary G1 certifies such moves, including plain swaps. Example: from ({11}, {1, 6}, {12}, {4, 8}, {5, 9}),
agent 3 takes 11 and agent 0 takes {0, 2}; with agent 1 as owner, G1's bound is 0 and def(P′) = 0. The coordinator's
witness: from ({11}, {6, 10}, {12}, {4, 8}, {5, 9}), agent 0 takes {9}, agent 2 takes {11}, and helper 4 gives up
{5, 9} for {12}; def(P′) = −1, the least deficit of the new key.

So the existence statement must be stated on the key graph: the repair may start from any state of the key
(`k4/dl13.md` §2.3, Remark). `k4/thetab.md` §5 restates Conjecture PS that way.

**Reproduce.** `python3 attempts/k4_thetab_attempts.py` (case X5). Both implementations compute: the state (f, deficit,
T1-stuckness, key-optimality, needers, plain swaps); its (T3) moves and their deficits; the key's least deficit and
states; the (T3) moves from the key to a better key and to a state below def*; and the coordinator's witness move.
Corollary G1's certificates come from implementation A only.
