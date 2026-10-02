# The θ-b case: "at every f = 1 target the frozen good has exactly two needers, both big-top"

Workstream `proof/k4-thetab` (`k4/thetab.md` §1, §5). Ledger row K4.TB.X (REFUTED).

**Candidate.** Every target of `k4/dl13.md` §6 item 2 at f = 1 lies in setting (H) of `k4/thetab.md` §3. A target is
a T3-stage state with θ-b S1 triples only, or without an S1 shape, that C1, C2, C3 do not certify. Setting (H): the
frozen good g has exactly two needers, both big-top on g. Theorems W and K of `k4/thetab.md` are stated in (H), so
the candidate would have confined the targets to it.

**It holds at 1,219 of the 1,223 target records** (all 1,154 at n = 3). It fails at four records at n = 4:
- two θ-a records with three needers (types 4 + 4 + BT);
- one θ-b record with three needers (4 + BT + BT);
- one θ-b record with two needers of types 4 + BT.

**Smallest failing configuration** (n = 4, m = 9). Source: #53's catalogue `gap_n4_3_s4000`, core (m = 9, idx 5) of
`results/k4_certs_4_n4_3.json.gz`, profile 106,48,94,3.
- Agents and values:
  - agent 0: goods 0:6, 2:3, 7:2, 8:10 (big-top: 10 > 6 + 3);
  - agent 1: goods 1:3, 3:6, 7:5, 8:7;
  - agent 2: goods 4:4, 5:5, 6:2, 8:8 (not big-top: 8 < 5 + 4);
  - agent 3: goods 4:3, 5:4, 6:2.
- P = ({0, 7}, {8}, {4, 6}, {5}), J = {1, 2, 3}. Agent 1 is frozen on 8 (its top); f = 1, ω = 2, def(P) = 1.
- The needers of 8 are agent 0 (big-top) and agent 2 (four goods, not big-top).
- The state is T1-stuck and key-optimal (the T3 stage), and C1, C2, C3 do not apply.

A plain swap still lowers the deficit there, and Corollary G1 of `k4/thetab.md` certifies one: the big-top needer 0
takes 8, x = agent 1 takes {1, 7} (one of agent 0's lower goods), and agent 3 owns.

**Reproduce.** `python3 attempts/k4_thetab_attempts.py` (case X2). The state's f, deficit, stage, needers and plain
swaps are computed by both implementations; whether C1–C3 apply, by implementation A only (they are `k4/dl13.md`'s
constructions). The list of targets: `python3 k4/thetab_targets.py` (`results/k4_thetab/targets.log`).
