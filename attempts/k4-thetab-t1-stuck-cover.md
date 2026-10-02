# The θ-b setting: "W, K or G1 with a plain swap applies at every T1-stuck state with two big-top needers"

Workstream `proof/k4-thetab` (`k4/thetab.md` §3–§5). Ledger row K4.TB.X (REFUTED).

**Candidate.** At f = 1, at every T1-stuck state in setting (H), the hypotheses of Theorem W, Theorem K or Corollary
G1 of `k4/thetab.md` with a plain swap (no helper) hold. A T1-stuck state is one where no (T1) move lowers the deficit
(`k4/dl13.md` §1); setting (H) means two needers of the frozen good, both big-top. These hypotheses hold at every
f = 1 target of `k4/thetab.md` §1. The T3 stage asks in addition that no (T2) rotation lowers the deficit, so the
candidate asked whether that extra hypothesis is needed. It is not enough either: the candidate fails at the T3 stage.

**Smallest failing configuration found: n = 4, m = 8**, the T3-stage (hence T1-stuck) state of
`attempts/k4-thetab-plain-swap-t3-stage.md`, where no plain swap exists at all. The state below (n = 4, m = 10) shows
a different failure: a plain swap exists there, but none of W, K, G1 names it. Source: #53's catalogue
`gap_n4_pure_s4000`, core (m = 10, idx 13) of `results/k4_certs_4_pure.json.gz`, profile 60,8,93,84.
- Agents and values:
  - agent 0: goods 0:3, 2:10, 7:6, 9:8;
  - agent 1: goods 1:2, 5:3, 8:8, 9:4 (big-top);
  - agent 2: goods 3:5, 6:3, 8:7, 9:6;
  - agent 3: goods 4:4, 7:2, 8:8, 9:3 (big-top).
- P = ({0, 9}, {1, 5}, {8}, {4, 7}), J = {2, 3, 6}.
- Agent 2 is frozen on 8, needed by agents 1 and 3; agent 0 needs nothing. f = 1, ω = 3, def(P) = 1.
- P is T1-stuck but not key-optimal: a rotation of the free agents lowers the deficit.
- None of W, K, or G1 with a plain swap applies:
  - x's best lower good 9 lies in the base of agent 0, so (W1) fails;
  - agent 0 holding {0, 9} (worth 11) is threatened by its goods 2 and 7 (worth 16), and it has no slot, so it is not
    tame, and no removal set fits the budgets of K and G1.

A plain swap still lowers the deficit there (the replay lists them). Its bundle is owned by x itself (Lemma 8 of
`k4/dl13.md`), not by an unmoved agent, so Lemma G does not see it. Corollary G1 with one helper does certify a swap
that lowers the deficit (`k4/thetab_lib.theorems` returns 'G1h'; the replay prints the certificate).

**Reproduce.** `python3 attempts/k4_thetab_attempts.py` (case X4). The state's f, deficit, T1-stuckness,
key-optimality, needers and plain swaps are computed by both implementations, and so is the deficit after the
certified swap; whether W, K, G1 apply, by implementation A only.
