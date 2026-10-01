# The T3 stage at f = 1: "Theorem W, Theorem K or Corollary G1 applies at every T3-stage state with two needers"

Workstream `proof/k4-thetab` (`k4/thetab.md` §3–§5). Ledger row K4.TB.X (REFUTED).

**Candidate.** At f = 1, at every T3-stage state whose frozen good g has two or more needers, the hypotheses of
Theorem W, Theorem K or Corollary G1 of `k4/thetab.md` hold. These are conditions on P alone, each naming a plain swap
that lowers the deficit to at most 0. The candidate would have extended the structural cover of the targets (where it
holds at all 1,223 records, `k4/thetab.md` §4) to every such state.

**It fails at n = 3 when no needer is big-top.** W, K and G1 swap a big-top needer z, which holding g is threatened
only by bundles containing all three of its lower goods. A needer that is not big-top is threatened by its pairs worth
more than g.

**Smallest failing configuration** (n = 3, m = 6). Source: #53's catalogue `gap_n3`, core (m = 6, idx 8) of
`results/k4_certs_3.json.gz`, profile 11,11,246.
- Agents and values:
  - agent 0: goods 0:2, 3:4, 4:5, 5:8;
  - agent 1: goods 1:2, 3:4, 4:5, 5:8;
  - agent 2: goods 2:8, 3:6, 4:3, 5:10.
- P = ({4}, {1, 3}, {5}), J = {0, 2}.
- Agent 2 is frozen on 5 (its top). Its needers are agents 0 and 1, both with four goods and neither big-top
  (8 < 5 + 4).
- f = 1, def(P) > 0, and P is at the T3 stage.
- A plain swap still lowers the deficit there. Lemma G certifies one, with z's threats (its pairs worth more than g)
  among the edges that the removal set C must meet.

**Frequency.** In the scans of `k4/thetab.md` §4 the T3-stage states outside setting (H) that W, K and G1 miss are
rows "needers … | T3stage | theorem -" of `results/k4_thetab/scan_*.log`. Lemma G certifies a plain swap at each of
them. At the targets none is missed.

**Reproduce.** `python3 attempts/k4_thetab_attempts.py` (case X3). The state's f, deficit, stage, needers and plain
swaps are computed by both implementations; whether W, K, G1 apply, by implementation A only (they are this
workstream's statements).
