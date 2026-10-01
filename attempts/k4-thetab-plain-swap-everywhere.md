# The θ-b case: "with two big-top needers, a plain swap lowers the deficit at every state"

Workstream `proof/k4-thetab` (`k4/thetab.md` §3, §5). Ledger row K4.TB.X (REFUTED).

**Candidate.** At f = 1, assume the frozen good g has exactly two needers y1 and y2, both big-top on g (setting (H) of
`k4/thetab.md` §3). Then at every min-frozen P with def(P) > 0 some *plain swap* lowers the deficit. A plain swap is
a (T3) move without helper: a needer z takes g, the frozen agent x takes an admissible A ⊆ J ∪ B_z, nobody else
moves.

At n = 3 this is Corollary N3 of `k4/thetab.md` (written proof). It would have made the T3-stage hypothesis
unnecessary for the θ-b case at every n.

**Smallest failing configuration found** (n = 4, m = 9). Source: #53's catalogue `gap_n4_pure_s4000`, core
(m = 9, idx 5) of `results/k4_certs_4_pure.json.gz`, profile 38,20,245,105.
- Agents and values:
  - agent 0: goods 0:3, 2:4, 4:2, 8:8 (big-top: 8 > 4 + 3);
  - agent 1: goods 1:2, 3:6, 7:3, 8:10 (big-top);
  - agent 2: goods 4:8, 5:6, 6:3, 7:4;
  - agent 3: goods 5:4, 6:7, 7:2, 8:10.
- P = ({0, 2}, {1, 3}, {5, 6}, {8}), J = {4, 7}.
- Agent 3 is frozen on 8, and its needers are agents 0 and 1 (setting (H)). Agent 2 needs nothing.
- f = 1, ω = 2, def(P) = 1.
- No plain swap lowers the deficit. Agent 2, a third agent holding {5, 6} (worth 9 to it), is threatened by every
  owner bundle that contains its goods 4 and 7 (worth 12 > 9), and 4 and 7 are the only junk goods. So Theorem W's
  hypothesis (W3) and Theorem K's (K3) fail.

P is **not** at the T3 stage. It is not even T1-stuck: agent 0 re-basing to {2} lowers the deficit, and so do
several other (T1) moves. So this refutes the candidate without the stage hypothesis; it does not refute Conjecture PS
of `k4/thetab.md` §5.

**Frequency.** In the scans of `k4/thetab.md` §4 (`results/k4_thetab/scan_*.log`, rows "(H) | other | … | NO plain
swap"), see that section's table.

**Reproduce.** `python3 attempts/k4_thetab_attempts.py` (case X1, both implementations: the state's f, deficit,
stage, needers and every plain swap's deficit agree).
