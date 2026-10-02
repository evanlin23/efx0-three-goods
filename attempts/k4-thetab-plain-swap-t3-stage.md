# The T3 stage at f = 1: "with two big-top needers, a plain swap (no helper) suffices at the T3 stage"

Workstream `proof/k4-thetab` (`k4/thetab.md` §4, §5). Ledger row K4.TB.X (REFUTED).

**Candidate (Conjecture PS, plain-swap form).** At f = 1, at every T3-stage state P in setting (H) (two needers of
the frozen good g, both big-top on g), some *plain swap* lowers the deficit. A plain swap is a (T3) move without
helper: a needer z takes g, the frozen agent x takes an admissible A ⊆ J ∪ B_z, nobody else moves. It holds at every
one of the 1,223 f = 1 targets of PR #75's dumps (`k4/thetab.md` §4) and at every T3-stage state of #53's catalogues.

**It fails in the structured hunt** (`k4/thetab_scan.py hunt 1 …`, item 27942). Smallest failing configuration found
(n = 4, m = 8):
- Agents and values:
  - x = agent 0: goods 0:12, 4:10, 5:9, 6:8 (g = 0; not big-top);
  - agent 1: goods 0:13, 1:7, 2:5, 3:4 (big-top);
  - agent 2: goods 0:15, 1:8, 2:6, 3:4 (big-top; the two needers have the same goods);
  - agent 3: goods 1:8, 4:6, 5:7, 7:12.
- P = ({0}, {1}, {2, 3}, {4, 5}), J = {6, 7}.
- f = 1, ω = 1, def(P) = 1. P is at the T3 stage, and it is a target of `k4/dl13.md` §6 item 2 (no S1 shape; C1,
  C2, C3 do not apply).
- No plain swap exists at all. x's two best lower goods 4 and 5 are agent 3's base, and its third lower good 6 alone
  is not admissible (x would need 4 and 5). So x has no admissible base inside J ∪ B_z for either needer z.
- 21 (T3) moves with one helper lower the deficit. In each, the helper is agent 3: it gives up 4 or 5 to x and takes
  its top good 7 from the junk. For example, agent 1 takes 0, x takes {4}, agent 3 takes {7}, and agent 2 owns
  {1, 2, 3} or more: def(P′) = 0. Corollary G1 of `k4/thetab.md` with one helper certifies this move.

So the θ-b / non-S1 regime at n ≥ 4 needs the helper of (T3); no plain-swap statement can cover it. The data are
consistent with the weaker form: some (T3) move with at most one helper, certified by Lemma G, lowers the deficit
(K4.TB.PS).

**Reproduce.** `python3 attempts/k4_thetab_attempts.py` (case X3, both implementations: the state, the absence of
plain swaps, the number of (T3) moves, and the deficit of the certified helper move by both).
