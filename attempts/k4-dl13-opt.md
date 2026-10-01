# DL₁₃^opt: "at T4-optimal states, (T1) or (T3) always lowers the deficit"

Workstream `proof/k4-dl13` (`k4/dl13.md` §2.2). Ledger row K4.DL13.OPT (REFUTED). The instance was found by the
compute workstream (`dl13-n4m9-rot` of `attempts/k4-dl13-refuted.md`, merged in #74, where it refutes DL₁₃₄,
K4.DL2.T134); it is replayed here with this workstream's two implementations.

**Candidate.** After DL₁₃ failed at n = 4, f = 3 (every failure has a cycle in the need digraph of the frozen
agents, and a frozen rotation repairs it; Lemma 12), the proposed repair of the conjecture was DL₁₃^opt: at f ≥ 1,
every *T4-optimal* min-frozen P (acyclic frozen need digraph) with def(P) > 0 has a (T1) or (T3) neighbour with a
smaller deficit. With Lemma 12 it would have implied TARGET₄ (Proposition 12.2).

**Smallest failing configuration found: `dl13-n4m9-rot`** (n = 4, m = 9, f = 1; #53's catalogue `gap_n4_pure_s4000`,
core 123 (m = 9, idx 0) of `results/k4_certs_4_pure.json.gz`, profile 7,196,164,44). At f = 1 there is one frozen
agent, so every state is T4-optimal and DL₁₃^opt says the same as DL₁₃.
- agent 0: goods 7:10, 2:6, 1:3, 0:2 (big-top: 10 > 6 + 3);
- agent 1: 5:8, 2:7, 4:4, 8:2;
- agent 2: 6:7, 3:6, 4:5, 5:3;
- agent 3: 7:8, 8:4, 3:3, 6:2.

P = ({7}, {2, 8}, {4, 5}, {3, 6}), J = {0, 1}.
- Needs: N₀ = ∅ (7 is agent 0's top), N₁ = ∅ (9 > 8), N₂ = ∅ (8 > 7), N₃ = {7} (5 < 8). Agent 0 is frozen, agent 3 is
  its only needer; f = 1, σ = 2n − m = −1, ω = 2, S = 0.
- Owner 1: {0, 2, 8} and {1, 2, 8} are safe; {0, 1, 2, 8} threatens agent 0 only (θ₀ = 2 + 3 + 6 = 11 > 10). Owner 2:
  {4, 5} plus any junk good threatens agent 1 (θ₁ = 4 + 8 = 12 > 9). Owner 3: {3, 6} plus a junk good threatens agent
  2 (θ₂ = 6 + 7 = 13 > 8). u = 0 throughout (agent 3 needs 7, and as an owner its only safe bundle {3, 6} is worth
  5 < 8). V = 3, def(P) = 1.
- No (T1) and no (T3) move lowers the deficit (both implementations). The natural (T3) repair, the Lemma 7 swap
  (Corollary 8.2: agent 3 takes 7, agent 0 owns its lower goods {0, 1, 2} and unfreezes agent 3), needs good 2 from
  agent 1, and agent 1 has no admissible base left inside J ∪ B₃ ∪ B₁ minus {0, 1, 2}: only {8} (worth 2), which
  leaves it needing 5 and 4, outside 𝒩 = {7}. Its repair would need a good of agent 2, i.e. a second helper.
- The 54 min-frozen states with a smaller deficit change three agents (24) or all four (30); e.g.
  ({7}, {5}, {6}, {8}), def 0: the three free agents rotate (agent 1 takes 5 from agent 2, agent 2 takes 6 from agent
  3, agent 3 takes 8 from agent 1), a (T2) move.

So rotations of free agents are needed at f ≥ 1 as well; the coordinator's successor target is R_T4 = (T1) ∪ (T2) ∪
(T3) ∪ (T4) (`k4/dl13.md` §2.3; Conjecture DL_RT4, K4.DL2.RT4E).

**Reproduce.** `python3 attempts/k4_dl13_attempts.py` (case 5: `k4/dl13_stuck.py`'s Profile and main's
`k4/c4x_check.py` with the separately written (T1), (T3) tests of the script; the check that the instance is a strict
core uses `k4/suite/model.py`).
