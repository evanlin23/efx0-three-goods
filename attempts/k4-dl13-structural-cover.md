# DL₁₃ existence: "one of the three structural repairs always applies"

Workstream `proof/k4-dl13` (`k4/dl13.md` §4, §5). Ledger row K4.DL13.X (REFUTED).

**Candidate.** At every T1-stuck state with f ≥ 1 (`k4/dl13.md` §1) one of the three repairs with structural
hypotheses applies: C1 = Corollary 9.1 (the S1 repair), C2 = Corollary 11.1 (the blocker swap), C3 = Corollary 8.2
(the Lemma 7 swap of a big-top frozen agent with a unique needer, at most one helper). Each of them is proved to lower
the deficit when its hypotheses hold; the candidate would have made the existence step a matter of showing that
T1-stuckness forces one of these shapes.

**Smallest failing configuration: `dl13-n3m6`** (n = 3, m = 6, f = 1, def 1), the state of
`attempts/k4-dl13-frozen-obstruction.md`: P = ({2}, {3, 5}, {4}), J = {0, 1}, agent 0 frozen on 2, agent 2 its only
needer, agent 1 satisfied.
- C1 needs an S1 shape: the blockers of the best owners are agents 2 and 1, both free.
- C2: owner 1 (X = {3, 5}) has each junk good blocked by agent 2 alone, a free needer of 2, and agent 2 holding 2 is
  not threatened by {0, 3, 5} or {1, 3, 5} (θ₂ = 7 ≤ 8); but agent 0 would have to take an admissible base outside
  X ∪ {c} inside J ∪ B₂ = {0, 1, 4}, i.e. inside {0, 4} ∩ R₀ (resp. {4}), and every such base leaves agent 0 needing
  good 5 (worth 6 > 4 and 6 > 1 + 4), which is not in 𝒩 = {2}. Owner 2's blocker (agent 1) needs nothing.
- C3: agent 0 is not big-top (8 < 6 + 4).

DL₁₃ holds there through a role swap with a helper that is not of shape C3 (`attempts/k4-dl13-frozen-obstruction.md`).

**Frequency** (the runs of `k4/dl13.md` §4): C1, C2, C3 together miss a repair at the states counted in
`results/k4_dl13/candidates.log` (row A7); the certificates C1* and C2* (Corollary 9.2, Lemma 11) reach most of them,
and the rest are listed in `k4/dl13.md` §4.

**Reproduce.** `python3 attempts/k4_dl13_attempts.py` (case 1, implementation A); the count: row A7 of
`results/k4_dl13/candidates.log`.
