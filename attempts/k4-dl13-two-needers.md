# DL₁₃ existence: "with several needers of the frozen good there is always an S1 shape"

Workstream `proof/k4-dl13` (`k4/dl13.md` §3, §5). Ledger row K4.DL13.X (REFUTED).

**Candidate.** At a T1-stuck state with f = 1 whose frozen good g has two or more needers, some best owner o needs g
and has, for some optimal X, a junk good c ∉ X blocked by the frozen agent x alone (the S1 shape of Corollary 9.1).
With several needers no owner can unfreeze x (every u-term is 0), so the deficit counts bundle sizes only, and at
n = 3 the candidate holds at all 9,743 such states of the runs; it would have reduced this regime to Lemma 10.

**Smallest failing configuration: `dl13-n4m10-needers`** (n = 4, m = 10; #53's hunt catalogue `hunt_n4_pure_s400k`,
core (m = 10, idx 18) of `results/k4_certs_4_pure.json.gz`, profile 115,72,285,150).
- agent 0: goods 0:6, 2:4, 6:5, 9:8; agent 1: 1:4, 5:3, 8:2, 9:8 (big-top); agent 2: 3:10, 6:8, 7:3, 8:6;
  agent 3: 4:6, 7:3, 8:2, 9:10 (big-top).
- P = ({9}, {1}, {3, 7}, {4, 8}), J = {0, 2, 5, 6}. Agent 0 is frozen on 9 (its top), needed by agents 1 and 3
  (v₁(1) = 4 < 8, v₃({4, 8}) = 8 < 10); agent 2 needs nothing (13 > 10). f = 1, ω = 3, def(P) = 1 (V = 4).
- The only best owner is agent 2 (Val 4, e.g. X = {3, 5, 7, 0}); it does not need 9. Its junk goods are blocked by
  agent 0 alone, so the state has a single frozen blocker but no S1 shape (owners 1 and 3, which need 9, have Val 3).
- DL₁₃ holds (38 (T3) moves lower the deficit), e.g. the plain swap ({0}, {9}, {3, 7}, {4, 8}): agent 1 takes 9,
  agent 0 takes 0 and becomes an owner of a 5-good bundle (def 0; Lemma 8).

**Frequency** (the runs of `k4/dl13.md` §4): row A5 of `results/k4_dl13/candidates.log` (all at n ≥ 4).

**Reproduce.** `python3 attempts/k4_dl13_attempts.py` (case 3, both implementations).
