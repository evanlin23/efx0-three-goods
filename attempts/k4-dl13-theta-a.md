# DL₁₃ existence: "a failing S1 repair is always of kind (θ-b)"

Workstream `proof/k4-dl13` (`k4/dl13.md` §2 Lemma 10, §5). Ledger row K4.DL13.X (REFUTED).

**Candidate.** Whenever the S1 repair (Corollary 9.1) fails at an S1 triple (o, X, c) of a T1-stuck state because o
holding the frozen good g is threatened by X ∪ {c}, the failure is of kind (θ-b) of Lemma 10 (o big-top on g with its
lower goods in X ∪ {c}), never (θ-a) (a set of at most two of o's goods in X ∪ {c} worth more than g). At n = 3 it
holds at every S1 triple of every T1-stuck state of the runs (off the T1-stuck states (θ-a) occurs at n = 3 already:
`results/k4_dl13_stuck/lemmas_gap_n3.log`); it would have confined the θ-failures at T1-stuck states to big-top owners.

**Smallest failing configuration: `dl13-n4m10-theta-a`** (n = 4, m = 10; #53's catalogue `gap_n4_pure_s4000`, core
(m = 10, idx 12) of `results/k4_certs_4_pure.json.gz`, profile 10,88,73,21).
- agent 0: goods 0:2, 2:4, 8:3, 9:8 (big-top); agent 1: 1:4, 5:8, 8:3, 9:10; agent 2: 3:4, 6:3, 8:6, 9:8;
  agent 3: 4:2, 7:6, 8:7, 9:10.
- P = ({0, 2}, {9}, {3, 6}, {4, 7}), J = {1, 5, 8}. Agent 1 is frozen on 9 (its top), needed by agents 0, 2 and 3.
  f = 1, ω = 3, def(P) = 1 (V = 4; each free agent has Val 4, e.g. owner 2 with X = {1, 3, 6, 8}).
- For each owner the junk good 5 is blocked by agent 1 alone (S1 shapes). Owner 2 holding 9 would be threatened by
  {1, 3, 5, 6, 8}: θ₂ = v₂({3, 6, 8}) = 13 > 8, and already the pair {3, 8} is worth 10 > 8: kind (θ-a) (Lemma 10:
  then g has another needer, as here). Owner 3: the pair {7, 8} is worth 13 > 10, (θ-a) again. Owner 0 is big-top:
  θ₀ = v₀({0, 2, 8}) = 9 > 8 with no pair above 8, (θ-b).
- DL₁₃ holds (44 (T3) moves lower the deficit), e.g. ({2}, {5}, {9}, {4, 7}): agent 2 takes 9, agent 1 takes 5,
  agent 0 (helper) gives up 0 and keeps 2, and owner 3 owns a 6-good bundle (def −1).

**Frequency** (the runs of `k4/dl13.md` §4): row A6 of `results/k4_dl13_stuck/candidates.log`. Lemma 10(θ-a) forces a
second needer besides o; in the runs every such state has three needers of the frozen good (`k4/dl13_lemmas.py
--stats`, regime counts in `results/k4_dl13_stuck/stats.log`).

**Reproduce.** `python3 attempts/k4_dl13_attempts.py` (case 4, both implementations).
