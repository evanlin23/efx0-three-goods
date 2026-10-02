# T3 stage at f ≥ 2: "one of the structural repairs along need paths always applies"

Workstream `proof/k4-f2` (`k4/f2.md` §4, §6). Ledger row K4.F2.X (REFUTED).

**Candidate.** At every T3-stage state with f ≥ 2 (def(P) > 0, def(P) = def*(κ(P)), no improving (T4) move), some best
owner o with an optimal bundle X satisfies the hypotheses of one of the four structural corollaries of `k4/f2.md` §3.2:
Corollary 9.1⁺ (the S1 repair through a need path), 11.1⁺ (the blocker swap through a need path), 8.2⁺ (the Lemma 7
swap through a need path) or 11.2⁺ (the κ swap). Each is proved in writing to lower the deficit when its hypotheses
hold, so the candidate would have reduced the T3 stage to showing that one of these shapes is forced. It is the f ≥ 2,
need-path version of `attempts/k4-dl13-structural-cover.md` (f = 1, without 11.2⁺).

**Smallest failing configuration** (the smallest by (n, m) among the 33,816 T3-stage states of `k4/f2.md` §1):
n = 4, m = 8, f = 2, ω = 2, a strict profile of a core (k4/suite/model.py's checks),
- sets [[0,2,4,7],[1,4,5,6],[3,5,6,7],[5,6,7]], values [[2,3,4,8],[6,5,8,4],[4,8,1,6],[4,2,3]];
- P = ({0,2}, {5}, {3,6}, {7}), def(P) = 1, agents 1 and 3 frozen (on 5 and 7), case A-z of `k4/f2.md` §1.
- The only single block of a best owner is (owner 0, blocker 1): agent 1 is frozen, but owner 0 is not the free end
  of a need path to it with θ-ok (9.1⁺ fails), the blocker is not free (11.1⁺ fails), and 8.2⁺ and 11.2⁺ do not
  apply either (`k4/f2_lemmas.py`).
- DL_{R_C} holds there: (T3) and (T3⁺) moves lower the deficit, and the certificate C8⁺ of `k4/f2_lemmas.py` (a path
  swap after which x owns a bundle beating Val*(P), computed exactly by Lemma 8⁺) applies with k = 0.

**Frequency.** 694 of the 33,826 T3-stage state records of `k4/f2.md` §4 (main 232, n5 432, rc 30) are certified only
by C8⁺ (595) or C11⁺ (99) (`results/k4_f2/coverage_*.log`, `coverage5_*.log`).

**Reproduce.** `python3 attempts/k4_f2_attempts.py` (case "n = 4, m = 8"): implementation A (k4/f2_lemmas.py on
k4/suite/model.py) checks that no corollary applies and C8⁺ does; implementation B (main's k4/dl134_xcheck.py with its
own owner table, single blocks and need paths) confirms the T3 stage, the improving move kinds, the single block and
the absence of a θ-ok S1 shape through a need path and of a free single blocker.
