# COUNT: a global counting certificate for C₄ᵐⁱⁿ (route 1)

Workstream `proof/k4-strategy` (`k4/strategy.md` §2.1). Ledger row K4.STRAT.X.

**Statement tried.** For every strict profile of a k = 4 core with ω ≥ 1:
> **COUNT.** Some pool-optimal configuration at a min-frozen key has more robust free agents than free owners that
> threaten a frozen agent (r′ > |D|, threats with C = ∅).

**Why it was worth trying.** COUNT is a sound certificate, and it is the global form of the counting in Theorem Z′ and
#51's Lemma C:
- at a pool-optimal configuration every free agent is threatened by at most one owner (Lemma Z2 with U_y, as in the
  proof of Theorem F);
- robust agents are never threatened, so at least r′ owners threaten no free agent;
- if r′ > |D|, one of them threatens no frozen agent either, and it is a valid owner with C = ∅.

`k4/suite/predicates.py` (`count`) asserts that the certificate yields such an owner whenever it holds.

**Result: it fails at n = 2.** COUNT implies SIMPLE, and SIMPLE fails on the 720 n = 2 category-W profiles of #53.
- It fails on 1,408 of the 74,256 profiles of #53's n = 3 gap catalogue (every 100th gap profile plus every hard one).
- It also fails on the n = 4 and n = 5 samples (`results/k4_strategy/count_sweep.log`, run with #53's bench, every
  counterexample re-derived by #53's `gap_model`).
- SIMPLE (some configuration has a valid owner with C = ∅) holds on every one of those profiles. So the configurations
  that complete are not the ones the count sees.

**Smallest failing configuration:** n = 2, m = 5 (`k4/suite/instances/gap-w-n2-m5.json`, core 3 of
`results/k4_certs_2.json.gz`): agents {0, 2, 3, 4} and {1, 2, 3, 4}, both with values 2, 3, 6, 10; f = 1, ω = 2, best
r′ − |D| = 0 (`python3 k4/suite/run.py count --only=gap-w-n2-m5`: FAILS in both implementations). The first n = 3 one
in the catalogue sweep is `count-n3m8` (`k4/suite/instances/count-n3m8.json`):
- Sets and values:
  - agent 0: goods {0, 2, 6, 7} with values 3, 6, 2, 10;
  - agent 1: goods {1, 4, 6, 7} with values 3, 6, 2, 10;
  - agent 2: goods {3, 5, 6, 7} with values 3, 6, 2, 10.
- Three identical big-top agents (10 > 6 + 3) share goods 6 and 7; 7 is everyone's top.
- Every pool-optimal configuration has r′ ≤ |D|.
- C₄ᵐⁱⁿ holds (both implementations).

**Replay.** `python3 attempts/k4_strat_attempts.py` checks COUNT and the configuration form of C₄ᵐⁱⁿ with this PR's
`model.py` and #53's `gap_model`. `python3 k4/suite/run.py count --only=count-n3m8` does the same through the runner.
