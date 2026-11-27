# Referee review: base-phantom's Proposition SEP and the certified rows K4.BASE.DEAD.N4, K4.BASE.P1FREE.N4 (`k4/base_phantom.md` on `proof/k4-base-phantom` at `0e6d9abc`, PR #139)

Referee: `proof/k4-referee`, 2026-11-27 (coordinator's queue).
- Read: `k4/base_phantom.md` §0, §2, §4 and the ledger rows K4.BASE.*.
- Data, read as data:
  - `results/k4_base_phantom/deadends_n4.jsonl.gz` (32,480 records);
  - `results/k4_base_phantom/data/two_move_starts_n4.json.gz`, byte-identical to the certifier's n = 4 export
    (sha256 `6159e38d…`).
- Checks:
  - `k4/referee/sep_ref.py` and `k4/referee/basephantom_ref.py` (own code: settlements, rounds, (L\*), (P2), SD,
    lifted completions and raw EFX₀ from my `cert_ref` / `oc1hall_ref` / `rsd_ref` / `base_ref`);
  - runs `basephantom_ref_runs.sh`; logs `results/k4_referee/sep_ref.log` and `basephantom_ref.log`.
- Nothing from `k4/base_phantom/` was run or imported.

## Verdict

| item | verdict |
|---|---|
| **Proposition SEP** (K4.BASE.SEP) and Corollary LIFT-SEP | **CORRECT** |
| **K4.BASE.DEAD.N4** | **CONFIRMED** on all 32,480 records |
| **K4.BASE.P1FREE.N4** | **CONFIRMED** on all 112,880 starts (exhaustive) |

## Proposition SEP

**Re-derivation.** A threat to k by X is v_k(X ∖ h) > τ for some h ∈ X, and X ∩ R_k ⊆ R_k ∖ T.
1. If |X| ≤ 2, X ∖ h holds at most one good, worth ≤ τ by P1-freeness. Likewise if X holds at most one good of
   R_k ∖ T.
2. For |T| = 3, R_k ∖ T ⊆ {y}, so part 1 applies. For |T| = 2, Lemma PHANTOM (refereed) leaves (P2) alone, since (P1)
   needs v_k(ℓ) > τ.
   - The statement also covers |T| = 1, through part 1: a threat needs ≥ 3 goods and two goods of R_k ∖ T.
3. (P3), (S-φ2) and (S-φ3) bound single goods by τ_φ, and P1-freeness bounds every good outside T. No agent is
   phantom-frozen for the same reason.

**Corollary LIFT-SEP.** It is Lemma LIFT\* for rounds (refereed, `lift.md` §9).
- (Φ) consists of "no bundle of X threatens a phantom" and "no later T threatens an earlier phantom". The second is
  admissibility's (P2).
- (L\*) at each round's end covers the real agents.
- The "only if" direction is trivial.

**Check** (`sep_ref.py`; random phantoms with |R_k| ≤ 4, strict values, |T| = 1–3 improving and P1-free, and random
bundles X disjoint from T, against the raw threat test):
- 1,156,525 tests, 61,300 of them threatened, and 0 violations of part 1 or of the triple case;
- the pair characterization is exact on 166,649 pair tests;
- *mutation* without P1-freeness: 4,848 part-1 violations and 774 pair mismatches.

## K4.BASE.DEAD.N4 (all 32,480 records)

Each record's path is replayed round by round. Each of its rounds must be one of my admissible rounds at the current
state. Then:
- the stored state is reached at all 32,480;
- no lifted completion exists: 0 failures;
- no admissible round exists: 0 failures;
- the feasibility flag (some EFX₀ allocation of I with every phantom holding exactly T; exhaustive) matches at 32,480,
  with 3,200 feasible and 29,280 infeasible, as stated;
- "ℓ alone on a present agent's base" (some phantom values a present agent's single good of R_k ∖ T above τ) holds at
  all 32,480.

*Not checked here:* that these are *all* the dead ends, i.e. a state-by-state enumeration. My rule-"any" exploration
(below) finds unsafe starts at exactly the 16,240 starts the records come from.

## K4.BASE.P1FREE.N4

The greedy process is explored exhaustively from every one of the 112,880 export starts, with my own code:
- at each reachable state without a lifted completion, every admissible round all of whose settlements are P1-free;
- a state is *stuck* if it has neither.

| rule | safe starts | unsafe starts |
|---|---|---|
| P1-free settlements only | **112,880** | **0** |
| any admissible round (ROUND-RSD as is) | 96,640 | **16,240** |

The second row reproduces the 16,240 starts from which a dead end is reachable (K4.BASE.DEAD.N4, and my earlier RSD
count, `lift.md` §8). So, independently of base-phantom's two implementations, **at n = 4 the P1-free greedy process
never gets stuck**.

## For the campaign

- SEP is a clean general fact. In the P1-free class the phantom constraints are exactly separations ({y_k, ℓ_k} not
  together in a bundle of ≥ 3 goods).
- At n = 4 the certified rows stand, now with my independent computation.
- Conjecture BASE-R (greedy GR) and the n = 5 refutation K4.BASE.P1FREE were not checked here.
