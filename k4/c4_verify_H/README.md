# Independent verification of Proposition H (`k4/c4.md` §7)

This folder is a second, independently written encoding of Proposition H, as AGENTS.md §5 requires for a refutation. Its author is a verifier agent working for the coordinator. It shares no code with the author of `k4/c4.md` (`k4/c4tools/`, `k4/c4_chain.py`, `k4/c4_lb4w.c`).

The model follows the Lean definitions of LB₄ʳ (`lean/EFX/LB4R.lean`: `phase1State`, `UpRun`, `RotStep`/`RotChecks`, `Output`, `ownerNeeds`). Where `k4/lb4.md` and LB4R.lean differ, it follows Lean, which is the more permissive of the two.

## Claim checked
On the cores H_t of `k4/c4.md` §7, run LB₄ʳ with index insertion (τ = []) under all three upgrade policies, every owner (or none), and both owner-needs conventions (from the base; from the bundle, i.e. Lean's `ownerNeeds`). The least number of nested rotations after which some reachable state has an output is 1, 2, 2, 3, 4 for t = 1, …, 5. In particular, **no state of H_5 reachable with ≤ 3 rotations has an output**, so LB₄ʳ, which is bounded by 3 rotations, fails on H_5. Hence `EFX.LB4R.TheoremC4index`, and so `TheoremC4`, are false. They are false only at types large enough to hold H_5 (≥ 21 agents, ≥ 53 goods).

| t | n, m | new states at depth 0/1/2/3 | fails with | succeeds with |
|---|---|---|---|---|
| 1 | 5, 13 | 1/6/7/6 | 0 rotations | 1 |
| 2 | 9, 23 | 1/12/104/276 | ≤ 1 | 2 |
| 3 | 13, 33 | 1/18/237/1926 | ≤ 1 | 2 |
| 4 | 17, 43 | 1/24/406/4740 | ≤ 2 | 3 |
| 5 | 21, 53 | 1/30/611/8934 | ≤ 3 (0 outputs in all 9,576 states) | 4 (the matching construction, `matching.py`) |

- No upgrade applies on any H_t, under any policy. The state counts equal the author's at every depth.

## Files
- **Core and instance:**
  - `hcore.py`: H_t built from the prose of §7, plus the Task 1 checks (connected k = 4 core, strict profile, the §7 allocation EFX₀ by the raw definition). Logs: `task1_core.log`, `task1_negative.log`.
- **Model and encoding A:**
  - `lb4r.py`: the LB₄ʳ model, a literal checker `output_check`, and exact test A. A single clause model is solved with Glucose (python-sat) or HiGHS MILP (scipy); the H_4/H_5 runs used MILP.
  - `run_H.py`: exhaustive over the reachable states. Logs: `run_H{1..5}_q*.log`, `state_counts.log`.
- **Encoding B:** `enc_b.py`, written separately (MILP, one row per agent and removed good; frozen status encoded both ways; its own needs and ω code). Driver `run_encb.py`; logs `run_encb_H{4,5}_q3.log`. Encodings A and B agree on every state of H_4 and H_5 with ≤ 3 rotations, every owner, both conventions.
- **Validation of the exact tests:**
  - against a Python brute force over every junk assignment (`bfpy.py`, `validate_random.py`, `validate_cov.py`);
  - against a separate C brute force that recomputes needs, NA and ω (`bf.c`, `validate_bf_random.py`);
  - on every state of H_1 and H_2 with ≤ 2 rotations (`validate_H.py`, `validate_encb*.py`);
  - between the two backends (`validate_backends.py`).

  About 140,000 cases, 0 mismatches (`validate_*.log`). Three bugs planted in the encoder during development were each caught. The mutants are not stored.
- **C₄∃ on H_t:** `task4.py` gives three `SoundCompletion` witnesses for t ≤ 8 (`task4_c4exists.log`). H_t does not threaten C₄∃.
- **The gap in the written proof:** `gap_example.py` / `gap_example.log`. An x holding {a, g_j}, with g_j junk once y_{j−1} has ended a chain, is safe with both b and c in the owner's bundle (11 ≥ 10). So the proof's "x forces b or c out" must also allow "g_j in x's own slot" (for ℓ, "z"). The goods and slots involved are distinct, so the per-agent bounds, and the proposition, stand.

## Reproduce
Requires python-sat, numpy and scipy (for HiGHS through `scipy.optimize.milp`).
```
cd k4/c4_verify_H
python3 hcore.py                              # Task 1 checks
python3 run_H.py 4 3                          # H_4: fails with ≤ 2, succeeds with 3 (~11 min on 4 CPUs)
python3 run_H.py 5 3                          # H_5: no output with ≤ 3 rotations (~20 min on 4 CPUs)
python3 run_encb.py 5 3                       # encoding B on H_5 (~1 h)
python3 matching.py                           # H_5 with 4 rotations: the matching-construction states have outputs
gcc -O2 -o bf bf.c && python3 validate_bf_random.py 1 2000
```
