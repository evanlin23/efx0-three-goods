# Referee report: the certifier's refutation of TTC's R2-M and R2★ at n = 4 (`results/k4_oc1max/r2m_fails_n4.jsonl`)

Referee: `proof/k4-referee`, 2026-11-27, coordinator's queue (burst 5, item 2).
- Read:
  - `k4/ttc.md` §14.6 on `claude/k4-ttc`: the definitions of R2, R2★ and R2-M, and the setting;
  - the docstring of the certifier's `k4/oc1cert/verify_r2.py` on `main`, for the precise completion constraints only;
  - the failure file `results/k4_oc1max/r2m_fails_n4.jsonl` (306 starts; commit `c0de02c` on `main`).
- Check: `k4/referee/r2m_ref.py`, log `results/k4_referee/r2m_ref.log`.
  - It is my own code: canonical-chain enumeration, the constrained completion, and the core and perfect-start tests.
  - SD, the one-absorber completion, the §29 moves and raw EFX₀ come from `cert_ref.py`.
  - Nothing from `k4/oc1cert/` or `k4/sdc/` was run or imported.

## Verdict: CONFIRMED on all 306 starts

The coordinator asked for a raw replay of 5 instances. I replayed all 306, since each takes milliseconds. Every one
satisfies the hypotheses of R2-M, and R2-M fails there:
- the instance is a strict connected k = 4 core (K4.CORE conditions and strict types, checked by enumeration);
- the start is perfect: some order gives the picks (I counted the orders);
- there are at least two receivers;
- the start is hard: no one-absorber completion of the picks.

**R2-M fails.** I enumerated *every* canonical chain (x₀ ∈ D, x₁ valuing y_{x₀} above y_{x₁}, x_t a receiver, §29
official rules with H sets) and every allocation of the remaining junk. In none of them does a raw-EFX₀ completion
exist in which:
- nobody, x₀ included, receives two or more junk goods;
- the agents other than x₀ that hold two or more base goods receive none.

**R2★ also fails on 74 of the 306.** That is the same completion without the second constraint.

**R2 itself holds on all 306.** Some one-absorber completion exists after one official move, so these are
counterexamples to the sharpened target only, as the notes say.

On the first five lines, my counts match the certifier's `verify_r2m_fails_n4.log` exactly:
- the orders giving the picks: 4, 4, 5, 5, 5;
- the canonical-chain states: 16, 15, 15, 18, 15;
- R2★ fails on lines 1, 2, 3 and 5, and holds on line 4.

| | count |
|---|---|
| starts (distinct hypergraphs) | 306 (306) |
| strict connected k = 4 core / perfect / ≥ 2 receivers / hard | 306 / 306 / 306 / 306 |
| R2-M fails | **306** |
| R2★ fails | **74** |
| R2 holds (one official move repairs) | 306 |

**Scope.** These 306 starts are what the refutation needs: one failure refutes R2-M. The certifier's other claims, R2★
failing on 230 cores and R2-C certified at n = 4, come from its exhaustive run over the 1,002 n = 4 cores, and I did
not re-run that. The 74 R2★ failures here already refute R2★.
