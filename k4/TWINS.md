# k = 4 minimal counterexample, round 3: twins, near-twins, double edges

Workstream `proof/k4-twins`. New local reductions for a minimal counterexample to TARGET₄, in the certified style of
`k4/MINCEX.md` (rows K4.MC0–K4.MC7): a configuration (S, I) with its agents' types is excluded once every admissible
local state of an EFX₀ allocation of a smaller gadget instance has an extension (Lemma K4.MC1 = M1, M1(b) at k = 4).
Generator `k4/twins4.py` (on `k4/reduce4.py`); independent check `k4/check_twins4.py` (the checking functions of
`k4/check_reductions4.py`, which share no code with the generator, with the new configurations hard-coded).

Work in progress; this file is filled in as results are certified.

## 1. Configurations

- **dbl-K1-K2[-cC]** (*double edge*): two agents e, f of kinds K1, K2 ∈ {Q3, P4, Q4} share two goods g0, g1 that no
  other agent values (in Γ′, a double edge between two agents of degree ≥ 3). Their other shared goods are boundary
  goods; C of them are common to e and f. I = {g0, g1} plus the private goods of e and f.
- twins (same relevant set), near-twins (three common goods), the claw (three P3 agents on a good of degree 3) and Q4
  stars (a Q4 agent sharing goods of degree 2 with P3 agents): explored, see §3.

## 2. Certified so far (both implementations agree)

| configuration | profiles | reduced |
|---|---|---|
| dbl-Q3-Q3 | 36 | **36** |
| dbl-Q3-Q3-c1 (twins with R = {g0, g1, a}) | 36 | **36** |
| dbl-Q3-P4 | 1,728 | **1,728** |
| dbl-Q3-P4-c1 | 1,728 | **1,728** |
| dbl-Q3-Q4 | 1,728 | 1,708 |
| dbl-Q3-Q4-c1 | 1,728 | **1,728** |

## 3. Explored (coverage only, single implementation)

| configuration | profiles | reduced (DEL, copy gadgets, one-agent gadgets with 0–2 gadget goods) |
|---|---|---|
| twins-Q3-0 (R = {a, b, c}, all boundary) | 36 | 0 |
| twins-Q3-1 (one good of degree 2) | 36 | 26 |
| twins-P3 (two P3 agents on the same two shared goods) | 36 | 26 (two gadget goods add nothing) |
| near-Q3-Q4-0 (all three common goods boundary) | 1,728 | 0 |
| near-Q3-Q4-1 | 1,728 | 740 |
| near-Q3-P4-0 | 1,728 | 432 |
| near-Q3-P4-1 | 1,728 | 1,564 |
| claw | 216 | 177 |
