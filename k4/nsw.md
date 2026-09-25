# Nash social welfare as a potential for LB₄ʳ's rotations, and bounded LB₄ʳ on the (4, 3) class (compute/k4-nsw)

EVIDENCE only (PROMPT.md §5 rule 3). Two leads for the open step of the k = 4 proof:

1. **NSW-guided unbounded rotations.** `k4/c4.md` §7 (PR #33) shows that LB₄ʳ with a fixed insertion order needs
   unboundedly many rotations: ⌈2t/3⌉ on the cores H_t. A proof then needs a potential that makes unbounded rotation
   terminate with an output. `proofs/pq_bounded.md` §2–3 points to Nash social welfare (Kaviani et al., rankpath
   shifts).
2. **The (k, p) = (4, 3) class.** In these cores every good is valued by at most 3 agents, which excludes every H_t.
   The question is whether bounded LB₄ʳ ever fails there.

## Tools
- `k4/lb4_nsw.c`: `k4/c4_lb4w.c` (the 64-bit LB₄ʳ of proof/k4-c4) with the original modes unchanged, plus `-N`. It
  runs LB₄ʳ's Phase 1 (index insertion), then each upgrade policy separately (u1 need-shrinking, u2 envy-free,
  u0 none), then repeats:
  - stop with success if some owner passes LB₄'s exact owner test (every non-frozen agent; the big-base agent alone
    if one base has ≥ 3 goods; no owner if ω ≤ 0);
  - otherwise apply a RotStep (frozen start, need chain, O; validity (V1), (V2), at most one base of ≥ 3 goods, as
    in `k4/lb4.md` §5) whose result raises the potential;
  - if none does, the state is a dead end.
- Potentials (`-P`):
  - P0: Φ = (z, Π v_i(B_i)), where z is the number of agents with a nonempty base, the product runs over those
    agents, and pairs are compared lexicographically; exact 128-bit integers;
  - P1: Π alone;
  - P2: Φ with the number of goods in bases as a tie-break;
  - P3: Φ with the leximin of the base values as a tie-break;
  - P4: Φ with the number of rotated agents as a tie-break.
- Rules (`-N`):
  - N1: steepest strict walk (largest potential);
  - N2: first strict walk (first improving RotStep found);
  - N5: strict search, over every path of strictly increasing moves (the *existence form*);
  - N3: weak search, over moves that do not lower the potential, visiting each state once;
  - N4: weak greedy walk.
- Values are the types' representatives (`check4.core_domains`: the smallest integer vector of each type in
  [1, 16]^d). Unlike EFX₀, NSW comparisons depend on the representative, so these results are for these values.
- Every success is re-checked against the raw EFX₀ definition and the D2 shape (0 raw failures in every log).
- `k4/nsw_run.py`: the driver, over certificates (exhaustive or sampled), H_t and the GM₄ instances.
- `k4/nsw_verify.py`: an independent check on `k4/c4_verify_H/lb4r.py`'s model. That model transcribes the Lean
  definition of LB₄ʳ (PR #35) and shares no code with lb4.c. For one profile and policy, the check explores every
  Φ-increasing path and reports the stuck states.

## 1. Results for NSW

| data | steepest walk N1 | first walk N2 | strict search N5 | weak search N3 |
|---|---|---|---|---|
| n = 2, every profile (189,216) | 0 | 0 | 0 | 0 |
| n = 3, every profile (299,837,376) | 478,880 | 30,726 | **0** | 0 |
| n = 4, 10,020,000 random profiles | 6,074 | 763 | **2** | 0 |
| H_1 … H_5 (`-w0`) | 0 | 0 | 0 | — |
| GM₄ instances A–H, P, Q, S | 0 | 0 | 0 | 0 |

The counts are profiles where all three upgrade policies fail. Logs: `results/k4_nsw_n23_N*.log`,
`results/k4_nsw_n4_N*.log`, `results/k4_nsw_H_gm4.log`.

- **Local form, refuted.** The local form says every stuck state reached by Φ-increasing moves has a Φ-increasing
  RotStep. It fails at n = 3, m = 5 (`attempts/k4-nsw-local.md`). The walks stop in such states: 33,480 of N1's and
  8,519 of N2's n = 3 failures, and many more under single policies. The other walk failures end where no valid
  rotation exists at all. So a proof cannot take *any* Φ-increasing rotation.
- **Strict existence form, refuted.** The strict existence form says some strictly Φ-increasing path reaches an
  output. It holds on every profile with n ≤ 3, but fails on 2 sampled n = 4 profiles (`attempts/k4-nsw-strict.md`).
  There, every RotStep from Phase 1 ties or lowers Φ. Both failures are confirmed on lb4r.py's model
  (`results/k4_nsw_strict_verify.log`).
- **Weak existence form, survives.** The weak form (non-decreasing moves, no state twice) never failed. A proof along
  these lines needs Φ plus a tie-break that strictly increases on the equal-Φ moves. P4 (rotated agents) solves both
  n = 4 failures; P2 and P3 solve only one.
- **H_t.** Every H_t (t ≤ 5) succeeds. The steepest walk uses ⌈2t/3⌉ rotations (1, 2, 2, 3, 4), the minimum by
  `k4/c4.md` §7. The first walk uses 3t for t ≥ 2 (2, 6, 9, 12, 15); the path found by the strict search has t.
  So NSW does guide unboundedly many rotations there.

## 2. Results for the (4, 3) class
(filled in below as runs finish)

## Reproduce
```
python3 k4/nsw_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz --exhaustive -N5 -P0 -i0 -w1 -c1
python3 k4/nsw_run.py results/k4_certs_4_*.json.gz --sample=10000 --seed=4 -N5 -P0 -i0 -w1 -c1   # n4_1..3, pure
python3 k4/nsw_run.py --h=1,2,3,4,5 -N1 -P0 -i0 -w0 -c1; python3 k4/nsw_run.py --gm4 -N5 -P0 -i0 -w1 -c1
python3 k4/nsw_verify.py '<profile JSON>' shrink        # independent check (attempts/k4-nsw-*.md)
python3 k4/p3_run.py filter results/k4_certs_5_n4_3.json.gz --out=DIR    # (4, 3) cores, then k4/lb4_run.py on them
python3 k4/p3_run.py random --n=6,7,8,9,10 --cores=200 --profiles=500 --seed=43
```
