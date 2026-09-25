# Nash social welfare as a potential for LB₄ʳ's rotations, and bounded LB₄ʳ on the (4, 3) class (compute/k4-nsw)

EVIDENCE only (PROMPT.md §5 rule 3). Two leads for the open step of the k = 4 proof:

1. **NSW-guided unbounded rotations.** Proposition H (`k4/c4.md` §7, on main since #33; ledger K4.C4.R, PROVED) shows
   that LB₄ʳ with a fixed insertion order needs unboundedly many rotations: ⌈2t/3⌉ on the cores H_t. A proof then needs
   a potential that makes unbounded rotation terminate with an output. `proofs/pq_bounded.md` §2–3 points to Nash social
   welfare (Kaviani et al., rankpath shifts; per `proofs/pq_bounded.md`, [unverified] here).
2. **The (k, p) = (4, 3) class.** In these cores every good is valued by at most 3 agents, which excludes every H_t.
   The question is whether bounded LB₄ʳ ever fails there.

## Tools
- `k4/lb4_nsw.c`: `k4/c4_lb4w.c` (the 64-bit LB₄ʳ of #33, on main) with the original modes unchanged, plus `-N`. It
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
  - N4: weak greedy walk;
  - N6: the local-form census (the #40 reviewer's mode): every state reachable by strictly increasing moves through
    states without an output is visited, and the profile is flagged if one of them has no output, has a RotStep, and
    has none that raises the potential.

  The searches (N3–N6) keep a visited set of 64-bit state hashes. A collision can only hide a state (a false dead
  end or a missed flag), never fake a success.
- Values are the types' representatives (`check4.core_domains`: the smallest integer vector of each type in
  [1, 16]^d). Unlike EFX₀, NSW comparisons depend on the representative, so these results are for these values.
- Every success is re-checked against the raw EFX₀ definition and the D2 shape (0 raw failures in every log).
- `k4/nsw_run.py`: the driver, over certificates (exhaustive or sampled), H_t and the GM₄ instances.
- `k4/nsw_verify.py`: an independent check on `k4/c4_verify_H/lb4r.py`'s model (on main since #33; loaded from the
  tree, and checked at load against the git blob 6726d25 that the committed logs used). That model transcribes the Lean
  definition of LB₄ʳ (PR #35) and shares no code with lb4.c. For one profile and policy, the check explores every
  Φ-increasing path and reports the stuck states.

## 1. Results for NSW

| data | steepest walk N1 | first walk N2 | strict search N5 | weak search N3 |
|---|---|---|---|---|
| n = 2, every profile (189,216) | 0 | 0 | 0 | 0 |
| n = 3, every profile (299,837,376) | 478,880 | 30,726 | **0** | 0 |
| n = 4, 10,020,000 random draws (with replacement) | 6,074 | 763 | **2** | 0 |
| n = 5, 9,475,200 random draws | — | — | 0 | 0 |
| H_1 … H_5 (owner's needs from its base, `-w0`) | 0 | 0 | 0 | — |
| H_1 … H_3 (`-w1`) | 0 | — | 0 (with Φ⁺) | — |
| GM₄ instances A–H, P, Q, S | 0 | 0 | 0 | 0 |

The counts are profiles where all three upgrade policies fail. Logs: `results/k4_nsw_n23_N*.log`,
`results/k4_nsw_n4_N*.log`, `results/k4_nsw_H_gm4.log`, `results/k4_nsw_H_w1.log`, and for the census
`results/k4_nsw_census_n23.log`.

- **Local form, refuted.** The local form says every stuck state reached by Φ-increasing moves has a Φ-increasing
  RotStep. It fails at n = 3, m = 5 (`attempts/k4-nsw-local.md`). The walks stop in such states: 33,480 of N1's and
  8,519 of N2's n = 3 failures, and many more under single policies. The other walk failures end where no valid
  rotation exists at all. So a proof cannot take *any* Φ-increasing rotation. The census `-N6`
  (`results/k4_nsw_census_n23.log`) visits every state reachable by strictly Φ-increasing moves through states without
  an output. Its counts:
  - n = 2: no profile has such a stuck state (189,216 profiles);
  - n = 3, m = 4: none (24,406,272 profiles);
  - n = 3, m = 5: 46,992 of 49,813,056 profiles, under each policy.

  So n = 3, m = 5 is the smallest size at which the local form fails.
- **Strict existence form, refuted.** The strict existence form says some strictly Φ-increasing path reaches an
  output. It holds on every profile with n ≤ 3, but fails on 2 sampled n = 4 profiles (`attempts/k4-nsw-strict.md`).
  There, every RotStep from Phase 1 ties or lowers Φ. Both failures are confirmed on lb4r.py's model
  (`results/k4_nsw_strict_verify.log`).
- **Weak existence form, survives.** The weak form (non-decreasing moves, no state twice) never failed. A proof along
  these lines needs Φ plus a tie-break that strictly increases on the equal-Φ moves. P4 (rotated agents) solves both
  n = 4 failures; P2 and P3 solve only one. With P4, the strict search never fails:
  - on every profile with n ≤ 3 (`results/k4_nsw_n23_N5P4.log`);
  - on the 10,020,000 sampled n = 4 profiles (`results/k4_nsw_n4_N5P4.log`);
  - on the 9,475,200 sampled n = 5 profiles, 300 per certified core, every class (`results/k4_nsw_n5_N5P4.log`).

  So the surviving candidate is **Φ⁺ = (z, Π v_i(B_i), number of rotated agents)** in the existence form: some path
  of RotSteps, each strictly raising Φ⁺, reaches an output. A rotated agent is one holding a rotation base O (marked,
  no pick). Φ⁺ is a candidate, not a local rule: it still has to choose among the rotations.

  H_t and GM₄ were run with Φ (`-P0`), and H_t with the owner's needs from its base (`-w0`). Φ⁺ still holds on them:
  - every strictly Φ-increasing move strictly raises Φ⁺, which extends Φ lexicographically, so the successes of the
    `-P0` searches are successes of `-P4`;
  - a `-w0` completion is a `-w1` completion (`k4/c4.md` §7).

  Directly with `-w1` (`results/k4_nsw_H_w1.log`), on H_1–H_3 the Φ⁺ search `-N5 -P4` succeeds with 1, 2 and 2
  rotations, and the steepest walk `-N1 -P0` uses 1, 2 and 2. H_4 with `-w1` did not finish in 5 minutes (the #40
  reviewer).
- **H_t.** Every H_t (t ≤ 5) succeeds. The steepest walk uses ⌈2t/3⌉ rotations (1, 2, 2, 3, 4), the minimum by
  Proposition H. So NSW guides as many rotations as Proposition H requires, for t ≤ 5.
  - These are `-w0` numbers, so they are upper bounds for `-w1`.
  - The first walk uses 3t for t ≥ 2 (2, 6, 9, 12, 15).
  - The path found by the strict search has t rotations.
  - With `-w1`, H_1–H_3 need 1, 2 and 2 (above).

## 2. Results for the (4, 3) class
Bounded LB₄ʳ (`k4/lb4.c -i0 -u3 -r3 -w1 -c1`; for random cores the same options in `k4/lb4_nsw.c`) on k = 4 cores in
which every good is valued by at most 3 agents:

| cores | profiles | LB₄ʳ fails | least rotation depth that works (0 / 1 / 2 / 3), index order |
|---|---|---|---|
| n ≤ 3 (all 56 cores are (4, 3) cores) | every profile | 0 (`results/k4_lb4_variants.log`) | n = 2: 185,856 / 3,360 / 0 / 0; n = 3: 289,807,786 / 10,017,550 / 12,040 / 0 (main's `results/k4_lb4r_hist.log`, `-d2`) |
| n = 4, one, two, three 4-good agents (95, 219, 240 (4, 3) cores) | every profile | 0 | 5,023,990 / 77,066 / 0 / 0; 498,793,142 / 8,823,858 / 280 / 0; 23,761,119,376 / 443,237,808 / 29,120 / 0 (`results/k4_p3_lb4r_4_hist.log`) |
| pure n = 4 (142 of 219 cores) | every profile | 0 (`results/k4_lb4_nested_pure4.log`) | no histogram for the (4, 3) subset; on all 219 pure cores none needs 3 (`results/k4_lb4r_hist.log`) |
| n = 5, one or two 4-good agents (3,438 of 7,203) | every profile | 0 (`results/k4_lb4_nested_n5.log`) | no histogram for the (4, 3) subset; on all 7,203 cores none needs 3 (`results/k4_lb4r_hist.log`) |
| n = 5, three 4-good agents (4,622 of 9,861) | every profile | 0 (the index-order run on all 9,861 cores, `results/k4_lb4r_ex_5_n4_3.log`) | no histogram |
| n = 6, one 4-good agent (7,817 of 26,866) | every profile (1.58·10¹⁰) | 0 (`results/k4_p3_lb4r_6_n4_1.log`, 22 min on 2 CPUs) | no histogram |
| n = 5, four 4-good agents (4,380 of 9,846) | 4,380,000 random draws | 0 | 4,337,772 / 42,227 / 1 / 0 |
| pure n = 5 (1,962 of 4,674) | 1,962,000 random draws | 0 | 1,939,368 / 22,632 / 0 / 0 |
| random, n = 6–10, 200 cores each | 500,000 random | 0 | at most 1 rotation |
| random dense (90% 4-good agents, ≤ 0 or ≤ 1 private goods per agent), n = 6–10, 200 cores each | 1,000,000 random | 0 | at most 1 rotation (`results/k4_p3_random_dense.log`) |

Logs: `results/k4_p3_sample_5.log`, `results/k4_p3_random.log`, and for n = 4 with one to three 4-good agents also
`results/k4_lb4_nested_n4.log` (every core). The filtered core lists and the filter log are in `results/k4_p3/`.

The earlier exhaustive runs cover every core of their classes with index insertion (`k4/lb4.md` §5), so they cover the
(4, 3) cores among them. On the data, LB₄ʳ never fails in the (4, 3) class.

Rotation depth:
- **Histograms (index order, `-d2`).** No profile needs three rotations. Two are needed by 12,040 profiles at n = 3 and
  by 29,400 on the (4, 3) cores with n = 4 (280 with two 4-good agents, 29,120 with three). The histograms cover
  n ≤ 3 and those n = 4 classes on their (4, 3) cores, and every core of pure n = 4 and of n = 5 with at most two
  4-good agents.
- **Sampled runs.** One profile needs two rotations (n = 5, four 4-good agents); every other profile needs at most one.
- **No histogram** exists for n = 5 with three 4-good agents or for n = 6.

The random cores are mostly easy: nearly all profiles need no rotation.

## Reproduce
```
python3 k4/nsw_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz --exhaustive -N5 -P0 -i0 -w1 -c1
python3 k4/nsw_run.py results/k4_certs_4_*.json.gz --sample=10000 --seed=4 -N5 -P0 -i0 -w1 -c1   # n4_1..3, pure
python3 k4/nsw_run.py --h=1,2,3,4,5 -N1 -P0 -i0 -w0 -c1; python3 k4/nsw_run.py --gm4 -N5 -P0 -i0 -w1 -c1
python3 k4/nsw_verify.py '<profile JSON>' shrink        # independent check (attempts/k4-nsw-*.md)
python3 k4/nsw_run.py results/k4_certs_3.json.gz --exhaustive --m=5 -N6 -P0 -i0 -w1 -c1   # local-form census
python3 k4/nsw_run.py --h=1,2,3 -N5 -P4 -i0 -w1 -c1                                      # H_t with -w1
python3 k4/p3_run.py filter results/k4_certs_4_n4_{1,2,3}.json.gz --out=results/k4_p3    # (4, 3) cores
python3 k4/lb4_run.py results/k4_p3/k4_certs_4_n4_{1,2,3}_p3.json.gz -i0 -u3 -r3 -w1 -c1 -d2   # depth histogram
python3 k4/p3_run.py random --n=6,7,8,9,10 --cores=200 --profiles=500 --seed=43
```
