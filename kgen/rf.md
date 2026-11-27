# Conjecture RF at k = 5, 6, n ≤ 4, and the rank-maximal variant (workstream `proof/kgen-n3`)

Coordinator's request, 2026-11-27. The statements are from `k4/sdc.md` §31 (end) on main @ 898d80b0, read in full.
Code: `kgen/rf/`. Logs: `results/kgen_rf/`. Everything here is evidence only (PROMPT.md §5 rule 3).

**Definitions, as implemented** (`kgen/rf/rf_lib.py`, written from §29 and §31):
- SD picks; ν, the maximum-matching size of the agent / relevant-good graph.
- The official moves: additions, chains and rings, with no empty hand-on, and every receiver strictly gaining.
- A one-absorber completion, and raw EFX₀.
- A receiver of a start Y is an agent u with a pick that no other agent values above its own pick.
- **RF** (amended form): at a maximum-matching start where OC₁ fails, for every receiver u, every u-first order whose
  picks form a maximum matching satisfies OC₁. **False at k = 5, n = 4 (§0).** RF∃: some receiver-first
  maximum-matching order satisfies OC₁.

The second checker is k4/sdc's `oc1_mc2_rand.Inst.check` on main, imported read-only.

**Split with ksens** (agreed 2026-11-27). ksens runs the exhaustive n = 3, k = 5 RF test, by extending kcegar over
every strict profile of the 617 hypergraphs. This workstream takes n = 4 at k ≥ 5, and random and adversarial cores
at n = 3, 4 and k = 5, 6. ksens's own replay on 15 failing starts (`k4/ksens/rf_replay.py`, PR #98) agrees with the
results below.

## 0. RF in its every form is false at k = 5, n = 4; RF∃ survives (2026-11-27, after PR #97)

- **RF5** (ksens, `k4/ksens/refute_rf_k5.py` on `claude/k4-ksens` @ 0db58f4b; found by their exhaustive n = 4, k = 5
  sweep).
  - sets [[0,1,2,5,6],[1,2,4,5,6],[3,4,5,6],[3,4,5,6]], vals [[3,35,33,43,39],[20,26,16,43,32],[8,2,7,4],[8,2,7,4]].
  - Strict and balanced. Agents 2 and 3 are twins (same goods, same values).
- **Replayed here independently** (`kgen/rf/rf5_replay.py`, `results/kgen_rf/rf5_replay.log`). Both checkers agree.
  - OC₁ fails at two twin-swapped starts: (6,5,4,3), whose only receiver is agent 2, and (6,5,3,4), whose only
    receiver is agent 3.
  - Each start is the other's receiver-first image: the order (2,1,0,3) maps (6,5,4,3) to (6,5,3,4), and
    (3,1,0,2) maps back. So the every form fails at both.
  - The other 5 receiver-first maximum-matching vectors of each start satisfy OC₁. So **RF∃** holds: some
    receiver-first maximum-matching order satisfies OC₁, which still gives OC₁^∃max.
- **The candidate is now RF∃.** `kgen/rf/rf_climb2.py` climbs against it, seeded at the known failures and at random
  cores with one pair of twins (the RF5 mechanism). Runs: `results/kgen_rf/rf_exists_climb_*.log`.
- The earlier every-form climb (`rf_climb.py known`; 120 climbs × 1,500 steps from the 29 known failures,
  `results/kgen_rf/rf_climb_targeted_known.log`) found no violation. Its best case kept 6 completable states at
  every receiver-first vector. Climbs are therefore weaker than ksens's exhaustive sweep.

## 1. RF: no violation found by this workstream's data

| data | failing max starts | RF holds | notes |
|---|---|---|---|
| ksens's 13 n = 3, k = 5 one-chain witnesses (`kcegar_k5_n3_D1.log`), RD5, the kgen n = 4, k = 5 instance | 15 | 15 | `rf_known.log`. The two checkers agree on all 92 max starts. Each n = 3 witness has one receiver; the kgen instance has two, and all 12 receiver-first orders work |
| random strict cores, k = 5, 6, n = 3, 4 (20,000 each; `rf_run.py rand`) | 0 | n/a | `rf_rand_*.log`: no OC₁^max failure at all |
| hill climbs (400 × 1,500 steps each; `rf_run.py climb`) | k = 5, n = 3: 0; k = 5, n = 4: 3; k = 6, n = 3: 1; k = 6, n = 4: 9 | all 13 | `rf_climb_*.log`. Every failing start has exactly one receiver |

- Instances follow the k = 4 MC2-class rules of `k4/sdc/oc1_mc2_rand.gen`, with up to k goods per agent: at most one
  private good each, every shared good valued by ≥ 2 agents, connected, strict, and balanced (2·max < sum).
- Receiver-first orders are robust: on the known failures they complete at the picks or after one move with 6–13
  completable states (`rf_climb.py known`, smoke run). A longer targeted climb toward RF violations is next.

## 2. The rank-maximal variant: the every-form is false, the some-form survives

- rank_i(Y) = 1 + the number of i's relevant goods valued above Y_i.
- RM-optimal: among the maximum-matching SD vectors, lexicographically maximal (#rank 1, #rank 2, …).
- **"OC₁ at every RM-optimal vector" fails** (`attempts/kgen-rf-rm-every.md`):
  - at k = 5, n = 3, on ksens's witnesses, e.g. n3_m6_93, which is strict and balanced. At n = 3 every
    maximum-matching vector has signature (1, 1, 1), so RM selects nothing.
  - at k = 6, n = 4, on a strict balanced core found by climbing. Its failing start has the maximal signature
    (2, 1, 0, 1, 0, 0).
  - No failing RM-optimal vector at n = 4, k = 5 so far.
- **"OC₁ at some RM-optimal vector"** holds on all 28 instances with a failing max start (`rf_rm_known.log`,
  `rf_rm_xcheck.log`, two codes).
