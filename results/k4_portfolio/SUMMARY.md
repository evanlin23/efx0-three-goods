# The k = 4 deficit-descent portfolio: summary (compute/k4-portfolio)

EVIDENCE only: random samples, re-evaluated dumps and adversarial search. Nothing here is a proof. LEDGER.md is not
edited on this branch. Survival table: `TABLE.md`. The hunt: `HUNT.md`.

## Answer in brief

- **No non-control predicate of the lattice fails** on any state of the data. The data are 3,260,933 states with
  f ≥ 1 and def > 0 and 74,460 keys with def* > 0, in 172,493,761 profiles (summed over overlapping datasets). The two
  hunts found no failure either:
  - the annealing: 365 tasks, 20.8 million profiles generated, about 10 CPU hours;
  - the exhaustive two-type neighbourhoods of 14 hard profiles: 1,000,000 profiles, 550,648 states, 10,256 keys.

  Only the controls fail, where they must:
  - RT4 (DL_RT4) at the 67 known states and at 25 new ones, all re-derived by the reference implementation:
    - 17 in n5_purebt (seed 5): 10 on pure core 4170 (known) and 7 on pure core 4221 (m = 12), a core not known to
      fail before;
    - 2 on core 3200 of k4_certs_5_n4_4 (m = 9), also new;
    - 6 on core 4255 of k4_certs_5_n4_4 (m = 9), also new.

    The new profiles are `k4_certs_5_pure.json.gz#4170:20,0,18,10,37` and `#4221:16,2,10,9,45` (big-top domains),
    `k4_certs_5_n4_4.json.gz#3200:83,45,12,184,0` and `#4255:134,19,1,43,19` (domain indices of check4.core_domains).
    Their records are in `n5_purebt_fails.jsonl.gz`, `n5_4b_fails.jsonl.gz` and `n5_4c_fails.jsonl.gz`. The reference
    confirms them in `ref_hard.log`, `confirm_n5_4b_controls.log` and `confirm_n5_4c_controls.log`.
  - K1 (single T3/T4 key edges) at the 10 known keys and at 5 new ones.
  - D2 (DL₂) at 32,602 states (summed over overlapping datasets).
- **Strongest surviving single-step form: RC3_noT4** = T1 ∪ T2 ∪ T3⁺(|W| ≤ 1), with at most three agents changing.
  This is a finite catalogue of moves of at most three agents, all keeping NA:
  - a re-base;
  - a trade, or a rotation of three free agents;
  - a role swap x → z (z needs x's good), alone or with one helper that gives up a good;
  - a frozen chain x → w → z: x frees g, the frozen w moves from h to g, the free z takes h, which it needs.

  No T4 is needed. A frozen 2-swap is RC3's smallest repair at 11,303 states (summed over the datasets). At every one
  of them an RC3_noT4 move also lowers the deficit: a frozen chain at 11,107 and a role swap with a helper at 196.
- **Strongest surviving key-graph form: K3b_noT4.** Its edges are role swaps with at most one giving helper, and frozen
  chains (T3⁺ with |W| ≤ 1 and |ch| ≤ 3), with no T4 edges. DL_{RC3_noT4} implies it (below).
- RC3_noT4 and K3b_noT4 were added here as probes. The strongest forms on the coordinator's list are RC3 (RC_W1 with
  |ch| ≤ 3, added because no smallest repair changes more than three agents) and RC_W1 for single steps, and K3b and K3
  for the key graph. They all survive; RC3_noT4 ⊆ RC3 ⊆ RC_W1 ⊆ RC and K3b_noT4 ⊆ K3b ⊆ K3 ⊆ K2.

## The statements (k4/portfolio_preds.py)

For min-frozen P, Q:
- ch is the set of agents whose base differs.
- U are the agents frozen in P and free in Q; Z are the agents free in P and frozen in Q.
- W are the agents of ch frozen in both; Y are the agents of ch free in both.
- NA, NA′ are the needed sets.

Two facts are used throughout. `ProfData` asserts both on every profile evaluated: it checks that NA is the set of
frozen goods and that the class has a single frozen count.
- By (V1) and (V2), **NA is exactly the set of the frozen agents' goods**. So NA′ = NA iff the frozen goods are the
  same set.
- |U| = |Z| for every pair of min-frozen states, since both have exactly f frozen agents.

Consequences:
- **NAbal = NAall**: the clause |U| = |Z| adds nothing, and the two rows agree everywhere.
- "|U| ≤ 1, |Z| ≤ 1" is "|U| ≤ 1".
- **In T3⁺ the clause "the bases of W ∪ Z in Q are those of W ∪ U in P" follows from NA′ = NA**: both sides are NA
  minus the goods of the unchanged frozen agents.
- So T3⁺ = NA′ = NA, |U| = 1, |Y| ≤ 1 with a giving helper, and z needs its new good.
- With |W| = 1 and Y = ∅ the move is exactly the chain x → w → z above (w ∈ ch, so B′_w = B_x and B′_z = B_w).

Single-step forms DL_R, each requiring every state P to have a min-frozen Q with def(Q) < def(P) and R(P, Q), from the
strongest to the weakest:

| name | R | status on the data |
|---|---|---|
| RC3_noT4 | T1 ∪ T2 ∪ T3⁺(\|W\| ≤ 1), \|ch\| ≤ 3 (probe) | holds |
| RC3 | RC_W1 ∩ (\|ch\| ≤ 3) (added) | holds |
| RC_W1 | T1 ∪ T2 ∪ T3⁺(\|W\| ≤ 1) ∪ T4 | holds |
| RC | T1 ∪ T2 ∪ T3⁺ ∪ T4 (K4.DL2.RC) | holds |
| RC_noneed, RC_Yfree, RC_Yany | RC without "z needs"; with an unrestricted helper; with any number of giving helpers | hold |
| RC_U0 | (NA kept and U = ∅) ∪ T3⁺: T1, T2, T4 and their unions | holds |
| NA3 | NA kept, \|ch\| ≤ 3 (added) | holds |
| NA1 | NA kept, \|U\| ≤ 1 | holds |
| NAbal = NAall | NA kept | holds |
| U1Z1 | \|U\| ≤ 1, NA free | holds |
| D3, D4 | \|ch\| ≤ 3, ≤ 4 | hold |
| FR3 | \|U\| + \|Z\| + \|W\| ≤ 3 | holds |
| RT4 (control) | T1 ∪ T2 ∪ T3 ∪ T4 | fails: 92 states (25 new) |
| D2 (control) | \|ch\| ≤ 2 | fails (32,602 counted over the datasets) |

Key-graph forms (k4/dl13.md §2.3 Remark): every key κ with def*(κ) > 0 has a key κ′ with def*(κ′) < def*(κ) reached
by one E-move from some state of κ.

| name | E | status |
|---|---|---|
| K3b_noT4 | T3⁺(\|W\| ≤ 1), \|ch\| ≤ 3 (probe) | holds |
| K3b | (T3⁺(\|W\| ≤ 1) ∪ T4), \|ch\| ≤ 3 (added) | holds |
| K3 | T3⁺(\|W\| ≤ 1) ∪ T4 | holds |
| K2 | T3⁺ ∪ T4 (K4.DL2.RC key-graph form) | holds |
| K2_noneed, K2_Yany | without "z needs"; any number of giving helpers | hold |
| K4, K5, KU1 | NA kept and \|U\| ≤ 1; NA kept; \|U\| ≤ 1 | hold |
| K1 (control) | T3 ∪ T4 | fails: 15 keys (5 new) |

DL_{RC3_noT4} ⟹ the K3b_noT4 form. Take a state P with def(P) = def*(κ). T1 and T2 keep the key, so they cannot
lower def(P) below def*(κ). An RC3_noT4 repair of P is therefore a T3⁺ move, with |W| ≤ 1 and |ch| ≤ 3, to a key
κ′ ≠ κ with def*(κ′) ≤ def(Q) < def*(κ). The same argument gives RC3 ⟹ K3b, RC_W1 ⟹ K3, and RC ⟹ K2.

## Evidence

`TABLE.md` has the per-dataset counts for every predicate. The datasets:

| dataset | what | profiles | states (f ≥ 1, def > 0) | keys def* > 0 |
|---|---|---:|---:|---:|
| dumps | every distinct f ≥ 1 profile of the D records under results/k4_rt4, k4_dl13*, k4_dl2* (whole classes re-evaluated) | 168,799 (11 too large, skipped) | 700,635 | 70,749 |
| big | 6 of those 11 (H_2, n = 9, m = 23) | 6 | 1,701 | 0 |
| suite | k4/suite/instances | 154 | 215 | 37 |
| validate10 | the 10 DL_RT4-failing n = 5 profiles | 10 | 168 | 41 |
| n5_4 | n = 5, four 4-good agents, 4,000 per core, seed 3 | 39,384,000 | 280,604 | 476 |
| n5_4b, n5_4c | the same, 2,000 per core, seeds 7 and 11 | 39,384,000 | 278,641 | 460 |
| n5_purebt | pure n = 5, big-top, 5,000 per core, seed 5 | 23,370,000 | 1,855,551 | 1,872 |
| n5_3 | n = 5, three 4-good agents, 2,000 per core | 19,722,000 | 24,926 | 173 |
| n5_pure | pure n = 5 unrestricted, 600 per core | 2,804,400 | 87,855 | 47 |
| n5_12 | n = 5, one or two 4-good agents, 500 per core | 3,601,500 | 207 | 10 |
| x4_1 | n = 4, one 4-good agent, **every** strict profile | 7,247,232 | 286 | 286 |
| r3, r3b, r4, r4b | n = 3 (20 and 2,000 per core), n = 4 (20 and 1,000 per core, all four files) | 1,125,060 | 10,146 | 293 |
| n6_1 | n = 6, one 4-good agent, 100 per core | 2,686,600 | 0 | 0 |
| n6_ext, n6_ext2 | n = 6: random n = 5 cores (three or more 4-good agents) plus a sixth agent (k4/portfolio_ext6.py), 3,600 hypergraphs | 33,000,000 | 19,998 | 16 |

Hard states by (f, nearest distance k, the least |ch| of any better state):
- the dumps: 32,225 states with f = 1, k = 3, and 75 / 83 / 4 states with f = 2 / 3 / 4 at k = 3;
- n5_purebt: 102 states with f = 2 and 29 with f = 3 at k = 3;
- n5_4: 4 states with f = 4 at k = 3.

The exhaustive two-type neighbourhoods (k4/portfolio_nbhd.py) cover every profile within one or two type changes of a
seed, or a seeded random 150,000 or 40,000 of them:

| run | seeds | profiles | states | keys | non-control failures | least RC3_noT4 / K3b_noT4 margin |
|---|---|---:|---:|---:|---:|---|
| `nbhd_hard5_pairs.log` | the 4 hardest n = 5 profiles of the aggregates | 600,000 | 375,539 | 2,953 | 0 | 1 / 39 |
| `nbhd_fail10_pairs.log` | the 10 DL_RT4-failing profiles | 400,000 | 175,109 | 7,303 | 0 | 5 / 12 |

**Implied coverage.** Every single-step predicate except D2 contains R_13 = T1 ∪ T3, and every key-graph form has
the T3 edges. So these predicates can fail only at states where DL₁₃ fails. For the key forms, take a key-optimal
state: if DL₁₃ holds there, its T3 repair is an edge to a better key.

DL₁₃ holds at every f ≥ 1 state with n ≤ 3, exhaustively (K4.DL2.T13N). At n = 4 with one or two 4-good agents it
fails at exactly 20 and 3,040 states, exhaustively. Their 10 and 1,120 profiles are all in the dumps
(results/k4_dl13/dump_n4_1, dump_n4_2: every failure is dumped), and every predicate holds there.

So **every non-control predicate holds at every f ≥ 1 state of every strict profile with n ≤ 3, and of the n = 4
cores with one or two 4-good agents** (the x4_2 run was stopped for that reason).

**Smallest repairs.** Shapes are U|W|Z|Y, and the smallest repair of a state is the least by (|ch|, |U| + |W|, |Y|).

RC3_noT4, over all 3,260,933 states:

| shape | move | states |
|---|---|---:|
| 0\|0\|0\|1 | re-base T1 | 3,007,983 |
| 1\|0\|1\|0 | plain role swap T3 | 181,219 |
| 1\|0\|1\|1 | role swap + giving helper | 29,513 |
| 0\|0\|0\|2 | trade | 27,825 |
| 1\|1\|1\|0 | frozen chain | 11,277 |
| 0\|0\|0\|3 | 3-rotation of free agents | 3,116 |

RC3, the same states, with T4 allowed:
- 0|2|0|0, a frozen 2-swap, is the smallest repair at 11,303 states;
- 1|1|1|0, a chain, at only 170, almost all of them the RT4 failures (162 counted over the overlapping datasets).

So T4 and the frozen chain do the same job, and either is enough. All counts are summed over the datasets, and
validate10 and part of the suite repeat profiles of the dumps.

**By f** (the dumps again with `--byf`, 700,635 states and 70,749 keys; `TABLE.md`, last section):
- At f = 1 the work is done by re-bases, plain role swaps, role swaps with a helper (29,110), trades (15,597) and
  3-rotations (3,115). No T4 and no chain is ever the smallest repair.
- At f = 2 T4 is the smallest RC3 repair at 162 states, and a role swap with a helper replaces it in RC3_noT4. No chain
  is ever the smallest repair at f ≤ 2.
- At f = 3 and 4 the frozen 2-swap (11,010 states) is replaced by the frozen chain (11,061 chains in all).
- Key graph: plain role swaps, plus 13 with a helper, at f = 1, 2. Chains appear as the smallest edge only at f ≥ 3
  (7,846 keys), where T4 edges were smallest in K3b.

K3b_noT4, over 74,460 keys: 1|0|1|0 at 66,526, 1|1|1|0 at 7,915, 1|0|1|1 at 19. K3b: 1|0|1|0 at 66,526, 0|2|0|0
at 7,885, 1|1|1|0 at 35, 1|0|1|1 at 14.

**Margins.** The least number of repairs at a state is 1 for RC3, RC3_noT4, RC_W1, RC, NA3, D3 and 3 for NA1, NAall,
D4, FR3. The tight states are at f = 1:
- n = 4, near `dl13-n4m9-rot` (core 123 of k4_certs_4_pure, profile 7,196,11,3): the only RC3 repair is one T1
  re-base, and all other better states are role swaps with two helpers (4 agents);
- n = 5 (a hunt_n5 profile of results/k4_dl13): the only ≤ 3-agent repair is one plain role swap; the others are
  4-rotations of the four free agents and role swaps with 2-3 helpers.

These are where a bounded relation (RC3, NA3, D3) would break first. At n = 4 with f ≤ 3, every RT4 move changes at
most three agents, so RC3 ⊇ RT4 there. The tightness is an n ≥ 5, f = 1 phenomenon: four free agents, and rotations
of four (Theorem Z's moves at f = 0) appear as better states.

## Two implementations

- (a) The fast path: `k4/portfolio_dump.c` (dlrt4.c's code, verbatim) + `k4/portfolio_preds.py`. Its deficits equal
  dlrt4.c's `-s` lines on 1,954 states (`python3 k4/portfolio.py selftest`).
- (b) `k4/portfolio_ref.py`: main's `k4/c4x_check.py` enumeration and `rodef`, through `k4/dl134_xcheck.py`'s `Prof`,
  with every predicate written again from its definition. It shares no code with (a) and does not load model.py
  (asserted).

`compare` checks the class, the deficits, and **the number of repairs** of every predicate at every state and key, not
just the verdicts:

| subsample | profiles | states | keys | mismatches | log |
|---|---:|---:|---:|---:|---|
| the 10 failing profiles + `ref_subsample.json` (n ≤ 5, m ≤ 11: dumps strata and the suite) | 362 | 1,569 | 512 | 0 | ref_subsample.log |
| `ref_subsample_n5.json` (n = 5, m = 9, 10, dumps) | 80 | 146 | 10 | 0 | ref_subsample_n5.log |
| `ref_hard.json` (the hardest n = 5 profiles of the aggregates, m ≤ 11, and the 2 profiles of the 17 new RT4 failures of n5_purebt) | 104 | 402 | 97 | 0 | ref_hard.log |

The controls behave as required on the 10 failing profiles: RT4 fails at 67 states, K1 at 10 of 41 keys, and RC, K2
hold (`validate10.log`, `ref_validate10.log`).

## The hunt (Phase 3)

`HUNT.md` has every predicate and objective. In outline:
- **The round-robin hunt** (`hunt_main`, `k4/portfolio_hunt.py`) went strongest first, over rounds 0-7 (the last cut short at the
  time limit), over 24 non-control predicates: all of them except NAbal, which equals NAall. Each predicate had two objectives:
  - "count": the number of repairs at the worst state;
  - "edge": first the number of repairs by the next stronger predicate, then by the predicate.

  Tasks ran 60-90 s each, on seeds of four kinds:
  - fail10: the 10 DL_RT4-failing profiles;
  - hard: the 12 hardest profiles of the Phase 2 aggregates, one per core;
  - rcores: 12 random n = 5 cores with three or more 4-good agents, at their hardest of 2,000 random profiles;
  - ext: 8 n = 6 extensions of the failing cores.
- **Two focused hunts**, with 240-300 s tasks:
  - `f1focus` (and `f1focus_n4`): RC3, NA3, D3 on the hard f = 1 profiles, where those relations are tight;
  - `not4focus`: RC3_noT4 and K3b_noT4.
- Totals: 459 tasks, 25,766,088 profiles generated (each with an f ≥ 1 state is evaluated for every alive
  predicate), 46,351 CPU s (12.9 CPU hours). Stopped at 04:40 UTC for the time budget.
- **No predicate died.** There is no `FAILURES_<pred>.md`.
- The least "count" objectives reached (repairs at the worst state):
  - single-step: RC3 1, NA3 1, RC3_noT4 2, RC_noneed 2, D3 3, RC_W1 3, RC 5, NAall 5;
  - key-graph: K3b 7, K4 7, KU1 7, K3b_noT4 12, K3 12, K5 14, K2 36.
- The "edge" objectives reached 0 for the inner predicates RT4, K1 and D2. So the hunt finds new DL_RT4 failures
  easily; they are not recorded, since RT4 is a control. No inner predicate of the lattice reached 0.
- Edge objectives [1, 1] (RC_Yfree, inner RC) and [2, 2] (RC_Yany) show states whose only RC repairs are one or two
  moves, all inside RC's own edge.

The **exhaustive two-type neighbourhoods** (Evidence, above) are the systematic counterpart: 1,000,000 profiles around
the 14 hardest and failing profiles, with no non-control failure.

## Reduced coverage, said plainly

- Random samples, not exhaustive, at n ≥ 5 and for n = 4 with three or four 4-good agents (r4b: 1,000 per core).
  DL_RT4's own failures show up in about one profile per 3 to 80 million sampled (n5b_4, n5c_purebt and the runs
  here).
- n = 6 is thin: the certificate file has only cores with one 4-good agent, and none of their profiles has an f ≥ 1
  state. The extensions in k4/portfolio_ext6.py are not reduced up to isomorphism.
- Not run:
  - gluings of two failing instances (n = 10, classes of thousands, too slow per annealing step);
  - 5 of the 11 large H_2 profiles of the dumps (30M-82M state × class pairs each);
  - the exhaustive n = 4 run with two 4-good agents (implied, above).
- The hunt anneals profiles of fixed cores; it never changes the hypergraph.
- The checkpoint files (container-only resume state) were committed in early commits, before they were untracked. They
  stay in this branch's history (76 MB at most each, under GitHub's limit). Rewriting the history to drop them was not
  done.

## Reproduce

```
python3 k4/portfolio.py selftest                      # portfolio_dump.c = dlrt4.c on 1,954 states
python3 k4/portfolio.py inst results/k4_rt4/n5b_failures_inst.json results/k4_rt4/n5c_fail_inst.json --name=validate10 --chunk=1
python3 k4/portfolio_ref.py compare results/k4_portfolio/ref_hard.json    # ~5 min, one process
sh k4/portfolio_runs.sh <dumps|dumps_byf|suite|r3|r4|r3b|r4b|n5_4|n5_4b|n5_4c|n5_purebt|n5_3|n5_12|n5_pure|n6_1|n6_ext|n6_ext2|x4_1|big>
python3 k4/portfolio_ext6.py results/k4_portfolio/cores_6_ext2.json.gz 3000 2   # the n = 6 hypergraphs (cores_6_ext: 600 1)
python3 k4/portfolio.py table                         # TABLE.md
python3 k4/portfolio_hunt.py --rounds=12 --slot=90 --jobs=3 --name=main [--push]
python3 k4/portfolio_hunt.py --preds=RC3,NA3,D3 --seeds=hard5 --slot=300 --jobs=1 --rounds=4 --name=f1focus
python3 k4/portfolio_hunt.py --preds=RC3_noT4,K3b_noT4 --seeds=fail10,hard,rcores --slot=240 --jobs=1 --rounds=6 --name=not4focus
python3 k4/portfolio_hunt.py report                   # HUNT.md
python3 k4/portfolio_nbhd.py --seeds=hard5 --k=4 --pairs --max=150000 --jobs=1 --name=hard5_pairs
python3 k4/portfolio_nbhd.py --seeds=fail10 --k=10 --pairs --max=40000 --jobs=1 --name=fail10_pairs
python3 k4/portfolio_ref.py confirm results/k4_portfolio/n5_4c_fails.jsonl.gz --pred=RT4   # the new RT4 failures
```

## For the provers

The data point to a finite move catalogue of at most three agents, with NA kept: re-base, trade, 3-rotation, role
swap, role swap with one giving helper, frozen chain. On all data, every def > 0 state at f ≥ 1 has a repair in this
catalogue (RC3_noT4).

Next to it, T4 is never needed. The frozen chain replaces the frozen 2-swap everywhere, including the 3,060 DL₁₃
failures at n = 4.

Its weakest points are the f = 1, n ≥ 5 states. There, four free agents make 4-rotations available, and on the
tightest states the catalogue's only repair is a single re-base or a single role swap. A counterexample to RC3_noT4,
if one exists, is most likely an n ≥ 5, f = 1 state whose only improvements are 4-rotations of free agents or role
swaps with two helpers. In that case the next candidate is RC_W1 restricted to free rotations of any size (RC3_noT4
with T2 unbounded), which is still T4-free.
