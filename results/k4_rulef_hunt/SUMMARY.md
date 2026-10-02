# Hunt for a counterexample to Lemma M (`k4/rulef.md` §4, ledger row K4.RF.M)

Workstream `compute/k4-lemmam-hunt`, branched from `proof/k4-rulef` (PR #72) at b0f4ee5. `k4/rulef.c` unchanged,
sha256 `5721abf3bc9e25b101412aeb6b602db24d80e1991beee9a367a01cf9ccfc424e` (printed at the top of every log). No existing
file was modified. EVIDENCE only (PROMPT.md §5 rule 3): adversarial local search, not an exhaustive check.

## Result

- **No counterexample.** No profile was found on which no first agent is in K0 ∪ K1 (so no `FAILURES.md`). Every
  profile found with at most one working first agent was re-checked by the second implementation
  (`k4/rulef_hunt_check.py` on `k4/rulef_model.py` / PR #33's model): 8,501 distinct profiles, the classes of every first
  agent agree, every completion built from a certificate is an `Output` of `lean/EFX/LB4R.lean` and EFX₀ by the raw
  definition (`check.log`: 8,501 agree, 0 disagree, 0 witness failures, 0 profiles without a working first agent).
- **Best objective value reached: nwork = 1** (exactly one first agent in K0 ∪ K1), on **13 pure n = 5 cores** (five
  4-good agents, m = 9 and 10; table below), 8,501 distinct profiles in `tight.jsonl.gz`. Everywhere else the least
  value reached is at least 2: n = 4 pure 2 (71 of 219 cores); n = 5 with four 4-good agents 2, three 2, one or two 3;
  n = 6 (one 4-good agent, the only n = 6 certificate file) 6 on all 26,866 cores, i.e. every first agent works on every
  best profile found.
- **The tight profiles all have one shape.** The one working first agent is in K0 (LB₄ʳ needs no rotation with it), it
  is big-top (four goods, top worth more than the next two together), and it is the **first big-top agent in index
  order** — also when two or three agents are big-top (2,641 of the profiles). Every other first agent (34,004 runs) has
  the same three frozen agents under all three policies (need-shrinking, envy-free, none: no upgrade changes them),
  ω = 2 (m = 9) or 3 (m = 10), Lemma K deficit exactly 1 under every policy, no single rotation that Lemma K certifies,
  and LB₄ʳ (rulef.c) needs exactly two rotations with it first. So the profiles are tight for rule F itself: in Lean's
  exact sense too (`SucceedsR 1`: some policy, at most one `RotStep`, then an `Output` for some owner or none, decided
  by SAT on PR #33's model, `k4/rulef_hunt_rulef1.py`, `rulef1_lean.log`) exactly one first agent succeeds with at most
  one rotation on all 8,501 profiles, and the per-agent counts equal rulef.c's. The no-upgrade policy (RK₃, `-N1`) and
  Remark 4's kept-out sets (`-Y1`, on throughout) do not add a working agent. "The big-top agent with the fewest
  private goods (ties by index)" picks a failing agent on 1,685 of them (that rule was already refuted,
  `attempts/k4-rulef-bigtop-first.md`); "the first big-top agent" never does.
- **Around each tight profile** the exhaustive two-change neighbourhood (every profile that differs in the types of one
  or two agents, about 825,000 for n = 5 pure) holds no profile with nwork 0, for the best tight profile of each of the
  13 cores (`deep5t`, `deep5t2`) and for 132 further profiles with nwork 2 (`deep5x`), and neither do the 120 agent
  orders of the end points.

## A finding about rulef.c's class K1 (affects how C-only failures must be read)

`k4/rulef.c`'s K1 test (`k1_run`, apply_chain with KMODE) gives every rotated (marked) agent **no slot place**, also
when its new base O is a single good. Lemma K's text counts κ^K = Σ (2 − |B_x|) over the agents outside F^K
(`k4/rulef.md` §2), and Lean's `Completion.free` (`lean/EFX/PreAllocK.lean`) lets every non-frozen non-owner agent take
2 − |B_j| junk goods, marked or not. So rulef.c's K1 is a sound **restriction** of K1 (its K0 is not affected: upgraded
bases have two goods), and a profile where every first agent fails rulef.c's K1 need not refute Lemma M. Example
(`xcheck/k1_slot_example.*`): `k4_certs_5_n4_4` core 7942, sets [[0,2,4,6],[1,3,5,9],[2,4,5,9],[3,7,8,9],[6,7,8]],
vals [[2,4,3,8],[4,2,10,7],[4,5,8,6],[3,2,4,8],[4,2,3]]: first agents 1, 2, 4 fail rulef.c's K1, but for first agent 1
the RotStep along the chain 2 → 3 with O = {4} reaches a state with deficit 0 for owner 0, whose completion gives the
rotated agent 2 the junk good 7 in its slot; it passes `lb4r.output_check` (Output, owner's needs from the bundle) and
the raw EFX₀ test. The same rule (cap 0 for marked agents) is in rulef.c's LB₄ʳ owner search after rotations, so
rulef.c's rotation counts are upper bounds for Lean's `SucceedsR` (on the tight profiles they coincide, see above).

The hunt therefore evaluates K1 as Lemma K's text has it (`k4/rulef_hunt_eval.c -T1`, the default: after the validity
checks a rotated agent with a one-good base is entered as an unmarked agent with that good as its pick; otherwise
rulef.c's apply_chain unchanged). On 597 profiles with a non-K0 first agent its classes agree with the second
implementation everywhere, every certificate's completion (rotated states included) checked
(`xcheck/k1_text_597.log`). The partial first broad pass made with rulef.c's K1 (`n5hi_cK1`, 1,281 cores) and the pilots
(`ck/pilot*`) used `-T0` semantics; their low nwork values are partly this restriction (e.g. the three nwork-3 profiles
of the regression set all become 5 with `-T1`).

## What was searched

Classes as rule RK (`k4/rulef.md` §4, `rulef.c -A41 -E1`): K0 = Lemma K deficit ≤ 0 (or ω ≤ 0) after Phase 1(τ_a) and
need-shrinking or envy-free upgrades; K1 = some single rotation (rulef.c's chains and bases O) reaches a state with
Lemma K deficit ≤ 0; Lemma K with Remark 4's kept-out sets (`-Y1`) and the text's slot count (`-T1`). C40 is not
evaluated (C40 ⊆ K0 ∪ K1). The evaluator `k4/rulef_hunt_eval.c` `#include`s rulef.c unchanged and calls its functions
(`deficits`, `apply_chain`/`hdefK_owner`, `c40_run`, `lb4r`); it agrees with `rulef_run.py -A41 -E1 -Y1` on all 261
comparable profiles of a test set, and with `-T0` its rotation count is positive exactly when `k1_run` succeeds
(6,060 profiles).

Profiles: the strict types of `k4/check4.py` `core_domains` (288 per 4-good agent, 6 per 3-good agent, fewer with
private goods). Objective (`--key=M`, as asked): minimize nwork = |K0 ∪ K1| over the n first agents, ties by the least
Lemma K deficit over all first agents and policies (larger is closer to failure), then |K0| and the sum of the
deficits. Search (`k4/rulef_hunt.py`): per core, restarts from the best of 96 random profiles (or a seed, or a kick of
the best so far), then batches of 48 neighbours (one agent's type redrawn, sometimes two or three), moving to the best
neighbour unless it is worse, until 25 batches bring no strict improvement. `--key=R` (deep5r) replaces the deficit
tie-break by the number of certifying rotations of each K1 agent; `--exhaust` evaluates the whole two-change
neighbourhood and descends; `--relabel` evaluates all n! agent orders of each restart's best profile (rule RK depends
on the index order, and the certificates list one labeling per core). Every profile with nwork ≤ 1 was re-evaluated in
detail (every policy, frozen agents, C₄⁰, LB₄ʳ's fewest rotations) and dumped.

| run | what | units | profiles | least nwork reached per unit |
|---|---|---|---|---|
| n5hi | n = 5, three to five 4-good agents, m ≥ 9, 20,000 each | 16,374 | 327,755,136 | 1: 4, 2: 49, 3: 213, 4: 448, 5: 15,660 |
| n5lo | the same classes, m ≤ 8, 4,000 each | 8,007 | 32,292,288 | 2: 4, 3: 6, 4: 6, 5: 7,991 |
| n5n12 | n = 5, one or two 4-good agents, 6,000 each | 7,203 | 43,226,352 | 3: 5, 4: 5, 5: 7,193 |
| pure2 | n = 5 pure, 9 ≤ m ≤ 11, second seed, 60,000 each, agent orders scanned | 3,218 | 193,489,680 | 1: 8, 2: 71, 3: 193, 4: 376, 5: 2,570 |
| n44r | n = 5, four 4-good agents, m ≥ 9, second seed, 20,000 each, agent orders scanned | 7,004 | 141,075,216 | 2: 20, 3: 81, 4: 76, 5: 6,827 |
| n4pure | n = 4 pure (only sampled before), 500,000 each | 219 | 109,503,648 | 2: 71, 3: 28, 4: 120 |
| seedsH | H₁ under all 120 agent orders, H₂ (n = 9) and 8 relabelings, from H_t's profile, 60,000 each | 129 | 7,740,273 | 5: 129 |
| suite | the suite's strict k = 4 core instances, 4 ≤ n ≤ 9, from the instance, 60,000 each | 77 | 4,620,125 | 2: 8, 3: 5, 4: 48, 5: 14, 6: 2 |
| deep5t, deep5t2 | two-change neighbourhood of the best tight profile of every tight core, then its agent orders | 4 + 16 (+ 4 partial) | 19,805,904 | 1: 24 |
| deep5x | two-change descent from every best profile with nwork ≤ 2 (n = 5 runs, suite, n4pure) | 136 | 75,645,422 | 1: 4, 2: 132 |
| deep5r | key R climbs from every best profile with nwork ≤ 3, 200,000 each, agent orders scanned | 294 | 58,837,302 | 1: 5, 2: 79, 3: 210 |
| n6hi, n6lo | n = 6 (one 4-good agent): m ≥ 10 10,000 each with agent orders, m ≤ 9 2,000 each | 26,866 | 100,660,368 | 6: 26,866 |
| (n5hi_cK1, pilots) | rulef.c's K1 (see above) | — | 47,891,806 | — |

Total: 1,162,543,520 profiles evaluated (each: all n first agents, two policies, every single rotation for every
first agent outside K0), 14.0 worker-hours on 4 CPUs. Per-run tables with the classes by m and the best profiles:
`summary_tables.txt` (`python3 k4/rulef_hunt_summary.py RUN ... --merge --tight`). The deep6 step had no seed (no n = 6
unit below nwork 6).

## The 13 tight cores (n = 5, pure)

One profile each (the certificate's labeling where one exists, then the least largest value); `tight.jsonl.gz` has all
8,501, each with its classes, deficits, the frozen agents of every run (bit masks `fzN`, `fzE`, `fz0`), big-top flags,
C₄⁰ and LB₄ʳ's fewest rotations per first agent. "(relabeled)": the profile is on a relabeling of the certificate core's
agents; cores 1784, 2003 and 3082 were tight only so.

| core of `k4_certs_5_pure` | m | profiles | sets | vals | working first agent |
|---|---|---|---|---|---|
| 1373 | 9 | 1,037 | [[0,3,4,6],[1,3,5,8],[2,4,6,7],[4,5,7,8],[5,6,7,8]] | [[2,8,3,4],[3,7,5,6],[2,4,7,8],[2,4,7,8],[3,2,4,8]] | 0 |
| 1557 | 9 | 496 | [[0,2,3,4],[1,4,7,8],[2,3,5,6],[5,6,7,8],[5,6,7,8]] | [[2,3,4,8],[3,7,6,5],[3,6,4,8],[1,6,8,4],[1,6,8,4]] | 0 |
| 1710 | 9 | 1,222 | [[0,3,4,8],[1,4,6,7],[2,3,5,8],[2,5,6,7],[5,6,7,8]] | [[2,3,8,4],[3,7,5,6],[4,2,8,7],[1,6,4,8],[4,3,8,2]] | 0 |
| 1784 | 9 | 400 | (relabeled) [[0,4,7,8],[2,3,4,5],[1,6,7,8],[2,3,5,6],[5,6,7,8]] | [[4,8,5,2],[2,3,8,4],[1,6,4,8],[2,4,7,8],[3,6,5,7]] | 1 |
| 1836 | 9 | 1,128 | [[0,1,2,4],[1,3,4,8],[2,3,6,7],[5,6,7,8],[5,6,7,8]] | [[2,4,8,3],[7,4,2,8],[8,4,1,6],[1,8,4,6],[2,8,4,7]] | 0 |
| 1846 | 9 | 487 | [[0,1,4,8],[1,3,4,5],[2,3,6,7],[2,6,7,8],[5,6,7,8]] | [[2,7,4,8],[4,8,2,3],[4,8,5,6],[1,4,8,6],[1,4,8,6]] | 1 |
| 1861 | 9 | 356 | [[0,1,7,8],[1,3,4,5],[2,3,4,6],[2,6,7,8],[5,6,7,8]] | [[4,8,2,5],[8,3,4,2],[2,4,7,8],[1,6,8,4],[3,8,10,4]] | 1 |
| 2003 | 9 | 280 | (relabeled) [[1,2,3,5],[0,6,7,8],[1,4,5,8],[2,4,6,7],[3,6,7,8]] | [[2,8,3,4],[1,8,4,6],[2,4,7,8],[8,4,1,6],[1,8,4,6]] | 0 |
| 2839 | 10 | 729 | [[0,4,5,9],[1,4,6,8],[2,5,7,9],[3,6,7,8],[6,7,8,9]] | [[3,8,2,4],[4,8,1,6],[3,4,8,6],[1,8,6,4],[8,6,4,1]] | 0 |
| 2945 | 10 | 290 | [[0,3,4,6],[1,6,8,9],[2,7,8,9],[3,4,5,7],[5,7,8,9]] | [[3,2,4,8],[4,8,6,5],[2,7,8,4],[4,7,2,8],[1,6,8,4]] | 0 |
| 2952 | 10 | 627 | [[0,3,4,6],[1,7,8,9],[2,7,8,9],[3,4,5,7],[5,6,8,9]] | [[3,4,2,8],[1,6,8,4],[1,6,8,4],[7,4,2,8],[4,8,1,6]] | 0 |
| 3015 | 10 | 1,209 | [[0,3,5,6],[1,5,6,9],[2,7,8,9],[3,4,7,8],[4,7,8,9]] | [[2,8,4,3],[3,6,4,8],[1,4,8,6],[8,4,6,1],[2,4,8,7]] | 0 |
| 3082 | 10 | 240 | (relabeled) [[0,3,7,8],[3,4,5,6],[1,7,8,9],[2,7,8,9],[4,5,6,9]] | [[4,8,5,2],[8,3,2,4],[2,4,8,7],[1,4,8,6],[4,2,7,8]] | 1 |

Agent orders matter but did not produce a failure: the 120 orders of each of n5hi's 144 tight profiles give nwork 1, 2
and 3, a third each (17,280 profiles), never 0.

## For the proof of Lemma M (what the data suggest; nothing here is proved)

- The hardest profiles found are exactly the situation of rulef.md §6, cases (a)/(b): a first agent that is not the
  first big-top agent leaves three frozen agents, deficit 1, and no rotation of Lemma KR's kind repairs it (LB₄ʳ needs
  two); inserted first, the first big-top agent q holds its top and the run is in K0. On every tight profile found the
  choice "the first big-top agent" is the only one that works, also with two or three big-top agents.
- Tight profiles appear only on pure cores (five 4-good agents) with m = 9, 10; with four 4-good agents the least value
  reached was 2, with one 4-good agent at n = 6 every first agent always worked.

## Time

Wall time about 4 h 05 min (22:25 to 02:30 UTC, of which about 3 h 50 min of searching on all 4 CPUs), 14.0
worker-hours, within the 5-hour budget. Pilots chose the objective variant (key M against R, S and annealing E: no
clear winner per unit of time; M is the asked objective and the fastest; a fifth variant, W, crashed on a bug and was
not rerun).

## Files (`results/k4_rulef_hunt/`)

- `RUN.log`: each starts with the command line, rulef.c's and the evaluator's sha256 and the options (logs of resumed
  runs repeat the header); `ck/RUN.jsonl`: one line per finished unit (best key, best nwork, best profile, histogram
  of restarts, relabeling results); `tight_RUN.jsonl.gz`: the profiles with nwork ≤ 1 of each run; `tight.jsonl.gz`:
  all of them merged (10,638 lines, 8,501 distinct), each line tagged with its run.
- `check.log`: the second implementation on every distinct tight profile; `rulef1_lean.log`: rule F with Lean's exact
  owner step on them; `xcheck/`: the K1 cross-checks above.
- `seeds_*.jsonl`: the seeds of the seed runs; `summary_tables.txt`: the tables of this file.
- `deep5t2_partial.*`, `seeds_tight5b_partial.jsonl`: the first 4 units of deep5t2 with an earlier seed list (one seed
  per relabeled hypergraph, 480 seeds), stopped as too long and rerun with one seed per core; its units are counted.
- `n5hi.log` holds two sessions (the first was stopped by the 30-minute background limit and resumed from the
  checkpoint).
- Code: `k4/rulef_hunt_eval.c` (evaluator), `k4/rulef_hunt.py` (driver), `k4/rulef_hunt_check.py` (second
  implementation), `k4/rulef_hunt_rulef1.py` (rule F, Lean's owner step), `k4/rulef_hunt_seeds.py`, `k4/rulef_hunt_summary.py`, `k4/rulef_hunt_runs.sh` (every run:
  `bash k4/rulef_hunt_runs.sh n5hi n5lo n5n12 seedsH suite n4pure deep5 pure2 n6 deep6 deep5t2 n44r check`, each step
  resumable; then `python3 k4/rulef_hunt_summary.py n5hi n5lo n5n12 n44r pure2 seedsH suite n4pure deep5t deep5x
  deep5r deep5t2 deep5t2_partial n6hi n6lo deep6x --merge --tight`).

## Caveats

- Local search: a counterexample may exist where the search did not go. Agent orders other than the certificate's
  were searched only by the relabeling scans (pure2, n44r, deep runs, n6hi) and the seed runs.
- K1 here is Lemma K's text (`-T1`); rulef.c's own K1 (`-T0`) can only add failures, never remove one (see above).
  rulef.c restricts slot goods outside R_x to one representative and kept-out sets to the options of `prot_sets_in`;
  this is a sound restriction, and on the 8,501 tight profiles and 597 other profiles the classes equal those of the
  second implementation, which has no such restriction.
- Seed runs that start at a profile whose type is not in `core_domains` would add it to the agent's types
  (`extra_types` in the checkpoint); this never happened (every seed's types are strict types of its core).
