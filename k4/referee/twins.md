# Referee review: K4.MC8, double edges in a minimal counterexample (`k4/TWINS.md`, branch `proof/k4-twins`, PR #117)

Referee: `proof/k4-referee`, 2026-11-27.
- Read:
  - `k4/TWINS.md` at `29bb2e6`, §1–§3;
  - `k4/MINCEX.md` §1–§3 (K4.MC0, K4.MC1, the tools) on main;
  - `proofs/min_counterexample.md` §2 (Lemmas M1, M1(b), local states, extensions, domination);
  - the docstring and `states()`/`canonical()` of `k4/check_reductions4.py`, read only for the certificate's state-key
    and token encoding;
  - the checkers' logs `results/k4_twins/check_dbl_q3.log` and `check_dbl_p4q4.log`.
- Data: `results/k4_twins/dbl_q3.json.gz` (41 records) and `dbl_p4q4.json.gz` (245 records).
- Check: `k4/referee/twins_ref.py`, run by `twins_ref_runs.sh`, log `results/k4_referee/twins_ref.log`. Own code, raw
  EFX₀, concrete instances. Nothing from `k4/` was run or imported.

## Verdict: CORRECT (certified result; my check is concrete evidence)

| question | finding |
|---|---|
| Does K4.MC8 follow from the certified coverage? | **Yes.** A double edge e–f whose (configuration, types) is reduced by some record is excluded by K4.MC1. The kind pairs without a Q4 agent (Q3–Q3, Q3–P4, P4–P4, open and closed) are covered for every profile, so one of e, f must be Q4. c = 2 needs two 4-good agents, i.e. Q4–Q4. P3 agents are handled by K4.MC3/MC5 (cited, not re-checked) |
| Gadget legality | **Legal.** All 286 records are fixed-valuation gadgets (DEL, or one agent h on ∂ plus one gadget good z₀′). Each has fewer agents than S, support of ≤ 4 goods inside I′ ∪ ∂, a consistent I/∂ split, and gadget goods new to H. The class 𝒞_β is preserved, by the argument below |
| Does M1(b) apply? | **Yes.** All 286 records declare the unenvied bundle ("source"). My concrete check takes every EFX₀ allocation Y of H′ with an acyclic envy graph and every unenvied bundle of it, which is exactly M1(b)'s setting after F2 |
| Stored extensions, on concrete instances | **Confirmed** (below): every state met is in the certificate; whenever e and f are safe, the outside agents are too; and every excluded configuration is covered on every instance tried |

**𝒞_β is preserved** (my own argument; the checker verifies the same by enumerating connections). Let R be the
incidence graph without S ∪ I, and C₁…C_t the components of R touched by ∂.
- The component of H containing S has cyclomatic number Σβ(C_i) + d_e + d_f + 1 − t, where d_e, d_f count incidences
  to ∂ and the "+1" is the double edge's cycle.
- In H′, h with support T ⊆ ∂ and a pendant gadget good gives a component with Σ_{C_i touched by T} β(C_i) + |T| − t′.
- Since t − t′ ≤ |∂ ∖ T| ≤ d_e + d_f − |T|, this is at most the former, and the components of R that h no longer
  touches are sub-components.
- DEL only deletes.

So H′ ∈ 𝒞_β whenever H ∈ 𝒞_β, for every way the rest connects.

## The concrete check

For each configuration, I built random instances H:
- e and f have the record's goods, with random strict, strictly balanced values;
- I = {g0, g1} plus the private goods;
- 2–3 outside agents value random subsets (≤ 4 goods) of the boundary goods and 2–3 outside goods. Some boundary goods
  may have no outside valuer, which the configuration also covers.

For every record of the configuration:
1. Build H′.
2. Enumerate every EFX₀ allocation Y of H′ with an acyclic envy graph, and every unenvied bundle.
3. Compute the local state in the certificate's canonical form, and look it up.
4. Realize every stored extension of it concretely ('w:h' = h's outside goods, 'W:i' = block i's outside goods) as an
   allocation X of H, and test raw EFX₀ on H.

| configurations | instances | EFX₀ allocations Y of H′ | states looked up (missing) | extensions realized | with e, f safe | outside agent then unsafe (M1 domination) | instances covered |
|---|---|---|---|---|---|---|---|
| Q3–Q3, Q3–Q3-c1, Q3–P4, Q3–P4-c1, Q3–Q4, Q3–Q4-c1 | 480 | 75,732 | 204,817 (0) | 377,528 | 136,946 | **0** | 480 / 480 |
| P4–P4, P4–P4-c1, P4–Q4-c1 | 180 | 11,310 | 28,638 (0) | 129,950 | 41,227 | **0** | 180 / 180 |
| P4–Q4, Q4–Q4-c2 (partially covered) | 50 | 32,717 | 89,654 (0) | 265,712 | 81,157 | **0** | 50 / 50 |

**Sensitivity (mutation).** Each realized extension is altered by moving an interior good of e or f into an outside
bundle that holds a boundary good (the checker's own selftest corruption). This gives **312 domination failures**, and
coverage collapses in every configuration (e.g. Q3–Q3: 0 of 20 instances covered). So the concrete check detects
broken extensions.

Limits:
- This is evidence on concrete instances (random profiles and outside structure, ≤ 3 outside agents and goods). It is
  not a second certificate check. The certificate's own independent checker (`check_twins4.py` → `check_reductions4.py`)
  is the proof artifact, and its logs show all counts and an OK selftest.
- The few uncovered profiles of the partial configurations (e.g. the 20 open Q3–Q4 profiles) were not hit by my random
  profiles. The theorem does not claim them.

## For the coordinator

- K4.MC8: CORRECT as a certified reduction.
  - The gadgets are legal and keep 𝒞_β.
  - M1(b) is the lemma used.
  - The stored extensions behave as claimed on concrete instances: 710 instances and 773,190 realized extensions,
    with 0 failures; the mutation is caught.
- The candidate-list pruning (`twins_filter.py`) was not re-run here.

## Addendum: the candidate filter and its Γ′-level prune (`k4/TWINS.md` §1 at `450a58f`; coordinator's queue, 2026-11-27)

**Read.**
- `k4/TWINS.md` §1;
- `k4/twins_filter.py`: the docstrings of `excluded` and `gamma_prune` and their code, read but not run.

**Check.** `k4/referee/twins_prune_ref.py`, log `results/k4_referee/twins_prune_ref.log`.
- It is my own core-level predicate, written from TWINS.md's table, and my own Γ′-level test, which enumerates every
  completion of a Γ′.
- Data, read as data:
  - the β = 4 core list `results/k4_min_cex_shapes_4.json.gz` (main);
  - the hunt session's β = 5, n = 6 list `results/k4_hunt/mc_n6_b5.json.gz` (`claude/k4-hunt-cegar`).

**Verdict: the Γ′-level prune is SOUND.**

*Argument.*
- In Γ′ an agent's degree is its number of shared goods. Private goods are new goods of degree 1, so they never change
  a shared good's degree.
- An agent with three shared goods becomes Q3 (no private good) or P4 (one), since k ≤ 4. One with four shared goods is
  Q4.
- So two Γ′-degree-3 agents sharing two degree-2 goods form a {Q3, P4} pair with c = |shared| − 2 ∈ {0, 1}. All of
  those are certified.
- A degree-3 and a degree-4 agent sharing two degree-2 goods and a third good form a {Q3 or P4, Q4} pair with c = 1,
  which is certified.
- Pairs with a Γ′-degree-2 agent (P3, or a 4-good agent with two private goods) and the uncertified cases are never
  pruned:
  - open Q3–Q4 or P4–Q4;
  - every Q4–Q4.
- So the prune removes a Γ′ only when every core built on it contains a certified double edge.

*Computation.*

| list | cores | excluded by my core predicate | left | distinct Γ′ | Γ′ with some but not all completions excluded | stated rule ≠ "every completion excluded" |
|---|---|---|---|---|---|---|
| β = 4 | 5,558 | **2,392** | **3,166** | 1,163 | 0 | 0 |
| β = 5, n = 6 | 30,337 | **9,455** | **20,882** | 4,143 | 0 | 0 |

Both counts are TWINS.md's. On these lists the Γ′ prune is exactly the core-level filter.

*Not checked.*
- The β = 5 counts for n ≥ 7, which come from a single implementation of the pipeline.
- The domain cuts (`cut_domains`), which depend on the uncovered-profile files.

## Addendum 2: K4.MC9, claws (`k4/TWINS.md` §4 on `proof/k4-twins-2` at `ea71fb54`, PR #135; coordinator's queue, 2026-11-27)

**Read.**
- `k4/TWINS.md` §4.
- The diffs of `k4/check_twins4.py` (the three hard-coded configurations and the new sensitivity case).
- `k4/reduce4c.py`: its docstring and the re-check in `rebuild` and `_chunk`.
- The logs `check_claw.log`, `reduce4c_test.log` and `count_b5_mc9.log`.

`reduce4c.c` was not read line by line, because soundness does not depend on it (below).

**Checks.**
- `claw_ref.py`, which reuses my K4.MC8 concrete check `twins_ref.py` (own code, raw EFX₀), and `claw_filter_ref.py`.
- Runs `claw_ref_runs.sh`; logs `results/k4_referee/claw_ref.log` and `claw_filter_ref.log`.

## Verdict: SOUND (certified result; my checks are concrete evidence)

| question | finding |
|---|---|
| Does K4.MC9 follow from the certified coverage? | **Yes.** A claw is three P3 agents on a good G of degree 3. Each f_i holds G, a private p_i, and a third good y_i of degree ≥ 2. So the y's are all distinct (claw), two equal (claw-y12 up to relabelling), or all equal (claw-y123), and all 216 profiles of each are certified. K4.MC1 then excludes the claw |
| Two-agent gadgets legal? | **Yes.** H′ has n − 1 agents. Each gadget agent values ≤ 4 goods: its boundary goods (≤ 3) and one gadget good of its own, new to H. 𝒞_β is preserved by the argument below, which needs the forest condition. My own scan of the 8 two-agent records: all are forests on ∂, each gadget agent has exactly one own gadget good, and the gadget goods are disjoint |
| Does the C proposer affect soundness? | **No.** `reduce4c.py` rebuilds every C proposal and asserts reduce4's own domination test, moved-items test, views and safe masks before using it. The certificate is then re-checked by `check_twins4.py` → `check_reductions4.py`, whose functions are unmodified and whose configurations are hard-coded. The C code can only lose coverage. The 12 agreement tests are evidence that it does not |
| Stored extensions, on concrete instances | **Confirmed** (table below) |
| Effect on the candidate lists | **Reproduced** with my own predicate: β = 4, 3,166 → **2,079**; β = 5, n = 6, 20,882 → **20,553**, the same set of cores as `mc_n6_b5_mc9.json.gz` |

**𝒞_β is preserved by two-agent gadgets** (my own argument; the checker verifies it by enumerating connections).
- Let R be H without S ∪ I, and C₁ … C_t the components of R that contain a boundary good.
- The claw has 9 incidences and |S ∪ I| = 7. So H's component through S has
  β_H = Σβ(C_i) − t + 3.
- In H′, take h₁ and h₂ with supports T₁, T₂ ⊆ ∂ and one pendant gadget good each. Let u = |T₁ ∪ T₂|, let t′ be the
  number of C_i they touch, and let c′ be the number of H′-components containing a gadget. These components have total
  cyclomatic number Σ_{touched} β(C_i) − t′ + |T₁| + |T₂| − 2 + c′.
- So each of them is ≤ β_H as soon as (t − t′) + |T₁| + |T₂| + c′ ≤ 5. This holds:
  - t − t′ ≤ 3 − u, since each untouched C_i contains an untouched boundary good;
  - the forest F on {h₁, h₂} ∪ T₁ ∪ T₂ has |T₁| + |T₂| ≤ 2 + u − comp(F);
  - and c′ ≤ comp(F).
- For claw-y12, |∂| = 2 and the bound is 4.
- Components without a gadget are components of R, hence subgraphs of H's components.
- Without the forest condition the count breaks: h₁, h₂ on the same two boundary goods add a cycle, which the
  checker's sensitivity case rejects.

**The concrete check.**
- Random instances H containing the configuration: f_i with random strict, strictly balanced values on (G, y_i, p_i);
  2–3 outside agents on random subsets of the boundary goods and 2–3 outside goods. Some boundary goods have no outside
  valuer.
- For every record with fixed gadgets (DEL, one-agent, and the two-agent pairs):
  - every EFX₀ allocation Y of H′ with an acyclic envy graph, and every unenvied bundle;
  - the local state, looked up;
  - every stored extension, realized and tested by raw EFX₀ on H.

| configuration | instances | EFX₀ allocations Y of H′ | states looked up (missing) | extensions realized | with S safe | outside agent then unsafe | instances covered |
|---|---|---|---|---|---|---|---|
| claw (11 records, 7 two-agent) | 150 | 132,547 | 414,893 (0) | 715,306 | 277,102 | **0** | **150 / 150** |
| claw-y12 (4 records, 1 two-agent) | 150 | 11,291 | 28,127 (0) | 93,859 | 23,042 | **0** | **150 / 150** |
| claw-y123 (2 records) | 150 | 1,651 | 3,070 (0) | 15,639 | 4,486 | **0** | **150 / 150** |

- A further 60 claw instances (seed 11) are all covered, with 0 domination failures.
- **5 of them are covered only by the two-agent records**, so those gadgets are exercised and behave as claimed.

**Sensitivity (mutation).** Each realized extension is corrupted by moving an interior good of an S agent into an
outside bundle that holds a boundary good. On 20 + 20 instances this gives **2,995 domination failures**, and
coverage collapses: 0 of 20 instances covered, for both claw and claw-y12.

**Not checked.**
- `reduce4c.c` itself; it is not needed for soundness.
- The β = 5 counts for n ≥ 7, a single implementation.
- The bound remark "n ≤ (8/3)(β − 1) for cores without Q4 agents".
