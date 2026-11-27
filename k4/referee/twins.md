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
