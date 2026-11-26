# Referee report: Theorem T1, Lemmas SINK, PARK, SLACK (branch `claude/k4-girth`, `k4/girth.md` §3–§4)

Referee: `proof/k4-referee`, 2026-11-26. Read: `k4/girth.md` at `5b79844` (all of it), and LSS itself. See §5 for what changed at `90c116f`.
- LSS: T. Lianeas, A. Sgouritsa, M. M. Sotiriou, "EFX Allocation In (Multi)Hypergraphs", arXiv 2608.03171v1.
- I fetched the PDF and extracted its text myself with `pdftotext -layout` (sha256 `a720a6e4…cb53`).
- Read in full: §2 (model, cycles, Observations 2.1, 2.2) and §3 (Algorithms 1–3, Lemmas 3.1–3.5). §4 skimmed for
  the uses of Observation 2.2.

Checks: `k4/referee/girth_ref.py`, runs `k4/referee/girth_ref_runs.sh`, log `results/k4_referee/girth_ref.log`. They
are written from LSS's text and `k4/girth.md`; no code is shared with `k4/girth/`.

## Verdicts

| item | verdict |
|---|---|
| Theorem T1 (linear + an agent on no 3-cycle ⇒ EFX₀, monotone valuations) | **CORRECT** |
| Lemma SINK | CORRECT |
| Lemma PARK | CORRECT (one degenerate case to state: N ≠ ∅ when there are goods valued by nobody) |
| Lemma SLACK | CORRECT |
| (in passing) Facts F1–F6 | CORRECT for additive valuations. The remark "the proofs also work for monotone valuations" is **false for F2** (counterexample below). Nothing proved depends on it. |

## 1. Theorem T1 against LSS's text

**The digest is accurate.** In §3, Observation 2.2 (the only consequence of girth ≥ 4) is invoked exactly once. It
is in Lemma 3.4, for a neighbour j of 0 outside the edge f that 0 and i share: "Due to Observation 2.2, vertices i, j
cannot both belong in the same edge". Every other step uses Observation 2.1 (two vertices share ≤ 1 edge), or nothing:
- Lemma 3.2 (line 4 of Algorithm 2);
- Lemma 3.4, |X_i| > 1 and j ∈ f;
- Lemma 3.5, both lines.

Lemma 3.3 uses only the labels.

**The replacement step.** Suppose X_i = {e}, e ≠ f_i, and j is a neighbour of 0 with j ∉ f_i and j ∈ e. Then
(0, f_i, i, e, j, f_j, 0) is a Berge 3-cycle:
- the vertices 0, i, j are distinct;
- f_i ≠ f_j, since j ∉ f_i;
- e ≠ f_i by assumption;
- e ≠ f_j, since otherwise 0 and i would share e and f_i.

So if 0 lies on no 3-cycle, j does not value e, and Lemma 3.4 holds under girth ≥ 3 alone. The rest of the proof
is LSS's, unchanged.

**Two small points LSS's text leaves implicit; both hold in T1's setting.**
- Lemma 3.4 does not mention that vertex 0 itself does not envy i. It does not: 0 and i share only f, so 0 ∉ e (Obs.
  2.1).
- §3's model is a *set* of edges. Our goods give parallel edges of size 0 (goods nobody values) and size 1 (several
  private goods of one agent). Such edges lie on no Berge cycle, and I checked each lemma:
  - private edges of i are irrelevant to every j ≠ i (Lemmas 3.2, 3.4);
  - Algorithm 3's line 1 never selects a size-0 edge, and line 4 gives it to 0, where nobody values it (Lemma 3.5).

  So T1 holds for our instances, in which every good is the edge of its valuers.

**Monotone valuations.** T1 uses LSS's model: monotone, normalized, and v_i(S ∪ {e}) = v_i(S) for i ∉ e. The edge
of a good is its set of *relevant* agents. For additive valuations that is {i : v_i(g) > 0}, the reading of
`k4/girth.md` §1.1.

**Computation** (evidence). LSS's Algorithms 1–3 are implemented from the text. Every choice is random: the labels of
the neighbours and non-neighbours, which envied vertex in Algorithm 2, argmax ties, which (e, j) in Algorithm 3.
Each instance is a random linear hypergraph with edges of size 0–4 (including private and dead goods). Every vertex
on no 3-cycle is tried as 0, five runs each. Properties (1)–(4) are asserted after Algorithm 2, and at the end the
allocation is checked against the raw EFX₀ definition and for completeness.

| set | instances (with a 3-cycle) | runs | failures |
|---|---|---|---|
| additive, n = 3–7, m ≤ 10, degree ≤ 4 | 20,000 (7,410) | 411,820 | 0 |
| monotone, same | 20,000 (7,519) | 411,115 | 0 |
| additive, n = 5–9, m ≤ 14, degree ≤ 6 | 5,000 (3,161) | 120,690 | 0 |
| monotone, same | 5,000 (3,183) | 119,850 | 0 |
| **mutation**: vertex 0 *on* a 3-cycle, additive | 3,000 | 51,890 | **9,834**, all Property (2) for a neighbour (G4) |

The mutation shows the hypothesis is used exactly where the proof says. Example: R = [{0, 1, 2, 4}, {2, 3}, {3, 4}],
vertex 0 = agent 2. The F2 counterexample is re-checked by brute force in `results/k4_referee/girth_f2_monotone.log`.

## 2. Lemmas SINK, PARK, SLACK

- **SINK.** If nobody envies X_s ∪ U, nobody strongly envies it. The other bundles are unchanged, and s's value only
  rises. Correct. The "clean sink" remark is correct too: v_i(X_s ∪ U) = v_i(U_i) ≤ v_i(X_i) by (4) when
  X_s ∩ R_i = ∅, and v_i(X_s) ≤ v_i(X_i) when U_i = ∅.
- **PARK.** Correct. I re-derived the case split.
  - k envied with u ∈ S_k: Y_u ∩ R_k ⊆ X_u ∪ U_k.
  - Otherwise: every good of Y_u that k values contains both u and k, so there is at most one (linearity). It is
    bounded by u's non-envy if it lies in X_u, and by (3) if it lies in U.
  - Hypothesis (4) is never used.
  - Degenerate case: goods valued by nobody need a non-envied agent. In a partial EFX₀ orientation every agent can be
    envied (an envy 3-cycle on a triangle). The lemma should say "if N ≠ ∅", or rotate envy cycles first (F5).
- **SLACK.** Correct.
  - If k values f and e, removing either good leaves one good worth ≤ v_k(X_k): f by u's non-envy, e by (3).
  - Otherwise k sees at most one of them.
  - The proof's aside "k is the only such agent" is true (two such agents would share f and e), but it is not needed.
- **The combination** (§3, last paragraph). With every leftover good having only envied valuers, park sinks plus
  distinct one-good absorbers that take nothing else give EFX₀. Correct: the two proofs do not interact, because
  absorbers are not sinks. Goods valued by nobody must go to a non-absorber, since an absorber holding {f, e, z} can
  be strongly envied through {f, e}.

**Computation** (evidence). For each small random linear instance, every partial orientation is enumerated, and the
EFX₀ ones with (3) for all agents and (4) for the envied are kept. Then every applicable SINK, every PARK completion
(up to 200 choices per state), every SLACK pair, and park + absorber combinations are tested against the raw EFX₀
definition.

| set | states | SINK cases | PARK completions | SLACK cases | combinations | failures |
|---|---|---|---|---|---|---|
| additive, n = 3–5, m ≤ 7 | 11,221 | 28,362 | 56,179 | 20,323 | 4,760 | 0 |
| monotone, same | 19,233 | 52,865 | 126,888 | 37,254 | 4,593 | 0 |
| additive, n = 4–6, m = 5–8 | 5,174 | 15,473 | 49,380 | 13,549 | 3,657 | 0 |
| monotone, same | 9,889 | 31,683 | 110,982 | 26,495 | 3,539 | 0 |

## 3. In passing: F1–F6

All six are correct for additive valuations. I re-derived F3, F4 and F6's move (i's new bundle {h} ∪ U_i is envied by
nobody: a valuer of h sees only h, a valuer of a good of U_i sees only that good).

**F2 is false for monotone valuations**, contrary to "the proofs also work for monotone valuations". The proof adds e
to a non-envied valuer j as a Pareto improvement, but a relevant good need not raise a monotone value. Counterexample:
- agent 0 has R₀ = {e, f} with f₀({f}) = 5, f₀({e}) = 1, f₀({e, f}) = 5;
- agent 1 has R₁ = {g} with value 1;
- X = ({f}, {g}), e unallocated.

The value vector (5, 1) is Pareto-maximal among partial EFX₀ orientations, 0 is non-envied, and e has the
non-envied valuer 0. F2 is used only for Conjecture L's additive consequence, so nothing proved changes. The remark
should say "additive" for F2.

## 4. For the coordinator

- Theorem T1, Lemmas SINK, PARK, SLACK: CORRECT. They can be recorded as PROVED.
  - T1 is for linear hypergraphs in LSS's monotone model with an agent on no 3-cycle. Goods valued by nobody and
    several private goods per agent are allowed.
  - Its corollary (a linear TARGET₄ counterexample has every agent on a 3-cycle and a good with ≥ 3 valuers) follows
    with T3.
- Small fixes: PARK needs N ≠ ∅ when goods valued by nobody exist; F2's monotone remark is wrong.
- Conjecture L remains a conjecture. Nothing here bears on it beyond the facts above.

## 5. Addendum: changes at `90c116f` (22:15 UTC)

- **Lemma SLACK was generalized.** The new form: any hypergraph, monotone valuations, X a partial EFX₀ allocation with
  (3), u non-envied with X_u = {f} or X_u = ∅, and e any unallocated good. Re-derived: **still CORRECT**.
  - If k values f and e, each one-good remainder is bounded: f by u's non-envy, e by (3).
  - Otherwise k sees one of them.
  - X_u = ∅ gives a singleton.
  - Linearity was never used, as §2 above already noted.
- **Proposition HT** (new, marked PROVED): H_t and HH_t are linear and ℓ lies on no 3-cycle, so T1 covers every
  profile on them. Not refereed here; it is a hypergraph fact plus T1.
- **Conjecture L and PL** are now REFUTED by the session. That does not affect T1, SINK, PARK or SLACK. The F2
  remark of §3 is moot for L.
