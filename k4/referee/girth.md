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
  profile on them. **H_t part: CORRECT** (checked in passing).
  - The written argument re-derived: a 3-cycle through ℓ must use g_1 and z, hence x_{1,i} and y_t, which share a good
    only when t = 1.
  - `k4/referee/ht_ref.py` rebuilds H_t from `k4/c4.md` §7. For t ≤ 6, H_t is linear and ℓ is on no 3-cycle exactly
    for t ≥ 2. LSS with vertex 0 = ℓ ends EFX₀ on 40 random additive and monotone profiles per t (log
    `results/k4_referee/ht_ref.log`).
  - HH_t was not rebuilt here.
- **Conjecture L and PL** are now REFUTED by the session. That does not affect T1, SINK, PARK or SLACK. The F2
  remark of §3 is moot for L.

## 6. Addendum: Lemma EC and the stuck-state consequence (`235bca4`, unchanged at `ab906c8`; coordinator's queue, 2026-11-27)

Read: `k4/girth.md` §5 ("Envy-cycle rotation and the stuck states"), with the definitions of Properties (1)–(4)
(§1.2) and Lemma SLACK (§3). Check: `k4/referee/girth_ec_ref.py`, run by `girth_ec_ref_runs.sh`, log
`results/k4_referee/girth_ec_ref.log`. Own code, raw EFX₀, additive and non-additive monotone valuations.

**Verdict: CORRECT** (one premise left implicit, stated below).

- **Lemma EC.** Rotating an envy cycle i₁ → i₂ → … → i₁ (each i_l takes X_{i_{l+1}}) keeps EFX₀ and (3). Re-derived:
  - the bundles are the same sets, and values weakly rise, strictly on the cycle;
  - an agent never strongly envies its *old* bundle, now someone else's: v_i(new) > v_i(X_i) ≥ v_i(X_i ∖ g);
  - toward every other bundle, its value only rose;
  - agents off the cycle see the same sets at the same values;
  - (3) persists because U is unchanged.

  Monotonicity is all that is used. Correct.
- **Stuck states.** No envy cycle means the envy graph is acyclic, so it has a source: a non-envied agent exists. If a
  non-envied agent u held ≤ 1 good, Lemma SLACK would make every leftover placeable on u, so the state would not be
  stuck. Correct.
  - **The implicit premise:** SLACK needs (3) for all agents at the stuck state. "(3) persists" is right: parking steps
    only raise values and shrink U, and EC keeps (3). But it needs (3) when parking *starts*. That holds for the state
    LSS's Algorithm 2 hands over, with or without the G1 repair, since Algorithm 2 always ends with FixProp3. It
    should be said, because the stuck-state statement is false for parking runs started from a state without (3)
    (control below).

**Computation (evidence).**
- Instances: 200,000 random instances (n = 2–5, ≤ 4 relevant goods), half additive and half monotone non-additive
  (sum of the two largest values).
- States: FixProp3 from the empty allocation, and random EFX₀ partial allocations with (3); then random walks of
  dynamic-parking steps and envy-cycle rotations (1,094,836 states).

| check | tests | failures |
|---|---|---|
| EC at (3)-states: EFX₀ and (3) kept, values weakly up, cycle strictly up | 10,290 rotations | 0 |
| EC on EFX₀ partial allocations without (3): EFX₀ kept | 124,368 | 0 |
| SLACK core: a non-envied agent with ≤ 1 good absorbs any leftover (states with (3)) | 2,973,139 | 0 |
| stuck states: a non-envied agent exists and all non-envied agents hold ≥ 2 goods | 5,221 | 0 |
| control: the SLACK core on EFX₀ states *without* (3) | 784,999 | **442,797** fail |

So (3) is exactly what the consequence needs.

## 7. Addendum: Lemma RF-PATH (`k4/girth.md` §7 at `8f7ba8aa`, PR #102), with TTC's Lemma RF-ROT (`k4/ttc.md` §14.7 at `d451ea0c`, PR #125) (coordinator's priority item, 2026-11-27)

**Verdict: both CORRECT.** Script `rfpath_ref.py` (own code: serial dictatorship from the definition, no shared code),
runs `rfpath_ref_runs.sh`, log `results/k4_referee/rfpath_ref.log`.

**The basic fact.** If j picks before i in an SD order, i's pick was free at j's turn, so v_j(Y_j) ≥ v_j(Y_i). Hence j
does not want Y_i. This holds with ties too, and at non-perfect starts: a pickless j values every free good at 0.

**RF-ROT, re-derived.**
- By the basic fact, only later pickers can want a pick. So the last picker is a receiver (unfrozen).
- σ_{n−1} is a receiver unless σ_n wants its pick.
- With exactly one receiver, that receiver is σ_n, so RF is the rotation (σ_n, σ_1, …, σ_{n−1}).
- In the rotated order σ_{n−1} picks last, so it is a receiver of the RF start.

**RF-PATH, re-derived step by step.**
- *t = Y_u.* Then t was free throughout σ and nobody before u took it. Removing it first changes no choice, so Y′ = Y.
- *t ≠ Y_u.* Then t is not junk: junk is free at u's turn, and u would have taken its top good. So t = Y_{x₁}.
- *The invariant.* A′_k = A_k ∖ {m_k} with m_k ∈ A_k.
  - If Y_a ≠ m_k, then Y_a ∈ A′_k ⊆ A_k is still a's best good, and m is unchanged.
  - If Y_a = m_k, a is ejected and takes its best g ∈ A_k ∖ {m_k}. Since g was free when a chose Y_a in σ,
    v_a(g) < v_a(Y_a) by strictness. Then A_{k+1} = A_k ∖ {m_k} and A′_{k+1} = A_{k+1} ∖ {g}. If a takes nothing,
    A′ = A from then on.
  - g is free after a's turn in σ, so its σ-holder (if any) picks later. This gives the increasing path, (a) and the
    losses in (b).
  - The path stops when the missing good is picked by nobody before u, i.e. it is junk of Y or Y_u.
  - u gains strictly, because t is its strict top.
- *(c).* Let g be d's new good.
  - Agents after d in σ′ keep their picks and had g free at their σ-turn, since nobody between d and u picks it.
  - Agents before d in σ′ (u included) had g free at their σ′-turn.
  - So nobody wants g. σ_{n−1}, the last picker of σ′, is unfrozen by the basic fact.
  - Hence at a one-receiver RF start, d = σ_{n−1}. If d receives nothing, its empty bundle is wanted by nobody either,
    and the conclusion stands.

**Check** (random instances: strict values, n = 2–7, m = n … n + 5; ≤ 4 relevant goods per agent, or up to 12;
random orders; picks not required to be perfect):

| | ≤ 4 goods | ≤ 12 goods |
|---|---|---|
| instances | 400,000 | 400,000 |
| t = Y_u (Y′ = Y) | 212,951, 0 changed | 208,076, 0 changed |
| path cases (lengths 1 / 2 / 3 / 4 / ≥ 5) | 187,049 (154,673 / 28,988 / 3,199 / 185 / 4) | 191,924 (150,352 / 35,759 / 5,319 / 469 / 25) |
| failures of (a) shape, (b) losses, (b) u's gain, (c) d unfrozen, (c) σ_{n−1} unfrozen | **0** | **0** |
| one-receiver RF starts: d = σ_{n−1} | 18,531 of 18,531 | 23,117 of 23,117 |
| RF-ROT: last picker a receiver; σ_{n−1} unless σ_n wants its pick; one-receiver starts with receiver ≠ σ_n | 0 / 0 / 0 (30,676 one-receiver starts) | 0 / 0 / 0 (35,171) |

**For the campaign.**
- RF-PATH and RF-ROT are general SD facts (any n, any strict additive values), and the statement used is exactly
  what is proved.
- They give DEMOTE (a) in general, with the remark that ℓ ≤ 2 is a data observation at the OC₁^max failures only.
  Random orders give paths up to length 6.
- The open half of RF is the completion statement: "(i) owner w or d, or (T), or (C)".

**Generalized RF-PATH** (`k4/girth.md` §7 at `712a5688`). u is any receiver of a perfect start Y (no agent wants Y_u),
and σ′ = (u, σ − u). The coordinator's priority item, needed for RF at n ≥ 5: **CORRECT.**

*Re-derivation.*
- t is a pick of an agent x₁ *before* u in σ: a good picked later, or junk, was free at u's turn.
- The invariant is A′ = A ∖ {m} before u's old turn. At that turn σ removes Y_u and σ′ does not, so
  A′ = (A ∖ {m}) ∪ {Y_u} after it. If m = Y_u there, because an earlier ejected agent took Y_u, the runs agree from
  then on.
- A non-ejected agent a keeps Y_a. Every other good of A′ was free at a's σ-turn, except Y_u, which a does not want.
- An ejected agent's new good g is either free at its σ-turn, or Y_u, which it does not want. With strict values,
  v_a(g) < v_a(Y_a) in both cases.
- If g = Y_u, or g is picked by nobody later in σ (so g is junk of Y), the chain stops. Otherwise the later σ-holder
  of g is ejected next. This gives (a) and (b). The path may pass u's old position.
- *(c), g = Y_u.*
  - Off-path agents keep their picks, and did not want Y_u at Y.
  - Path agents and u chose their new goods while Y_u was free in σ′.
- *(c), g junk of Y.* This is the argument of the u = σ_n case.
- The receiver hypothesis is used twice: once for non-ejected agents and once for ejected ones.

*Check* (`rfpath_ref.py … receiver`; perfect starts, u a random receiver):

| | ≤ 4 goods | ≤ 12 goods |
|---|---|---|
| path cases | 63,983 | 92,645 |
| of which u is not the last picker | 23,322 | 35,305 |
| failures of (a), (b) and (c) (d unfrozen; σ_{n−1} parts when u = σ_n) | **0** | **0** |

*Mutation* (u a frozen agent: the hypothesis dropped), 2,132 path cases:
- 1,474 shape failures;
- 1,818 loss failures;
- 392 cases with d wanted.

So the receiver hypothesis is needed, and it is enough.

**On PR #102 as a whole.** My referee verdicts cover:
- Theorem T1 and Lemmas SINK, PARK, SLACK (§2 above, CORRECT);
- Lemma EC and the stuck-state consequence (§6, CORRECT);
- RF-PATH in both forms (here, CORRECT).

Not refereed by me:
- the DYN∃ certification K4.GIRTH.DYN4 (`dyncert.py`, with girth's own second covering);
- Conjecture DOM;
- Rule RF and Lemma DEMOTE (evidence and conjectures).

The PR edits no ledger row.

**Lemma RF-T and Corollary RF-T′** (`k4/girth.md` §7 at `3e64bf0d`; coordinator's queue): **both CORRECT.**

*Re-derivation.*
- X is complete: J = {g, j, z}, the picks move along the path and the trade, and p is off the path.
- All bundles have ≤ 2 goods, so EFX₀ fails only by someone valuing a single good of another two-good bundle above
  its own.
- g, j, z and Y_u are excluded for everyone:
  - agents before d in σ′ had them all free;
  - agents after d are off the path, with junk free at their σ-turn and Y_u unwanted at Y;
  - d: the trade, and its σ′ choice of g;
  - p: the trade, z free at its σ-turn, and Y_u unwanted.
- That leaves exactly (W-d) and (W-p).
- RF-T′:
  - path agents x_s (s ≤ ℓ − 2) chose Y′ while Y_d was free;
  - d is covered by (F1), off-path agents by (F2), and Y_p's valuers by (F3);
  - u holds its top good, which is neither Y_d nor Y_p.
- The proof uses neither |U′| = 1 nor D_T′ = ∅.

*Check* (`rfbp_rft_ref.py rft`; 1,500,000 random strict instances, n = 4–7; every trade in the lemma's setting):
- 844 trades, all with X complete;
- raw EFX₀ ⟺ (W-d) ∧ (W-p) at all 844 (321 EFX₀, 523 not), 0 mismatches;
- 144 meet (F1)–(F3), and all 144 are EFX₀.

Log `results/k4_referee/rfbp_rft_ref.log`.

**The SINK form of DEMOTE** (`k4/girth.md` §7 at `ea279bb9`; coordinator's queue). It is stated as a **CONJECTURE**, and
nothing new in it is written as a proof. Its proved parts are the lemmas it cites. Each of their allocations has the
SINK shape, which I checked against the statements:
- RF-A1: w absorbs, and d receives one junk good h. CORRECT, `oc1_hall.md` addendum.
- RF-B: d absorbs everything left, Y′_d and J′ ∖ S. CORRECT, same addendum.
- RF-T: d receives the one good Y_u, and x_{ℓ−1} the one good z. CORRECT, above.
- The (1, 3) form is TTC's Lemma C13, which I have not refereed.

The conjecture's data claims (161,520 n = 4 RF starts; the n = 5 classes) were not re-run here. My n = 4 recomputation
of the A1 and B classes (`rfres_ref.py`) shows the SINK shape at all 32,000 and 43,520 starts.

## Addendum: replay of the 32 three-ring (T\*) certificates (`k4/girth/oc1_tstar.py`, `results/k4_girth_oc1_tstar.log` at `bbf55da7`)

**Read:** `k4/girth.md` §7 (DEMOTE-0, "32 need a 3-ring (T\*)") and the script, as a statement of the certificate.
**Check:** `k4/referee/tstar_ref.py` (`tstar_ref_runs.sh`), log `results/k4_referee/tstar_ref.log`. The code is my
own, with raw EFX₀ and my own move generator. Nothing from `k4/girth/` or `k4/sdc/` is run.

The input is my rebuild of the n = 5 DEMOTE-0 starts from the certifier's two exports: 113,484 starts, of which 274 have
no one-absorber completion at the picks.

**Result: CONFIRMED.**
- **OC₁ after one move** (my own search: additions, chains, rings, then one-absorber) holds at all 274.
- **(T), 242 starts.** Each has an improving trade: a pick-dangerous p takes {Y′_d, j} and d takes Y′_p. At every one,
  some such trade completes with each remaining junk good going to a different agent, i.e. with no absorber. This is
  girth's explicit (T) form.
- **(T\*), 32 starts.** None has an improving trade.
  - All are on 5_pure#374, with RF path u → d of length 1.
  - Each has exactly two improving 3-rings c1 → c2 → d: c1 takes {Y′_d, j}, c2 takes Y′_{c1}, d takes Y′_{c2}.
  - Both are official moves (found by my ring generator), and both become EFX₀ when d then absorbs all remaining junk.
    So the certificate holds at 32 of 32.
- **Roles at Y:** u U, d Dp, c1 DT, c2 Dp, and c2 keeps its pick. This is the log's line exactly, and girth.md's
  "(D_T, D_T, U, D, D)". At Y′, c1 is Dp and c2 is F (frozen, values no junk). That matches girth.md's "a frozen agent f
  takes Y′_p", with only c1 adding a junk good.

So DEMOTE-0 at n = 5 is covered:
- 113,210 at once (NA, or RF-A1\* on 71,443);
- 242 by (T);
- 32 by (T\*).

## Addendum: Lemma ORD and Lemma RF-T-A (`k4/girth.md` §7 at `56941dc6`, draft PR #161)

**Read:** RF-T, RF-T′, "Lemma ORD and (F2)", "Consequences for RF-T", "The right target" and Lemma RF-T-A, line by
line.
**Check:** `k4/referee/rft_ref.py` (`girth_ref_runs.sh`), log `results/k4_referee/rft_ref_300.log`. The code is my
own, with raw EFX₀ and my own official moves. Nothing from `k4/girth/` is run. The sample is girth's counterfactual
sample, rebuilt independently: 300 random strict balanced profiles on each of the 656 pure n = 5 cores with m = 8, every
order, every receiver u of Y, and RF-T's setting at Y′. Y is not required to fail OC₁. I keep starts with any number of
receivers at Y and split the counts.

### Lemma ORD: CORRECT WITH FIXES (a hypothesis to state)

- The argument "a can want b's pick only if b picks before a, so the last picker is a receiver" is correct at perfect
  starts.
- "Y has the one receiver u, so u = σ_n" uses **Y has exactly one receiver**. RF-T's setting does not state this: it
  speaks of Y′ only.
  - At n = 5 every exported failing start has one receiver.
  - But K4.SDC.R2.N5 has two-receiver failing starts, and RF starts from those are in scope.
  - So the statement should add "Y has exactly one receiver u".
- **(F2) needs no such hypothesis.** Y′ has the single receiver d, so d is the last picker of σ′ = (u, σ − u):
  - if u = σ_n, then d = σ_{n−1}, and only u picks after d in σ;
  - otherwise d = σ_n, and nobody picks after d.
  - Either way, no agent other than u wants Y_d at Y.
- With (F2), the reduction "(W-d) ⟺ (F1′)" is correct:
  - u holds its top;
  - x_s for s ≤ ℓ − 2 picked before x_{ℓ−1} in σ′ with Y_d free (path order is σ′ order);
  - off-path agents are covered by (F2), and p's value rose;
  - only d remains.
- The (W-p) remark is also correct. It reads "before p" in σ′ for path agents, which is the same relative order as σ.

| check (all settings of the sample) | count |
|---|---|
| RF-T settings, by the number of receivers of Y (1 / 2 / 3 / 4) | 1,123 / 10,557 / 10,191 / 4,011 |
| one receiver: u = σ_n and d = σ′_n | 1,123 of 1,123 |
| (F2) | at all 25,882 settings, any number of receivers |
| RF-T's reduction: X EFX₀ ⟺ (W-d) ∧ (W-p) | 28,405 of 28,405 trades |
| (W-d) ⟺ (F1′) | 28,405 of 28,405 trades |

### Lemma RF-T-A: CORRECT WITH FIXES (Y must have one receiver); false without it

**With Y having exactly one receiver u, the proof is correct:**
- *u wants Y_p:*
  - p is frozen at Y, since every agent but u is;
  - its wanter picks after p;
  - by (W-p), neither an off-path agent nor x_s (s ≤ ℓ − 2) wants Y_p, since v(Y_p) ≤ v(Y_{x_{s+1}}) < v(Y_{x_s});
  - x_{ℓ−1} doesn't, by (A0); d doesn't, by ¬(F1′).
- *u values exactly {t, Y_u, Y_d, Y_p}:*
  - u values Y_d because d is frozen and, by ORD, only u can want Y_d. The text leaves this step implicit.
  - The four goods are distinct: x₁ ≠ d since ℓ ≥ 2, and p is off the path. With k = 4, u values no junk.
- *The move is official:*
  - p values g, since otherwise v_p(j) > v_p(Y_p) contradicts j being junk;
  - H₀ = {g, j} (+ Y_u) ⊆ J ∪ B_u;
  - u's step improves.
- *X_A is EFX₀:*
  - u's bundle {Y_p, z}: z is junk, below every pick. Y_p is covered for p (trade), d (¬F1′), the others (as above)
    and x_{ℓ−1} (A0).
  - p's bundle {g, j, Y_u}: u values only Y_u, worth less than Y_p.
  - For d, k = 4 leaves at most one good besides g, Y_p and Y_d:
    - if it is Y_u: v_d(g) + v_d(Y_u) < v_d(Y_p) + v_d(Y_u) < v_d(Y_d);
    - if it is j: (A1);
    - otherwise: v_d(g) < v_d(Y_d).
  - Everyone else: (A2).

| one-receiver Y, sub-case "(W-p) holds, (F1′) fails" | count |
|---|---|
| settings / trades | 97 / 100 |
| u wants Y_p; R_u = {t, Y_u, Y_d, Y_p}; chain official | 100 / 100 / 100 |
| (A0)–(A2) hold | 78: **X_A raw EFX₀ at all 78** |
| a hypothesis fails ((A0) 1, (A1) 3, (A2) 18) | 22: X_A not EFX₀ at all 22, so the hypotheses are exact here |

**Without "Y has one receiver" the lemma is false.** In the same sample, with two to four receivers at Y, (W-p) holds,
(F1′) fails, and (A0)–(A2) hold, yet X_A is not EFX₀ at:
- 545 trades (two receivers);
- 3,783 (three);
- 3,509 (four).

The proof breaks at "some agent wants Y_p, and it is u": p can be a receiver at Y.

The smallest kind, from the log:
- the core `[[0,2,4,7],[1,3,5,7],[2,4,6,7],[3,5,6,7],[4,5,6,7]]`, σ = (0, 3, 1, 4, 2), with u = 1, d = 2, p = 0, g = 4,
  j = 0, z = 5;
- Y has receivers {0, 1, 2, 4}; nobody wants Y_p, and u values Y_p at 0;
- X_A gives u {Y_p, z}, worth 4 to it, while p's bundle holds Y_u, worth 23 to u.

**Fix:** state "Y has exactly one receiver u" in RF-T's setting, or in ORD and RF-T-A. It holds at every exported
n = 5 failing start, so the n = 5 uses stand.

*Not checked:*
- girth's own counts (454 settings, 24/25 sub-case trades);
- Conjecture RF-T-HARD (evidence; my sample is counterfactual too).
