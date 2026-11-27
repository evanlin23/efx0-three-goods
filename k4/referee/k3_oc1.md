# Referee report: Theorem R1C and Lemmas 1–3 (branch `claude/k4-k3-oc1`, `k4/k3_oc1.md` §2–§3)

Referee: `proof/k4-referee`, 2026-11-26. Read: `k4/k3_oc1.md` at `949718a` (all of it; §2–§3 unchanged at `253749e`), `k4/sdc.md` §29 (OC₁),
`proofs/lb_last_step.md` §0–§5 (LB⁺), and `paper/k3-simple/long.tex` Definitions state/valid, Lemmas draft, stay,
ring, chain and Theorem soundness. Checks: `k4/referee/k3oc1_ref.py`, runs `k4/referee/k3oc1_ref_runs.sh` and
`k3oc1_ref_runs2.sh`, logs `results/k4_referee/k3oc1_ref.log` and `results/k4_referee/k3oc1_ref_bstar.log`. Written
from the texts; no code shared with `k4/k3oc1/`.

## Verdicts

| item | verdict |
|---|---|
| Lemma 1 (simple completion; soundness) | CORRECT |
| Lemma 2 (ω identity; DE trades never raise ω) | CORRECT |
| Lemma 3 (self-service) | **CORRECT WITH FIXES**: its first two sentences are false for a pair-holder owner (fix below); "every satisfied state passes Lemma 1" is true |
| Theorem R1C | **CORRECT**, with a scope statement to add: it is about DE's core case (every agent values exactly three goods, strictly balanced; dead goods allowed), not every 3-limited instance |
| Theorem B\* (newer, checked in passing) | CORRECT |

## 1. Lemma 1

(a) and (b) are LB⁺'s Lemma 1 with every cap equal to one, i.e. S = |T|. Theorem 1′ covers every completion
satisfying (OC) whose caps are at most LB⁺'s, because lowering caps only removes completions. If
|J| < |T| − [o ∈ T], then (a) already holds, so the C ⊇ H with |C| = S − cap(o) of Lemma 1's proof exists whenever it
is needed. (c) is the no-owner completion with LB⁺'s own cap 2 for the empty terminal o. All three give at most one
agent two or more junk goods. Checked on random valid DE states with pair holders (n = 3–5, 66,000 states;
(a) 35,406, (b) 129,846 owner tests, (c) 1,967): every completion built as in the lemma is EFX₀ by the raw
definition, and has one absorber.

## 2. Lemma 2

The counts are right: m = 2|U| + (n − |U| − e) + |J|, and n = |U| + ν + |T|, since in a valid state each wanted good
is the whole holding of exactly one frozen agent and each frozen agent holds exactly one wanted good. Subtracting
gives |J| − |T| = m − 2n + e + ν. A trade never empties a holding, so e does not grow. The proof of DE's Lemma stay
shows more than its statement: if i wants g in Y′ then i wanted g in Y. So the set of wanted goods shrinks, and ν
does not grow. Correct.

## 3. Lemma 3: a false first sentence, and the fix

As written: "If every exposed agent of an owner o is a terminal, (b) holds for o". This is false when o is a pair
holder. (b) has a first condition, "no x ∈ E_o with {b_x, c_x} ⊆ base(o)", and Lemma 3's proof never checks it. An
exposed terminal x may hold its top while its pair {b_x, c_x} is exactly o's pair.

**Smallest instance.** Two agents with the same ranking a ≻ b ≻ c, and one dead good d.
- x holds {a} and o holds {b, c} (U = {o}); J = {d}, T = {x}, E_o = {x}, and x is a terminal.
- (b) fails for o, and o really is no owner: X_o = {b, c, d} gives v_x(X_o ∖ {d}) = b + c > a = v_x(X_x).
- The state still completes by (a): x takes d.

On random valid DE states the literal sentence fails 4,006 times (n = 3: 3,039; n = 4: 838; n = 5: 129). Every
failure is this case: o ∈ U and an exposed pair equals base(o) (`lemma3_false_pair_in_owner`).

**Fix.** Add the hypothesis "no x ∈ E_o has {b_x, c_x} ⊆ base(o)", which is automatic for o ∈ T, or restrict Lemma 3
to terminal owners. The general form then holds: (b) holds for o when h(E_o ∩ F) ≤ |T ∖ E_o| − [o ∈ T]. The count is
|E_o ∩ T| + h(E_o ∩ F) ≤ |T| − [o ∈ T], and π_x ≠ ∅ for an exposed terminal once the pair condition holds. That form
never failed (128,377 hypothesis cases, 0 false). The "in particular" is true as stated: in a satisfied state every
agent outside U is a terminal, so a terminal owner works. If T = ∅, every pair-holder owner has E_o = ∅.

Where Lemma 3 is used (§6, B\*), the owners are terminals or have just received a pair no exposed agent shares (B\*
(iii)), so no later claim depends on the defect.

## 4. Theorem R1C

**The reduction.** R1C is LB⁺ (Theorems A, B, C, Lean-checked as `EFX.target`) run with every cap equal to one.
I re-checked each count against that.
- *Lemma 1, Theorem 1′.* Lowering caps keeps soundness (§1).
- *Theorem A.* S − cap(r) ≥ |E_r ∖ B\*| needs only that the τ(x), x ∈ E_r ∖ B\*, are distinct terminals other than r
  with cap ≥ 1. The extra terminal τ(k\*) in the second sub-case needs the same.
- *Theorem B (g).* Needs cap′ ≥ 1 for the τ(x) outside B\*, which (d) provides, and cap′(k) = 0.
- *Output.* Every terminal but the owner receives at most one junk good. An upgraded agent's c_u is its one junk
  good. So the completion has one absorber.

**R1-compatibility.** Every linear extension of the need order gives the same picks (induction on the order: the
goods an agent prefers are taken by earlier agents, and its pick is free). Conversely, an order with the same picks is
a linear extension. So "R1-compatible" means: some order with the same draft is an LB⁺ Phase 1 run, and LB⁺'s block
facts (B1), (B2), (A3) apply to it.

**OC₁'s chain versus LB⁺'s rotation.** OC₁ (`k4/sdc.md` §29) applies its chain to the picks, while LB⁺ rotates
after the upgrades. They agree. No upgraded agent is on the need chain ((A4): x_{i+1} ∉ U, and k\* ∉ U). And
H₀ = {b_k, c_k} ⊆ J_after-upgrades ∪ {Y_r} ⊆ J_picks ∪ B_r. The gains are strict: b + c > a, and each x_i receives a
good it ranks strictly above its own. At k = 3 that needs strict values within an agent, which §1 assumes.

**Scope (to state wherever R1C is cited).** The setting is DE's core case: every agent values exactly three goods
a > b > c with a < b + c, and dead goods are allowed. Agents with fewer goods, and top-heavy agents, are outside it.
The attack log's "OC₁ at k = 3 for every R1-compatible order" should carry this restriction. OC₁ as literally stated
in `k4/sdc.md` §29 ranges over all instances, and that form is already refuted at k = 4 on non-cores (attack log,
21:50 and 21:55).

**Computation** (evidence). For every order of each instance:
- the draft is computed, and R1-compatibility is decided over all orders with the same picks;
- for every R1-compatible order σ, LB⁺ runs with unit caps: upgrades, owner r, otherwise an assertion of Theorem A's
  bad case and the rotation along every need chain from k\* to r;
- the completion of Lemma 1 is built and checked by the raw EFX₀ definition, for completeness, and for one absorber
  relative to the bases after the chain;
- independently, OC₁ is checked by brute force: a one-absorber completion of the picks, or one after some improving
  chain of §29, any chain.

| set | distinct drafts | R1-compatible | LB⁺ runs | rotations | failures | bad-case violations | OC₁: one chain / fail |
|---|---|---|---|---|---|---|---|
| exhaustive n = 3, m = 4 | 1,224 | 1,200 | 2,808 | 0 | 0 | 0 | 0 / 0 |
| exhaustive n = 3, m = 5 | 6,588 | 6,372 | 16,416 | 756 | 0 | 0 | 972 / 0 |
| exhaustive n = 3, m = 6 | 23,840 | 22,976 | 64,800 | 2,556 | 0 | 0 | 2,880 / 0 |
| random n = 4, m = 5–8 | 58,360 | 53,769 | 247,973 | 4,746 | 0 | 0 | 3,830 / 0 |
| random n = 5, m = 6–9 | 25,054 | 22,141 | 198,790 | 1,508 | 0 | 0 | 872 / 0 |
| random n = 5, m = 7–10 | 12,038 | 10,308 | 105,576 | 827 | 0 | 0 | 702 / 0 |
| random n = 6, m = 7–10 | 3,712 | 3,147 | 62,920 | 388 | 0 | 0 | 78 / 0 |
| random n = 6, m = 8–12 (no OC₁ brute force) | 1,797 | 1,442 | 35,432 | 97 | 0 | 0 | – |

("Exhaustive n = 3": agent 0 ranks 0 ≻ 1 ≻ 2, the others every ordered triple.) The rotation is needed: on 4,540
drafts the picks have no one-absorber completion at all, and LB⁺'s rotation repairs each R1-compatible one.

## 5. Theorem B\* (in passing)

Re-derived from `proofs/lb_last_step.md` §5 with r replaced by a terminal t.
- (a)–(c) use only {b_k, c_k} ⊆ W = J ∪ {Y_t}, Y_t ∉ NA (t is a terminal), and the need chain.
- (d′): a terminal other than t is off the chain (x₀, …, x_{s−1} are frozen) and keeps its pick, which is not in
  NA′ ⊆ NA.
- (e): an off-chain x ∈ E′_k is in E_t. A middle agent's old pick sits with its successor. For t itself:
  - b_t is another agent's pick if Y_t ∈ {none, c_t};
  - (UT) gives c_t ∉ J if Y_t = b_t.
- (f) is hypothesis (iii).
- (g): hypothesis (iv)'s hitting set lies inside W ∖ {b_k, c_k} = J′ and has ≤ |T| − 1 ≤ |T′| goods.

No block fact is used, so B\* holds for every order. Computation: on 78,379 drafts of random instances (n = 4–6),
B\* applies to 7,260, and all 9,986 rotations (every need chain) give an EFX₀ one-absorber completion. 0 failures.

## 6. For the coordinator

- Lemmas 1, 2, Theorems R1C and B\*: CORRECT. They can be recorded as PROVED for the core case at k = 3, with the
  scope line of §4.
- Lemma 3: CORRECT WITH FIXES. Add "no exposed pair lies in base(o)" (automatic for terminal owners). Nothing
  downstream is affected.
- R1C covers 4,608 of the 18,569 hard starts in the session's logs, so the open part of OC₁ at k = 3 is the non-R1-
  compatible drafts (§6 of the session's file). OT remains a conjecture.

## Addendum: Lemmas MAX₃ and RED₃ (`k4/k3_oc1.md` §11 at `974853c`; coordinator's queue, 2026-11-27)

Check: `k4/referee/red3_ref.py`, log `results/k4_referee/red3_ref.log`. Own code, raw EFX₀.

**Verdict: CORRECT** (both).

- **MAX₃** is Lemma MAX at k = 3, refereed CORRECT in `maxsd.md`.
  - A pickless agent found every junk good free at its turn and took nothing, so it values none.
  - An agent of S valuing a junk good would close an augmenting path.
  - (i): a valued good is a pick, and its holder is reachable. (ii) and (iii) follow.
- **RED₃.**
  1. At t's turn, the free goods of I′ are exactly the free goods of I that lie in I′, since S's picks are not goods
     of I′. So Y_t is still t's favourite, and U are null in I′ by (i).
  2. Values and junk agree on I′'s goods, so I′'s official moves are moves of I.
  3. Give S their picks as singletons. Singletons are never strongly envied. U ∪ S value nothing in T ∪ U bundles,
     by (i). T agents see T ∪ U bundles with the same values. The absorber count is unchanged.
  - Y′ is a perfect start of I′, so OC₁ at Y follows from OC₁ at Y′.
  - The argument never uses |R_i| ≤ 3; it is Lemma RED of `k4/sdc.md` §31 in DE's notation.

**Computation (evidence).** Non-perfect maximum-matching SD starts (some agent pickless) of random instances.

| class | starts | MAX₃ (no junk for U ∪ S; S closed) | RED₃ 1 (restricted SD) | RED₃ 2 (moves of I′ ⊆ moves of I) | RED₃ 3 (completions lift) | failures |
|---|---|---|---|---|---|---|
| ≤ 3 goods per agent | 38,678 | 38,678 | 38,678 | 16,794 moves | 1,746,427 | 0 |
| ≤ 4 goods per agent | 10,768 | 10,768 | 10,768 | 4,748 moves | 127,354 | 0 |

## Addendum: Lemma RF-A1\* and Lemma NA (`k4/k3_oc1.md` §13.5 at `17777f1e`; coordinator's queue, 2026-11-27)

**Read:** §13.5 line by line. Also Hall's Lemma RF-A1 (`k4/oc1_hall.md` §24.6) and Hall's second reading (§24.13),
both on `claude/k4-oc1-hall`; I compared them with mine only after writing mine.
**Check:** `k4/referee/rfa1s_ref.py` (`rfa1s_ref_runs.sh`), logs `results/k4_referee/rfa1s_ref_*.log`. The code is my
own, with raw EFX₀. Nothing from `k4/k3_oc1/`, `rf/` or `k4/oc1_hall/` is run.

### Verdict: RF-A1\* CORRECT; Lemma NA CORRECT. All n = 5 counts are confirmed.

**RF-A1\*, re-derived.** The setting:
- Y′ = SD(u, σ − u) is perfect, U′ = {d} and D_T′ = ∅;
- the path is u → w → d with Y′_u = Y_w, Y′_w = Y_d, Y′_d = g ∈ J, and J′ = (J ∖ {g}) ∪ {Y_u};
- W = {Y_d} ∪ (J′ ∖ {h}), X_w = W, X_d = {g, h}, and everyone else keeps its pick.

Here h ∈ J ∖ {g} ⊆ J′ by (A1-i), and Y_u ∈ J′ ∖ {h} ⊆ W, since Y_u is a pick of Y and h is not. Only w receives two or
more free goods, so X is a one-absorber completion of the picks.

Each step of the proof:
- *Junk below picks.* Every good of J′ was free at every agent's turn in σ′, so v_i(j) ≤ p′_i. (I2) suffices here;
  strictness is not needed.
- *X_d against i ≠ d.* v_i(X_d ∖ x) is one good's value.
  - g = Y′_d: unwanted, since d is a receiver.
  - h: junk at Y′.
  - Both are ≤ p′_i ≤ v_i(X_i), including for i = w, whose bundle contains Y′_w. Correct.
- *d against W.* J′ ∩ R_d = {h} gives W ∩ R_d = {Y_d}, so v_d(W) − min ≤ v_d(Y_d) < v_d(g) + v_d(h) = v_d(X_d) by
  (A1-i). Correct.
- *u against W.* By (A1-ii), v_u(W) − min ≤ v_u(Y_d) + v_u(Y_u) < v_u(Y_w) = v_u(X_u). Correct.
- *k2 against W (k2 ∉ {w, u, d}).* g, h and Y′_{k2} are three distinct goods of R_{k2}, none in W: g is d's pick,
  h ∉ W, and Y′_{k2} ≠ Y_d since k2 ≠ w. **With |R_{k2}| ≤ 4**, at most one good x of W is valued, and v(x) ≤ p′_{k2},
  as x is junk at Y′ or x = Y_d with (A1-iii). Correct. This is the proof's only use of k ≤ 4.
- *Frozen q ∉ {w, u, k2} valuing Y_d.* This is (A1-iv\*) verbatim.
- *Frozen q not valuing Y_d.* v_q(Y_d) = 0, so the minimum over W is 0, and v_q(W) − min = v_q(J′ ∖ {h}). q is frozen
  and D_T′ = ∅, so J′ does not threaten q: v_q(J′ ∖ h′) ≤ p′_q for every h′ ∈ J′, in particular h′ = h. Correct. The
  detour "if q values no junk, 0; otherwise q is dangerous" is harmless but unnecessary.
- *No other agent.* U′ = {d}, so every agent other than d is frozen. Correct; this is where U′ = {d} is used.

So the hypotheses used are: perfect SD at Y′, U′ = {d}, D_T′ = ∅, k ≤ 4 (for k2), and (A1-i)–(A1-iv\*). Of (A1-i), only
J′ ∩ R_d = {h} and v_d(g) + v_d(h) > v_d(Y_d) are used. Of (A1-ii), only the bound v_u(W) < v_u(Y_w). This matches
Hall's second reading.

**Lemma NA, re-derived.** Bundles have at most two goods. Against {Y′_a, j}, the conditions are v_i(j) ≤ v_i(X_i),
which always holds since j was free at i's turn, and v_i(Y′_a) ≤ v_i(X_i). The latter is automatic unless i wants
Y′_a. Necessity: if i wants Y′_a and v_i(X_i) < v_i(Y′_a), removing j from X_a violates EFX₀. So the "iff" is
correct.

**n = 5 data** (`rfa1s_ref.py n5`, `rfa1s_ref_n5.log`). My rebuild from the certifier's two n = 5 exports gives the
113,484 DEMOTE-0 starts (|J′| = 3 at all of them).

| quantity | mine | k3-oc1 / Hall |
|---|---|---|
| complete at the picks (one absorber) / need a move | 113,210 / 274 | 113,210 / 274 |
| path u → w → d with d taking junk of Y | 110,661 | 110,661 |
| … d values no good of J′ | 242 | 242 |
| (A1-i)–(A1-iv\*) hold | **71,443**: 32,368 with (A1-iv), 39,075 only with (A1-iv\*) | 71,443 = 32,368 + 39,075 |
| X raw EFX₀ | 71,443, exactly where the hypotheses hold | same |
| X not EFX₀ | 38,976, all with only (A1-iv\*) failing | 38,976 |
| \|D_T(Y)\| = 2 and d truly dangerous at Y (at the 71,443) | 71,443 | all |
| (A1-iv) failures | 39,075, all on 5_pure#464: q holds its top at Y′, values Y_u and exactly one junk good of Y | same description |
| NA criterion vs raw EFX₀, every injection J′ → agents | 6,809,040 assignments, 0 disagreements | 6,809,040, 0 |
| no-absorber completion exists | at all 113,210 at-once starts, at none of the 274 | same |

On this path shape the hypotheses are exact: X is EFX₀ if and only if (A1-i)–(A1-iv\*) hold.

**Any n, random** (`rfa1s_ref.py gen`). The proof uses only Y′-facts, so I tested RF-A1\*'s claim in Y′ terms: Y′
perfect, U′ = {d}, D_T′ = ∅, h the only junk good d values, v_d(Y′_d) + v_d(h) > v_d(Y′_w), a u as in (A1-ii), a k2
as in (A1-iii), and (A1-iv\*). The instances are random strict instances, n = 3–5, all orders, 400,000 per run.

| run | full hypotheses | without (A1-iv\*) | without D_T′ = ∅ | without U′ = {d} |
|---|---|---|---|---|
| k ≤ 4 | **758 cases, 0 failures** | 123 of 881 fail | 15 of 826 fail | 8,114 of 47,252 fail |
| k ≤ 5 | 23 of 8,526 fail | 3,458 of 11,961 fail | 536 of 10,268 fail | 60,321 of 273,962 fail |

At k ≤ 5 every full-hypothesis failure is a k2 candidate with |R_{k2}| = 5 that values two goods of W, which is exactly
the step that needs |R_{k2}| ≤ 4 (`rfa1s_ref_gen_k5.log`). So each hypothesis is used, and k ≤ 4 is used where the
proof says. A direct random generator of RF starts with this path shape (`rfa1s_ref.py rand`) hits the setting too
rarely to add much; its log is kept.

*For the record:* RF-A1\* implies Hall's RF-A1, because (A1-iv) makes (A1-iv\*) vacuous. And at n = 5, Lemma NA alone
covers DEMOTE-0's at-once part.
