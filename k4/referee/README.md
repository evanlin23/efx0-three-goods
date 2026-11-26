# Independent referee reports (workstream proof/k4-referee)

Branch `claude/k4-referee`. Each item of the k = 4 campaign (`k4/attack_log.md`) that claims a proof gets one report
here, `k4/referee/<item>.md`, with its checks under `results/k4_referee/`. The checks are written from the raw EFX
and EFX₀ definitions and share no code with the sessions' scripts.

EFX₀ (raw): for all i ≠ j and every g ∈ X_j, v_i(X_i) ≥ v_i(X_j ∖ {g}), including goods with v_i(g) = 0.
Ordinary EFX: the same, only for g with v_i(g) > 0.

Verdicts: CORRECT / CORRECT WITH FIXES / GAP / WRONG.

| # | item | branch | report | verdict |
|---|---|---|---|---|
| 1 | Theorem VM (reconstructed Viswanathan–Mehta, ordinary EFX) | `claude/k4-vm` | `vm.md` | **CORRECT** (ordinary EFX only; for the §2 reconstruction with G1) |
| 2 | Theorem R1C, Lemmas 1–3 (OC₁ at k = 3) | `claude/k4-k3-oc1` | `k3_oc1.md` | R1C, Lemmas 1, 2, B\* **CORRECT** (core case k = 3); Lemma 3 **CORRECT WITH FIXES** |
| 3 | Theorem T1, Lemmas SINK, PARK, SLACK | `claude/k4-girth` | `girth.md` | **CORRECT** (PARK: state N ≠ ∅; F2 is additive-only) |
| 4 | Lemma 2 / 2*, Corollary 2.1, Theorem F1_1 | `claude/k4-oc1-hall` | `oc1_hall.md` | **CORRECT** (Cor. 2.1 gloss: "demand" = threatening set) |
| 5 | CH-A, CH-B (charity) | `claude/kgen-charity` | `charity.md` | **CORRECT** |
| 6 | PW5 (OC₁ fails at k = 5) | `claude/k4-ksens` | `ksens.md` | **CORRECT** (t = 0 aside incomplete, not needed) |
| 7 | Lemmas D, F, S, U, BOTH-TP, Corollary TP | `claude/k4-sd-induct` | `sd_induct.md` | D, F, S, TP, BOTH-TP **CORRECT**; U **CORRECT WITH FIXES** (needs "f unfrozen") |

**Checked in passing** (newer PROVED items seen at the 22:15 UTC heads; short checks, recorded as addenda in the
reports):
- `vm.md`: Lemmas P0, P1′ and Proposition HDT, CORRECT (P1′'s "exactly when" needs strict values);
- `oc1_hall.md`: Lemma MAX, CORRECT;
- `girth.md`: generalized Lemma SLACK and Proposition HT for H_t, CORRECT (HH_t not rebuilt);
- `charity.md`: Proposition DU, CORRECT;
- `sd_induct.md`: Lemma H, Proposition PR-step and Theorem PR-TP, CORRECT (definition of PR should say EFX₀).

**Commits read**: vm `7a78df6`, k3-oc1 `949718a`, girth `5b79844` (+ `90c116f` for the addendum), oc1-hall `476207e`
(+ `e2b4701`), charity `78deef1` (+ `8862555`), ksens `ceba5c7`, sd-induct `d244b6a`. At the 22:15 heads the refereed
sections are unchanged except Lemma SLACK (generalized; re-checked).
