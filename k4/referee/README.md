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
| 8 | K4.SDC.MAXSD and Lemma SDPO (`k4/sdc.md` §28, §31); Lemma MAX (`k4/oc1_hall.md` §19) | coordinator, `claude/k4-oc1-hall` | `maxsd.md` | **CORRECT** (SDPO needs strict values; MAXSD also holds with tie-breaking) |
| 9 | Proposition CH-F (W(3, 1), W(4, 1) false); Proposition DU | `claude/kgen-charity` | `chf.md`, `charity.md` §5 | **CORRECT** (independent exact check, no SAT/MILP) |
| 10 | Lemmas SND, TERM; VM1 invariant (I1)–(I5) (`k4/vm.md` §7, §7.3) | `claude/k4-vm` | `vm.md` §6 | **CORRECT** ((I3) is about allocated goods) |
| 11 | Lemma PL, Lemma PWk(a) (`k4/ksens.md`, `7ec7073`) | `claude/k4-ksens` | `ksens.md` §5 | PL **CORRECT**; PWk(a) **CORRECT WITH FIXES** (the proof's W = 1 completion needs the clean values; fix given) |
| 12 | Lemma T5 (`k4/ttc.md` §13) | `claude/k4-ttc` | `ttc_t5.md` | **CORRECT**, the same as Lemma MAX |
| 13 | Theorem CH-KD, Corollary CH-KD′ (`kgen/charity.md` §8, `1e986c6`/`0c85d91`) | `claude/kgen-charity` | `chkd.md` | **CORRECT** (n-independent: (k − 2)d − 1 and p! ≤ d^{p−1}) |
| 14 | Theorem 2 (two-agent OC₁, t ≥ 0, every k), Fact L, Lemma M, Tops Lemma (`kgen/n3.md` §9, `418f876`) | `claude/kgen-n3` | `kgen_n3.md` | **CORRECT** (cite Plaut–Roughgarden Thm 4.3 for bare existence) |
| 15 | Lemma M (matching form, deficiency δ\*), Lemma EX (exchange criterion) (`k4/matching.md` §1, §3, `2c0198e`) | `proof/k4-matching` | `matching.md` | **CORRECT** (EX: Ext may include unfrozen chain agents); §2 refutation of "δ ≤ 1" confirmed |
| – | Literature: EFX₀ for n = 2 | – | `lit_n2.md` | Plaut–Roughgarden Thm 4.3 (EFX₀, monotone) covers existence; not `kgen/n3.md` Theorem 2 (picks kept / one chain) |

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
