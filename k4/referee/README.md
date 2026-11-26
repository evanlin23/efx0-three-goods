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
| 4 | Lemma 2 / 2*, Corollary 2.1, Theorem F1_1 | `claude/k4-oc1-hall` | `oc1_hall.md` | in progress |
| 5 | CH-A, CH-B (charity) | `claude/kgen-charity` | `charity.md` | pending |
| 6 | PW5 (OC₁ fails at k = 5) | `claude/k4-ksens` | `ksens.md` | pending |
| 7 | Lemmas D, F, S, U, BOTH-TP, Corollary TP | `claude/k4-sd-induct` | `sd_induct.md` | pending |
