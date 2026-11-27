# Referee report: Lemma T6 and its certificate corollary (`k4/ttc.md` §14.2, branch `claude/k4-ttc`)

Referee: `proof/k4-referee`, 2026-11-27.
- Read: `k4/ttc.md` §14.2 (instance 0 in TTC terms, Lemma T6, Corollary, "All 11") at `71c7b83`.
- Check: `k4/referee/t6_ref.py`, log `results/k4_referee/t6_ref.log`. Own code, raw EFX₀. The counterexample data are
  the certifier's `results/k4_oc1max/oc1max_cex_n4.json` (branch `compute/k4-oc1max-cert`).

## Verdict: CORRECT

The setting: a perfect-matching SD start, one move (an addition, a chain or a ring, as in `de_free`), then *any*
completion that keeps the new bases.
- **(a) Value domination.** Movers strictly improve their bases, and completions only add goods. Correct.
- **(b) At most two foreign picks per bundle**, and **(c)** the two-pick shape:
  - a ring gives each member one foreign base and releases no pick;
  - an addition moves no base;
  - in a chain, every base holds at most one foreign pick (x_j holds Y_{x_{j−1}}; x₀ may hold Y_{x_t}), and the only
    pick that can reach the pool is Y_{x_t}.
  - So two foreign picks occur only for some x_j with j ≥ 1 that also receives Y_{x_t}. Then j ≠ t, since Y_{x_t} is
    foreign to i, and i's step gives v_i(Y_{x_{j−1}}) + v_i(H_j) > v_i(Y_i). Correct.
- **Corollary.** An EFX₀ allocation after one move lies in 𝒯 by (a). It avoids three foreign picks by (b). If the
  blocked agent i held two, (c) would give an improving step with one of them plus junk inside R_i, which the
  hypothesis forbids. Correct.

**The certificate on the 11 n = 4 counterexamples** (my brute force over all n^m allocations): every value-dominating
EFX₀ allocation has a blocked agent, in all 11, each time through a single agent.

| core | EFX₀ | dominating | blocked agent |
|---|---|---|---|
| 4_n4_3 #58 (instance 0) | 14 | 6 | 0 |
| 4_n4_3 #77 | 24 | 4 | 3 |
| 4_pure #20 / #21 / #23 / #24 / #26 / #29 / #36 / #38 / #45 | 18 / 21 / 19 / 20 / 19 / 24 / 18 / 62 / 54 | 6 / 5 / 4 / 6 / 4 / 4 / 6 / 16 / 15 | 2 / 2 / 1 / 0 / 0 / 3 / 0 / 0 / 0 |

Instance 0 matches the text exactly:
- the 6 targets are ({0,2,5},{1},{3,4},{6}), ({0,2,5},{1},{6},{3,4}), ({2,5},{0,1},{3,4},{6}),
  ({2,5},{0,1},{6},{3,4}), ({2,5},{1},{0,6},{3,4}) and ({2,5},{1},{3,4},{0,6});
- in each, agent 0 holds {g2, g5}, with 7 + 2 ≤ 10 and 4 + 2 ≤ 10, since J ∩ R₀ = {g0}.

This is a human-checkable refutation of OC^max (hence of OC₁^max) on these cores, given the list of targets. The
target list itself is a finite computation, which my code reproduces.

## Computation (evidence)

Random perfect SD starts (n = 3–5, ≤ 4 relevant goods), every move (additions, chains, rings), and every completion
keeping the new bases, EFX₀ or not.

| check | tests | failures |
|---|---|---|
| (a), (b), (c) | 141,215 (move, completion) pairs from 19,680 moves at 4,557 starts | 0 |
| corollary's hypothesis met at a random start | 0 starts (none occurred) | – |

The corollary's soundness rests on its proof, and on the 11, where my certifier check finds no free completion after
any one move (`k4/referee/oc1cert.md`).

## For the coordinator

- Lemma T6 and the corollary: CORRECT. They can be recorded as PROVED.
- The certificate is confirmed on all 11 n = 4 cores.
