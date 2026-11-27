# The release bound (R) fails at n = 7: one rotation cannot always remove the need for an owner

Workstream `proof/k4-k3-oc1` (`k4/k3_oc1.md` §12.1). Setting: k = 3, a ledger core, a hard perfect draft in the gap
of Theorems R1C and B\*.

**The idea tried.** Prove Conjecture T-ω (every least-ω′ earliest-wanter rotation completes) by counting releases.
- By Lemma 5, a rotation gives ω′ = ω − r, where r is the number of goods it releases.
- **(R):** some valid Rule E rotation has ω′ ≤ 1.
- **(R′):** the same, measured by total rank deficit: W′ ≤ 2n − m + 1, which implies ω′ ≤ 1.

Then ω′ ≤ 0 completes with no owner, and ω′ = 1 leaves a small case (k's slot). Both forms hold on every gap draft
of every core with n ≤ 6: 106,368 drafts (`te_release_rules.log`, `te_wbound.log`).

**Counterexample** (n = 7, m = 12; a core of `results/certs_7_12.json.gz`; found by `k4/k3oc1/te_sample.py`):

| agent | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| a > b > c | 0 > 5 > 7 | 3 > 2 > 8 | 2 > 6 > 9 | 3 > 10 > 6 | 4 > 11 > 5 | 0 > 1 > 5 | 6 > 4 > 1 |

- **The draft.** Order (0, 3, 1, 2, 4, 6, 5) gives the picks (0, 2, 6, 3, 4, 5, 1) and J = {7, 8, 9, 10, 11}. The
  only terminal is 5, which holds its c. So ω = 4, and E_5 = {0, 4}.
- **The rotations.** The two valid Rule E rotations are (0, 5), a ring with the pair arrow 5 → 0, and (4, 6, 5). Each
  leaves ω′ = 2 after LB's upgrades, and so does every DE trade (`de_moves.de_trades`).
- **The completions.** Both rotations still complete, with the rotated agent as owner, which takes three junk goods:
  - ({5,7,8,9,10}, {2}, {6}, {3}, {4}, {0,11}, {1}) after (0, 5);
  - ({0}, {2}, {6}, {3}, {5,8,9,10,11}, {1,7}, {4}) after (4, 6, 5).

**Frequency** (`te_sample7_*d*.log`, `te_sample8_14d.log`, classified in `te_sample_d_classify.log`):
- n = 7: 6,445 hard drafts. (R) fails on 81, 5 of them in the gap.
- n = 8: 816 hard drafts. (R) fails on 33.
- (R′) fails somewhat more often.

T-ω, T′_k and T-E∃ hold on all of these drafts. In (P)'s class (§11) (R) already fails at n = 5.

**Consequence.** Releases alone cannot prove T-ω. The completion after the best rotation genuinely needs an owner
that absorbs several junk goods, B\*'s hitting count with |T′| for owner k or a terminal. A proof has to combine
Lemma 5 with that count, as B\* does.

Replay (no repository code, raw EFX₀ definition, values 10 > 8 > 7): `python3 attempts/k4_k3oc1_release_bound.py`.
