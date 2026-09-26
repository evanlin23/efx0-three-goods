# Potentials that start with (r, Λ) fail on big-top frozen agents (f = 1)

Workstream `proof/k4-c4min-f1` (`k4/c4min_f1.md` §3). The approach: at f = 1, take a configuration that maximizes
Ψ = (#robust agents, Σ levels), possibly with a tie-break, and show it has a valid owner.

Theorem F1 does this when the frozen agent is not big-top. The approach cannot be completed for big-top frozen agents.
On the profile below, **no** maximum of Ψ is completable, so no tie-break can help. This applies to (r, Λ, −t),
(r, Λ, −t, −p) and every other potential whose first two components are r and Λ. Some other configuration of the same
profile is completable, so C₄ᵐⁱⁿ itself holds there.

**Smallest failing configuration.** n = 3, m = 8, core 46 of `results/k4_certs_3.json.gz`, all three agents big-top
with top 6:
- agent 0: 0:3, 2:6, 6:10, 7:2;
- agent 1: 1:3, 4:4, 6:8, 7:2;
- agent 2: 3:3, 5:4, 6:8, 7:2.

The fewest frozen agents is 1 and ω = 3. There are 76 configurations, and 52 of them are completable. The three
Ψ-maxima (Ψ = (2, 19)) are the same up to symmetry. One agent is frozen on 6, the other two hold their two best goods,
and the pool is the frozen agent's other three goods (e.g. agent 2 frozen, pairs {0, 2} and {1, 4}, pool {3, 5, 7}).
Every owner's bundle then contains all three of those goods and threatens the frozen agent (`k4/c4min_f1.md`
Lemma 8(a)). The two free agents both need 6, so the unfreezing clause does not apply.

The maxima of Φ′ = (−t, r, Λ, −p) (`k4/c4min.md` §4) are all completable. In each of them one free agent keeps good 7,
the least good of every agent, in its pair, and so protects the frozen agent. For example, agent 1 holds {4, 7} instead
of {1, 4}; this costs it one level, which Ψ counts against it.

The minimum is n = 3: every strict profile with n = 2 has a completable Ψ-maximum (`results/k4_c4min_f1_n3.log`,
first FILE line: starfail 0). Among the n = 3 profiles, 128 of the 7,284,544 with f = 1 fail, all on core 46 (the same
log). The samples with n = 4 and 5 (`results/k4_c4min_f1_samples.log`) have a few more.

**Reproduce.** `python3 attempts/k4_c4min_f1_bigtop.py` (under a second). It replays the profile with both implementations:
- the independent Python one (`k4/c4min_cfg.py`) lists the maxima of Ψ, (r, Λ, −t), (r, Λ, −t, −p) and Φ′;
- `k4/c4min_f1.c` reports starfail 1, rltfail 1, phi1fail 0.

It ends with CONFIRMED.

## Protecting only big-top frozen agents: Φ_BT fails at n = 4

**The attempt.** Φ_BT = (−t, r, Λ, −p), with t (frozen agent threatened by the pool alone) and p (pool goods it
values) counted only when the frozen agent is big-top. It agrees with Ψ on every other configuration, so Theorem F1
would stay inside it. It fixes the profile above: every maximum is completable on every strict profile with n ≤ 3,
core 46 included (`results/k4_c4min_f1_phibt.log`).

**Smallest failing configuration.** n = 4 (n = 3 has no failure), m = 11, core 210 of
`results/k4_certs_4_pure.json.gz`:
- agent 0: 0:5, 2:4, 8:2, 10:8;
- agent 1: 1:6, 5:3, 8:2, 10:10;
- agent 2: 3:6, 6:3, 9:2, 10:10;
- agent 3: 4:5, 7:4, 9:2, 10:8.

The fewest frozen agents is 1. There are 1,030 configurations, and 678 of them are completable.
- The two Φ_BT-maxima have a frozen agent that is not big-top and no valid owner. The frozen agent is agent 0 (values
  8, 5, 4, 2, with 8 < 5 + 4) or agent 3. Their path moves would make a big-top agent frozen without protection, which Φ_BT
  ranks lower.
- The two Ψ-maxima (big-top frozen agents 1 and 2) are completable, as are all eight Φ′-maxima, consistent with
  Theorem F1.

The pure n = 4 sample of `results/k4_c4min_f1_phibt.log` has 7 such profiles, and the n = 5 samples one more
(`results/k4_c4min_f1_samples.log`, counter phiBTfail). The same script replays it with both implementations.
