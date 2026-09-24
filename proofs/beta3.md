# Conjecture D for β = 3 (connected cores with m = 2n − 2)

Workstream `proof/beta3`, plan Step 3.2, ledger open item 7. Work in progress.

**Target.** Every connected core with n ≥ 2 agents and m = 2n − 2 goods (cyclomatic number β = 3) has an EFX₀
allocation in which at most one bundle has more than two goods.

**Route.** Extend `proofs/beta2.md`. By the counting identity (L4), a β = 3 core has π = n − 3 + Σ (deg g − 2)
P-agents, so at most three Q-agents. With Q-agents, use Lemma O (a Q-agent holds its top alone) and the collector
theorem D2.C with pins, as in β = 2 Cases 2–3, split by the kernel shapes of L11 (β = 3: kernels with ≤ 4 vertices).
Without Q-agents the multigraph K of shared goods has |E| = |V| + 2, two deficit units, while D2.C absorbs one; the
plan is to spend the second unit on a good held alone by a suitably chosen agent (a pin), or to find a second
mechanism, guided by the certified data (R3, R2 at n = 7, m = 12, R4 at n = 8, m = 14) and by construction LB
(open PR #9).

Deliverables: this proof; `src/beta3.py` (the proof as an algorithm) and `src/verify_beta3.py` (every β = 3 core and
profile for small n, raw EFX₀ check, certificates for `tools/check_certs.py`); ledger rows with artifacts.
