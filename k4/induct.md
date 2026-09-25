# k = 4: induction on the number of 4-good agents (insertion lemma)

Workstream `proof/k4-induct`. Ledger rows `K4.IND.*` (CONJECTURE / EVIDENCE only). Work in progress.

**The avenue.** Induct on j = the number of agents with 4 relevant goods. Base j = 0 is TARGET (k = 3, proved and
machine-checked). Step j → j + 1: pick a 4-good agent w and a good d ∈ R_w; I − d has j four-good agents, so it has an
EFX₀ allocation X′; an *insertion lemma* would build an EFX₀ allocation of I from X′ by placing d and a bounded repair.

Sections (to be filled): 1. Statements tested; 2. Computational results; 3. Proofs of special cases; 4. The gap.

## Tools
- `k4/induct.c`: every EFX₀ allocation X′ of I − d (or I − w, I − w − d), and the exact repair distance r(X′) = the
  fewest goods (other than d) that change owner to reach an EFX₀ allocation of I (raw definition).
- `k4/induct_run.py`: driver over certified cores (`results/k4_certs_*.json.gz`) and random strict profiles.
