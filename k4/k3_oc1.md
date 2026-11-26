# One chain suffices at k = 3 (OC₁ at k = 3), and lifting it to k = 4

Workstream `proof/k4-k3-oc1`. Code: `k4/k3oc1/`; logs: `results/k4_k3oc1/`. Notation: `paper/k3-simple` (Draft and
Exchange, DE) and `k4/sdc.md` §29 (Conjecture OC₁). Everything called evidence is evidence only (PROMPT.md §5 rule 3).

## Status (burst 1, in progress)
- **Computed (exact, ordinal model).** OC₁ at k = 3 holds for every connected core with n ≤ 4
  (`results/certs_small_m.json.gz`), every ranking profile, every order: 1,244,160 starts at n = 4, none needs more
  than one chain (`oc1_small4.log`). On all 5,296 hard starts some single DE trade (DE chain or DE ring) repairs.
- **Next.** n = 5 exhaustive (running); the proof.
