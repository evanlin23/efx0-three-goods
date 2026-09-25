# k = 4: structure of a minimal counterexample (work in progress)

Workstream `proof/k4-mincex`. The minimal-counterexample route of `proofs/min_counterexample.md` (rows MC1–MC6),
carried to TARGET₄ (every agent has at most four relevant goods; plain EFX₀ existence). Ledger rows `K4.MC*`.

Plan:
1. K4.MC1: the soundness of local reductions (Lemma M1, M1(b)) at k = 4.
2. Local reductions for k = 4 configurations (two thread agents sharing a good of degree 2, agents with two private
   goods, ...), certified by `k4/reduce4.py` and re-checked by an independent checker, with a sensitivity test.
3. Structural bounds on a minimal counterexample (n in terms of β), and the finitely many shapes left for small β.
4. The shapes left, against the certified data (`results/k4_certs_*.json.gz`).
