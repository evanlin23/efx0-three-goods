# Paper: EFX₀ with at most three relevant goods (k = 3)

A research paper (CS 580 course project report, Fall 2026) on the k = 3 result of this repository: TARGET, conjecture D, construction LB⁺, the algorithm K3ALG and the Lean formalization. It is written in Springer's LLNCS format, 11pt, with at most 8 pages of body before the references and the rest in the appendix.

- `main.tex`: the paper; `refs.bib`: the bibliography; `main.pdf`: the built paper.
- `llncs.cls` (v2.26, 2025-02-25) and `splncs04.bst`: copied unmodified from Springer's LLNCS package on CTAN, https://mirrors.ctan.org/macros/latex/contrib/llncs.zip (the class that the Overleaf template "Springer Lecture Notes in Computer Science" uses).

Build (pdflatex and bibtex; the fonts are Latin Modern, `lmodern`, so the PDF has only Type 1 fonts):

    pdflatex main && bibtex main && pdflatex main && pdflatex main

Every claim in the paper is taken from `LEDGER.md` and the files it cites (`proofs/`, `lean/`, `results/`); the paper changes no ledger status.
