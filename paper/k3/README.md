# Paper: EFX₀ with at most three relevant goods (k = 3)

A research paper (CS 580 course project report, Fall 2026) on the k = 3 result of this repository: TARGET, conjecture D, construction LB⁺, the algorithm K3ALG and the Lean formalization. It is written in Springer's LLNCS format, 11pt, in two versions that share the bibliography and the class files.

- `main.tex` → `main.pdf`: the submission, with at most 8 pages of body before the references and the rest in the appendix.
- `long.tex` → `long.pdf`: the long, readable version, with no page limit. It explains the approach informally before any definition (with a pipeline figure), introduces the notions of the algorithm one at a time, gives the pseudocode, traces two examples step by step (one with the owner r, one with a rotation), and gives every proof of the main theorems in full in the body. Same class and options (`\documentclass[runningheads,11pt]{llncs}`), no layout changes; figures are drawn with TikZ (`pgf`), the pseudocode with `algorithm` and `algpseudocode`.
- `refs.bib`: the bibliography of both.
- `llncs.cls` (v2.26, 2025-02-25) and `splncs04.bst`: copied unmodified from Springer's LLNCS package on CTAN, https://mirrors.ctan.org/macros/latex/contrib/llncs.zip (the class that the Overleaf template "Springer Lecture Notes in Computer Science" uses).
- `examples/`: verification of the examples of `long.tex` (see its Appendix D).
  - `trace.py` recomputes every intermediate state of Examples 2 and 3 with the repository's literal transcription of the Lean program (`k3/k3algo.py`, `mirror`), compares the outputs with `mirror` and `fast`, checks them against the EFX₀ definition by brute force, and checks the side claims of the text (the EFX-but-not-EFX₀ allocations, the failing completions with owner r, the cases of the safety lemma (ledger L5), the repeated good in `HitSet`, ω = m − 2n + |NA|). Run from the repository root: `python3 paper/k3/examples/trace.py` (output: `trace_output.txt`; exit status 0 iff every check passes).
  - `lean_examples.lean` evaluates the Lean program `EFX.K3.algo` on the same instances (`#eval`) and checks the outputs of Examples 2 and 3 by `decide`. It is not part of the library. Run from `lean/` after `lake build`: `lake env lean ../paper/k3/examples/lean_examples.lean` (output: `lean_examples_output.txt`).

Build (pdflatex and bibtex; TeX Live with `texlive-pictures` and `texlive-science` for `long.tex`; the fonts are Latin Modern, `lmodern`, so the PDFs have only Type 1 fonts):

    pdflatex main && bibtex main && pdflatex main && pdflatex main
    pdflatex long && bibtex long && pdflatex long && pdflatex long

Every claim in the papers is taken from `LEDGER.md` and the files it cites (`proofs/`, `lean/`, `results/`), or from the verification runs in `examples/`; the papers change no ledger status.
