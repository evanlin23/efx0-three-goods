# Paper: a short proof of EFX₀ with at most three relevant goods (k = 3)

A research paper on the k = 3 result of this repository, with the short proof found on branch `proof/k3-simplify`:
every instance with nonnegative additive valuations in which each agent positively values at most three goods has a
complete EFX₀ allocation, in which all bundles but at most one have at most two goods, and algorithm Draft and Exchange
(DE) computes one in polynomial time, with at most 4n exchanges. The proof replaces construction LB⁺ of `paper/k3/`
(blocks, leaders, Theorems A and B, the rotation) by the Improvement Lemma: a valid state in which no free agent can
absorb the leftover goods is Pareto-dominated by a valid state, through a need cycle, a pair chain or an exchange
cycle. It is written in Springer's LLNCS format, 11pt, in two versions that share the bibliography and the class
files.

- `main.tex` → `main.pdf`: the submission, at most 8 pages of body before the references, with the full proof of the
  Improvement Lemma in the body and the other proofs (preliminaries, soundness, short moves, limits of the shape), the
  evidence and the related-work table in the appendix.
- `long.tex` → `long.pdf`: the long, readable version: an informal overview, preliminaries (threats, safety,
  peeling), states and soundness, the Improvement Lemma with every proof, DE with pseudocode, its correctness and
  running time, a worked example with a TikZ figure of the exchange cycle, how large an exchange must be, the limits
  of the shape, the verification status and the evidence, and open problems.
- `refs.bib`: the bibliography of both; the entries of `paper/k3/refs.bib` plus `LinK3` (the previous paper,
  `paper/k3/`) and `RepoS` (branch `proof/k3-simplify`, commit `bdff404`, which holds the notes, tests, referee report
  and Lean files).
- `llncs.cls` and `splncs04.bst`: copied unmodified from `paper/k3/` (Springer's LLNCS package).
- `examples/check_examples.py`: recomputes every example and number of the papers with an independent implementation
  of the definitions and of DE, written from the paper, and cross-checks with `k3/simplify/po/hall/hall.py`: the
  EFX/EFX₀ example; the n = 6 instance (draft state, failed absorbers, all 10 completions failing, no short move, the
  4 dominating valid states, DE's representatives, exchange cycle and completion, raw EFX₀ check, also for 2,000 random
  valuations); the n = 2 example; the n = 6, m = 8 instance; the ring family for k ≤ 4; the limits of the shape by
  listing every allocation; the first rows of the hall evidence table; and DE, peeling included, on 40,000 random
  instances. Run from the repository root: `python3 paper/k3-simple/examples/check_examples.py` (one process, about
  10 s; output copied to `examples/check_output.txt`; exit status 0 iff every check passes).

Build (pdflatex and bibtex; TeX Live with `texlive-pictures` and `texlive-science`; fonts are Latin Modern):

    pdflatex main && bibtex main && pdflatex main && pdflatex main
    pdflatex long && bibtex long && pdflatex long && pdflatex long

Status of the claims, as the papers state it. Existence, and the shape for agents that value exactly three goods and
are balanced, were machine-checked in Lean in the previous work (`lean/`, `paper/k3/`), with the old proof. The new
proof (the Improvement Lemma, soundness in the form used, DE with at most 4n exchanges, and the shape for all
instances with at most three relevant goods per agent) is a written proof that is also machine-checked in Lean, over
the natural numbers (`lean/EFX/K3DE.lean`, `K3DEImprove.lean`, `K3DEAlgo.lean`, `K3DEExamples.lean`; ledger row
K3S.PO.LEAN); the running time and real values are not formalized, and the formal statements were written by the
same AI assistant and have not been reviewed independently. The written proof was derived independently twice
(`k3/simplify/po/hall/NOTES.md`, `k3/simplify/po/potential/NOTES.md`), refereed once with no error
(`k3/simplify/po/referee/README.md`; its four presentation fixes are applied), and checked by computer on millions of
states. The provers and the referee were AI agents: separate sessions of the coding assistant (Claude Code), the
referee given only the written proof. There has been no human peer review. The papers themselves were proofread by a
further AI referee session (no mathematical error; status and presentation fixes applied). Every claim is taken from
`LEDGER.md` (rows K3S.PO, K3S.PO.LEAN, K3S.SA, K3S.ST) and the notes it cites, or from the runs of
`examples/check_examples.py`; the papers change no ledger status.
