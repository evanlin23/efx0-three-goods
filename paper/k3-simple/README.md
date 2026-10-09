# Paper: EFX₀ with at most three relevant goods per agent

The paper of this repository's k = 3 result: every instance with nonnegative additive valuations in which each agent
positively values at most three goods has a complete EFX₀ allocation, in which all bundles but at most one have at
most two goods, and algorithm Draft and Exchange (DE) computes one in time O(n(n + m)), with at most 4n exchanges. The
proof rests on the Improvement Lemma: a valid state in which no free agent can absorb the leftover goods is
Pareto-dominated by a valid state, through a need cycle, a pair chain or an exchange cycle. It is written in
Springer's LLNCS format, 11pt, in two versions that share the bibliography and the class files. This is the paper
intended for publication; the papers are self-contained and cite only this repository and published work.

- `main.tex` → `main.pdf`: the submission, at most 8 pages of body before the references, with the full proof of the
  Improvement Lemma in the body and the other proofs (preliminaries, soundness, short moves, limits of the shape), the
  evidence and the related-work table in the appendix.
- `long.tex` → `long.pdf`: the long, readable version: an informal overview, preliminaries (threats, safety,
  peeling), states and soundness, the Improvement Lemma with every proof, DE with pseudocode, its correctness and
  running time, a worked example with a TikZ figure of the exchange cycle, how large an exchange must be, the limits
  of the shape, the verification status and the evidence, and open problems.
- `refs.bib`: the bibliography of both; `Repo` is this repository at commit `a1f9dc0`, which holds the notes, tests,
  referee reports and Lean files.
- `llncs.cls` and `splncs04.bst`: Springer's LLNCS package, unmodified.
- `examples/check_examples.py`: an independent implementation of the definitions of `long.tex` (wants, free agents,
  blockers, finishing, want and pair arrows, rings, chains) and of DE with its loop chain / finish / ring, written
  from the paper's text, that recomputes every example and number of the paper: Example EFX-but-not-EFX₀ and
  Corollary two relevant goods; the small example of §6; the worked example of §7 (draft state, wants, free agents,
  blockers, the sets H_o, all 10 candidate completions failing, no short move, the 4 dominating valid states, the
  arrows and cycles of Figure 1, DE's ring and output, raw EFX₀, also for 2,000 random valuations); both instances of
  Proposition short moves and the remark on the reused leftover good; the ring family for k ≤ 4, d ≤ 3, and DE's
  trades on it at depth 4; Lemma cases of safety and Proposition limits of the shape, by listing every allocation;
  on all 30,507 valid states of the core profiles with n = 2 (m ≤ 6) and n = 3 (m ≤ 7), up to renaming goods, the
  finishing test, soundness (every completion), Lemma ring (every ring), the Improvement Lemma in the form of its
  proof and DE's loop started there; and DE, peeling included, on 40,000 random instances, compared with the loop of
  the previous version (an agent holding nothing finishing first) and with `k3/simplify/po/hall/hall.py`. Run from
  the repository root: `python3 paper/k3-simple/examples/check_examples.py` (one process, about a minute; output
  copied to `examples/check_output.txt`; exit status 0 iff every check passes).

Build (pdflatex and bibtex; TeX Live with `texlive-pictures` and `texlive-science`; fonts are Latin Modern):

    pdflatex main && bibtex main && pdflatex main && pdflatex main
    pdflatex long && bibtex long && pdflatex long && pdflatex long

Status of the claims, as the papers state it. Every result of the papers is a written proof that is also
machine-checked in Lean, except the rainbow-walk second proof of the Improvement Lemma:
- the Improvement Lemma, soundness, DE with at most 4n exchanges, and the shape (`lean/EFX/K3DE.lean`,
  `K3DEImprove.lean`, `K3DEAlgo.lean`, `K3DEExamples.lean`; ledger row K3S.PO.LEAN);
- the lemmas of §3, Lemma cases of safety and Proposition limits of the shape, Proposition short moves with its
  instances, the worked example's facts, Example EFX-but-not-EFX₀, the remark on protecting goods, the ring family
  (every k and depth; this corrected the papers' remark, which lacked the condition k ≤ 2^d for "no free agent
  absorbs"), at most n peeling rounds, and DE on ordered values such as ℝ≥0 (`lean/EFX/K3DEPrelim.lean`,
  `K3DELimits.lean`, `K3DEShort.lean`, `K3DEShortExamples.lean`, `K3DERings.lean`, `K3DEReal.lean`,
  `K3DERemarks.lean`; ledger rows K3S.PRELIM.LEAN, K3S.LIMITS, K3S.SHORT, K3S.EX.LEAN, K3S.RINGS, K3S.REAL.LEAN);
- the running time O(n(n + m)) (`lean/EFX/K3DECost*.lean`, ledger row K3S.TIME: at most 750 (n + 1)(n + m + 1)
  counted operations, array reads and writes one unit each).

The formal statements were written by AI assistant sessions; independent AI referee sessions compared them with the
papers and found no mismatch (`k3/simplify/po/referee/lean_audit.md`, `lean_audit2.md`, `lean_audit3.md`; their minor
findings are resolved). The written
proof was derived independently twice (`k3/simplify/po/hall/NOTES.md`, `k3/simplify/po/potential/NOTES.md`), refereed
once with no error (`k3/simplify/po/referee/README.md`; its four presentation fixes are applied), and checked by
computer on millions of states. The provers and the referee were AI agents: separate sessions of the coding assistant
(Claude Code), the referee given only the written proof. There has been no human peer review. The papers themselves
were proofread by a further AI referee session (no mathematical error; status and presentation fixes applied). Every
claim is taken from `LEDGER.md` (the rows above, and K3S.PO, K3S.SA, K3S.ST) and the notes it cites, or from the runs
of `examples/check_examples.py`; the papers change no ledger status.
