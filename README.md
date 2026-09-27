# EFX₀ with at most three relevant goods per agent

Question (CS 580 course project, Fall 2026; answered yes, see Status): does every fair-division instance with nonnegative real additive valuations in which each agent positively values at most three goods admit a complete EFX₀ allocation (envy-free up to any good, where the removed good may be worthless to the envious agent)?

**Status** (every claim with its evidence is in [LEDGER.md](LEDGER.md), the source of truth; the row names are given in parentheses):

- **The answer: yes, with machine-checked proofs.** Every instance with nonnegative real additive valuations in which each agent positively values at most three goods has a complete EFX₀ allocation (TARGET; row T, PROVED). If every agent values exactly three goods and none of them more than the other two together, there is one in which all but at most one agent receive at most two goods (conjecture D; row D, PROVED). Both are machine-checked in Lean for values in any type satisfying `EFX.OrderedValue`, the axioms of a linearly ordered cancellative commutative monoid (`EFX.target_ordered`, `EFX.corollaryD_ordered` in [lean/EFX/RealValues.lean](lean/EFX/RealValues.lean)), derived from `EFX.target` and `EFX.LB.corollaryD` over ℕ by the reduction L12 (`EFX.l12`; row L12, PROVED). ℝ≥0 is covered by the standard fact that it satisfies these axioms; core Lean has no real numbers, so that one step is not a Lean theorem. The proof is construction LB⁺ (row S2.LB+, PROVED; [proofs/lb_last_step.md](proofs/lb_last_step.md)): a serial dictatorship with R1 priority, leftover goods in free slots, and the surplus to one owner after at most one rotation of picks along a chain of agents. An independently written Lean statement of both theorems follows from them (row AUD).
- **The algorithm K3ALG** ([proofs/k3_algorithm.md](proofs/k3_algorithm.md), `lean/EFX/K3*.lean`): peel agents by rule R1, then run LB⁺ with computed rankings; LB⁺'s owner test is exact without a minimum vertex cover (Proposition O; row K3.OWNER, PROVED). Machine-checked in Lean, every row PROVED:
  - correctness: for natural-number values it returns an EFX₀ allocation whenever every agent values at most three goods (`EFX.K3.algo_efx0`; K3.ALG);
  - at most 400·(n + m + 1)⁴ operations in the unit-cost model of [lean/EFX/Timed.lean](lean/EFX/Timed.lean), for the counted program whose value is the algorithm (`EFX.K3.algoC_cost`; K3.ALG.TIME), and the finer bound ≤ 270·(n⁴ + n²m) for the same program (`EFX.K3.algoC_cost_fine''`; K3.ALG.FINE);
  - nonnegative rational values, scaled to natural numbers (`EFX.K3.algoRat_efx0`; K3.RAT);
  - real values in the comparison model: from a correct comparison oracle, a computed natural-number surrogate (at most n(m + 12) oracle calls), then K3ALG on it; the output is EFX₀ for the original values, in any `EFX.OrderedValue` (`EFX.K3.algoOrd_efx0`, `EFX.K3.algoOrdC_cost`; K3.ALG.REAL);
  - the candidate owner r lies in the last block of Phase 1 (`EFX.LB.lastOut_lastBlock`; K3.LASTBLOCK);
  - the size of the large bundle: ω = m − 2n + |NA|, and the owner receives at least ω + 2 goods, exactly ω + 2 when the other slots are full (`EFX.LB.largeBundle_size`; K3.SIZE);
  - serial dictatorship for k ≤ 2 (at most two relevant goods per agent), in every order and with every choice of favourite, for natural-number values (`EFX.Inst.sdRun_efx0`; K3.SD2).

  A Python implementation (`fast` in [k3/k3algo.py](k3/k3algo.py)) gives the same output as a literal transcription of the Lean program on 200,000 random instances and runs in about linear time up to 10⁵ agents (row K3.ALG.RUN, EVIDENCE).
- **Not formalized:** the bound on bit operations; the O((n + m) log n) analysis of the Python implementation; serial dictatorship for k ≤ 2 over ordered values (its Lean statement is for ℕ); and the ℝ≥0 instance of `EFX.OrderedValue` (the standard fact above). The full list is in [lean/README.md](lean/README.md), "Not formalized".
- **The papers** ([paper/k3/](paper/k3/), build instructions in its README): `paper/k3/main.pdf` is the 8-page LLNCS submission (references and appendix after page 8); `paper/k3/long.pdf` is the long, readable version, with every proof of the main theorems in the body, the pseudocode and two examples traced step by step; `paper/k3/examples/` holds the checks of those examples (`trace_examples.py`, and `lean_examples.lean` for Lean's own evaluation).
- **k = 4 (at most four relevant goods per agent) is open.** Work in progress is in `k4/` and LEDGER.md open items 18–27; the named next target is Conjecture DL₂ (row K4.STRAT.DL2, CONJECTURE).
- **Earlier results**, partial results that came before the proof (details in the ledger):
  - certified by exhaustive computation: EFX₀ exists for every instance with n ≤ 7 (R1, R5); conjecture D for every core with n ≤ 6 (R3), every connected core with n = 7 (R2, S2.N7) and every connected core with n = 8, m ≥ 13 (R4, S2.N8);
  - proved: D for connected cores with β = 2 (D2) and for connected cores in which every agent has a private good (D3.0); certified: D for connected cores with β = 3 (D3);
  - refuted: bundles of at most two goods always suffice (X1, smallest n = 3), also when m ≤ 2n − 2 (X2, smallest n = 4); one bundle of three goods always suffices (X4);
  - from the literature, read in full ([proofs/citations.md](proofs/citations.md)): EFX₀ exists, for every n, for cores with m ≤ n + 3 and for cores in which every good is relevant to at most two agents (T3); no published result implies TARGET or D.

## Layout
- `AGENTS.md`: how an AI agent gets oriented, sets up, branches, checks and opens a pull request (`CLAUDE.md` loads it for Claude Code)
- `PROMPT.md`: the research brief every agent works from (problem, results, plan, rules, repository workflow)
- `LEDGER.md`: every claim, its status, and the artifact behind it; the single source of truth
- `CONTRIBUTING.md`: the contribution rules in short, for humans and agents
- `src/`: tools; `frontier.py` is the main one (enumerate connected cores with `cores_nauty.py`, CEGAR over ranking profiles, save certificates)
- `tools/`: checkers run by CI: `check_certs.py` (SAT-free certificate checker), `check_enum.py` (a certificate lists every connected core, by orbit counting), `check_ledger.py` (status ⇒ artifact)
- `results/`: logs, result summaries, certificate files
- `proofs/`: written proofs; `attempts/`: failed approaches with their smallest failing configuration
- `lean/`: Lean formalization of ledger items (core Lean only, no `sorry`, standard axioms only; see `lean/README.md`)
- `k3/`: Python implementations of K3ALG (`k3algo.py`: `fast` and the literal transcription `mirror`), the cross-check against Lean, timings, and the local search LS2
- `k4/`: the k = 4 workstream (open; notes, searches, test suite)
- `paper/k3/`: the papers on the k = 3 result (`main.tex`, `long.tex`) and the checks of their examples
- `archive/`: superseded versions of code, kept verbatim (see `archive/README.md`)

## Reproduce
```
pip install -r requirements.txt   # plus nauty: apt-get install nauty (or brew install nauty)
cd src
python frontier.py 5 6        # ~10 s on 4 CPUs: enumerate cores (nauty genbg), search, certify; writes certs_5_6.json.gz
python ../tools/check_certs.py certs_5_6.json.gz --expect 5:9:15 6:10:211 6:11:25   # re-check without SAT
python verify_fail.py         # independent confirmation of the 57 refutations of conjecture A
cd ..
lean/check.sh                 # Lean: build, no sorry, standard axioms only, replay check (pinned toolchain)
python3 paper/k3/examples/trace_examples.py   # recompute and check the examples of the papers
```

## Working here
Humans and agents follow PROMPT.md §7: one branch per workstream (`compute/...`, `proof/...`, `formal/...`), pull requests into `main`, CI green, and a ledger status change only with its artifact. Protect `main` (Settings → Branches: require a pull request and passing checks).

Kickoff message for a new agent (for Claude Code on the web, start a session on this repository and paste it; the repository is already cloned and dependencies are installed):
> You're joining an open research project in fair division. Read AGENTS.md and follow it: read README.md, PROMPT.md and LEDGER.md, then take the WORKSTREAM workstream (compute: Steps 1–2 of the plan; proof: Step 3; formal: machine-check PROVED ledger items in `lean/`). The repository, not this chat, is the record: work on your own branch, push, and open a pull request into main when a unit of work is done.

## AI use
Most code and text here were produced with AI assistants (Claude) under human direction; commit messages are tagged with the workstream that produced them. Cite accordingly in course submissions.
