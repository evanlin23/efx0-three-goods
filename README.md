# EFX₀ with at most three relevant goods per agent

Question (CS 580 course project, Fall 2026; answered yes, see Status): does every fair-division instance with nonnegative real additive valuations in which each agent positively values at most three goods admit a complete EFX₀ allocation (envy-free up to any good, where the removed good may be worthless to the envious agent)?

**Status** (details and evidence in [LEDGER.md](LEDGER.md)):
- **Conjecture D, and hence TARGET, are proved: machine-checked in Lean over any ordered value type (ℝ≥0 by the textbook fact that it satisfies the axioms), via the reduction to natural numbers L12 ([proofs/real_values.md](proofs/real_values.md), machine-checked too)** ([proofs/lb_last_step.md](proofs/lb_last_step.md); Lean: `EFX.target_ordered` and `EFX.corollaryD_ordered` in [lean/EFX/RealValues.lean](lean/EFX/RealValues.lean), from `EFX.target` in [lean/EFX/Target.lean](lean/EFX/Target.lean) and `EFX.LB.corollaryD` in [lean/EFX/CorollaryD.lean](lean/EFX/CorollaryD.lean) over ℕ, see [lean/README.md](lean/README.md)). Every instance with nonnegative real additive valuations in which every agent positively values at most three goods has a complete EFX₀ allocation. The proof uses construction LB⁺: serial dictatorship with LB's junk placement, plus one "rotation" along a chain of agents when the natural owner of the large bundle fails. Two independent reviews of the written proof found no error. The items below are the partial results that came before.
- Reduced to "cores" (agents with exactly three goods, balanced, at most one private good), where EFX₀ is a purely combinatorial condition.
- Certified: EFX₀ exists for every such instance with at most 6 agents. Every connected core is covered, including those with m ≤ n + 3, which were first left to Mahara's theorem; nothing external is needed. With at most 7 agents it is certified too, again with nothing external: construction LB (below) certifies every connected core with 7 agents, including the 37,488 with at most 10 goods that were first left to Mahara's theorem.
- From the literature (read in full, [proofs/citations.md](proofs/citations.md)): EFX₀ exists, for every n, for cores with m ≤ n + 3 and for cores in which every good is relevant to at most two agents (ledger T3). No published result implies TARGET or conjecture D.
- Refuted: "bundles of at most two goods always suffice" (smallest counterexample n = 3), and its weaker form for m ≤ 2n − 2 (smallest n = 4).
- Main conjecture D: some EFX₀ allocation has at most one bundle with more than two goods. Certified for every core with n ≤ 6, and for every connected core with n = 7 or n = 8, m ≥ 14.
- Proved: conjecture D for every core with m = 2n − 1 (cyclomatic number β = 2), for all n ([proofs/beta2.md](proofs/beta2.md)); for every connected core in which every agent has a private good, for every β; and for every connected core with m = 2n − 2 (β = 3) and at most two agents without a private good ([proofs/beta3.md](proofs/beta3.md)).
- Certified: conjecture D for every connected core with m = 2n − 2 (β = 3), for all n: a proved reduction to 394 small "reduced" cores (n ≤ 10), checked exhaustively with an independent checker ([proofs/beta3.md](proofs/beta3.md)).
- Proved ([proofs/multigraph_extension.md](proofs/multigraph_extension.md), ledger T5): the multigraph theorem for cores, re-proved without the paper, and extended to goods with three or more valuers when each such good is the top of all its valuers and the ranking profile has a popular matching. The paper's allocation shape cannot survive a single good with three valuers (n = 3 example).
- Step 2 ([proofs/construction.md](proofs/construction.md)): an explicit construction, LB, whose output is always EFX₀ with at most one large bundle (proved). It never fails on any core with n ≤ 6 or any connected core with n = 7 (certified, for the labelling the enumeration produces; LB breaks ties by index). The open gap is its last step. When a large bundle is needed (n ≤ 6), it can always go to an agent holding only its bottom good, together with goods private to agents that don't need them (conjecture K).
- Certified independently of D3 (a second certification of the β ≤ 3 part of ledger T4): EFX₀ exists for every instance whose core components have β ≤ 3, with no appeal to the literature, via the structure of a minimal counterexample ([proofs/min_counterexample.md](proofs/min_counterexample.md)): no good relevant to exactly two agents is relevant to two agents with private goods, so a minimal counterexample has n ≤ 5(β − 1) agents.

## Layout
- `AGENTS.md`: how an AI agent gets oriented, sets up, branches, checks and opens a pull request (`CLAUDE.md` loads it for Claude Code)
- `PROMPT.md`: the research brief every agent works from (problem, results, plan, rules, repository workflow)
- `LEDGER.md`: every claim, its status, and the artifact behind it; the single source of truth
- `src/`: tools; `frontier.py` is the main one (enumerate connected cores with `cores_nauty.py`, CEGAR over ranking profiles, save certificates)
- `tools/`: checkers run by CI: `check_certs.py` (SAT-free certificate checker), `check_enum.py` (a certificate lists every connected core, by orbit counting), `check_ledger.py` (status ⇒ artifact)
- `results/`: logs, result summaries, certificate files
- `proofs/`: written proofs; `attempts/`: failed approaches with their smallest failing configuration
- `lean/`: Lean formalization of ledger items (core Lean only, no `sorry`, standard axioms only; see `lean/README.md`)
- `archive/`: superseded versions of code, kept verbatim (see `archive/README.md`)

## Reproduce
```
pip install -r requirements.txt   # plus nauty: apt-get install nauty (or brew install nauty)
cd src
python frontier.py 5 6        # ~10 s on 4 CPUs: enumerate cores (nauty genbg), search, certify; writes certs_5_6.json.gz
python ../tools/check_certs.py certs_5_6.json.gz --expect 5:9:15 6:10:211 6:11:25   # re-check without SAT
python verify_fail.py         # independent confirmation of the 57 refutations of conjecture A
```

## Working here
Humans and agents follow PROMPT.md §7: one branch per workstream (`compute/...`, `proof/...`, `formal/...`), pull requests into `main`, CI green, and a ledger status change only with its artifact. Protect `main` (Settings → Branches: require a pull request and passing checks).

Kickoff message for a new agent (for Claude Code on the web, start a session on this repository and paste it; the repository is already cloned and dependencies are installed):
> You're joining an open research project in fair division. Read AGENTS.md and follow it: read README.md, PROMPT.md and LEDGER.md, then take the WORKSTREAM workstream (compute: Steps 1–2 of the plan; proof: Step 3; formal: machine-check PROVED ledger items in `lean/`). The repository, not this chat, is the record: work on your own branch, push, and open a pull request into main when a unit of work is done.

## AI use
Most code and text here were produced with AI assistants (Claude) under human direction; commit messages are tagged with the workstream that produced them. Cite accordingly in course submissions.
