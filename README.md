# EFX₀ with at most three relevant goods per agent

Open question (CS 580 course project, Fall 2026): does every additive fair-division instance in which each agent positively values at most three goods admit a complete EFX₀ allocation (envy-free up to any good, where the removed good may be worthless to the envious agent)?

**Status** (details and evidence in [LEDGER.md](LEDGER.md)):
- Reduced to "cores" (agents with exactly three goods, balanced, at most one private good), where EFX₀ is a purely combinatorial condition.
- Certified: EFX₀ exists for every such instance with at most 7 agents, conditional on Mahara's m ≤ n + 3 theorem.
- Refuted: "bundles of at most two goods always suffice" (n = 5), and its weaker form for m ≤ 2n − 2 (n = 6).
- Main conjecture D: some EFX₀ allocation has at most one bundle with more than two goods. Certified for connected cores with n ≤ 7 and m ≥ n + 4, and with n = 8, m ≥ 14 (no counterexample so far).

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
