# EFX₀ with at most three relevant goods per agent

Open question (CS 580 course project, Fall 2026): does every additive fair-division instance in which each agent positively values at most three goods admit a complete EFX₀ allocation (envy-free up to any good, where the removed good may be worthless to the envious agent)?

**Status** (details and evidence in [LEDGER.md](LEDGER.md)):
- Reduced to "cores" (agents with exactly three goods, balanced, at most one private good), where EFX₀ is a purely combinatorial condition.
- Certified: EFX₀ exists for every such instance with at most 6 agents, conditional on Mahara's m ≤ n + 3 theorem.
- Refuted: "bundles of at most two goods always suffice" (n = 5), and its weaker form for m ≤ 2n − 2 (n = 6).
- Main conjecture D: some EFX₀ allocation has at most one bundle with more than two goods. Certified for n ≤ 6 and for n = 7, m = 13.

## Layout
- `PROMPT.md`: the research brief every agent works from (problem, results, plan, rules, repository workflow)
- `LEDGER.md`: every claim, its status, and the artifact behind it; the single source of truth
- `src/`: tools; `frontier.py` is the main one (enumerate connected cores, CEGAR over ranking profiles, save certificates)
- `tools/`: checkers run by CI: `check_certs.py` (SAT-free certificate checker), `check_ledger.py` (status ⇒ artifact)
- `results/`: logs, result summaries, certificate files
- `proofs/`: written proofs; `attempts/`: failed approaches with their smallest failing configuration

## Reproduce
```
pip install python-sat networkx numpy
cd src
python frontier.py 5 6        # about 4 min: enumerate cores, search, certify; writes certs_5_6.json.gz
python ../tools/check_certs.py certs_5_6.json.gz --expect 5:9:15 6:10:211 6:11:25   # re-check without SAT
python verify_fail.py         # independent confirmation of the 57 refutations of conjecture A
```

## Working here
Humans and agents follow PROMPT.md §7: one branch per workstream (`compute/...`, `proof/...`), pull requests into `main`, CI green, and a ledger status change only with its artifact. Protect `main` (Settings → Branches: require a pull request and passing checks).

Kickoff message for a new agent:
> You're joining an open research project in fair division. Clone REPO_URL, read PROMPT.md and LEDGER.md, and take the WORKSTREAM workstream (compute: Steps 1–2 of the plan; proof: Step 3). The repository, not this chat, is the record: work on your own branch and open pull requests.

## AI use
Most code and text here were produced with AI assistants (Claude) under human direction; commit messages are tagged with the workstream that produced them. Cite accordingly in course submissions.
