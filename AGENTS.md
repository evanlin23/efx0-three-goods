# Agent guide

Start here if you are an AI agent (Claude Code on the web, or any other coding agent) opening this repository. This file covers orientation and mechanics. The research brief is in PROMPT.md, and PROMPT.md wins wherever the two disagree.

## 1. Get the context (in this order)
1. `README.md`: the problem in one paragraph, current status, layout.
2. `PROMPT.md`: the full brief: problem, lemmas L1–L11, results, plan (Steps 0–4), working rules (§5), repository workflow (§7). Read all of it before doing anything.
3. `LEDGER.md`: every claim with its status and artifact. This is the source of truth; "Open items" at the bottom lists what to do next.
4. Open pull requests (drafts included: a draft PR claims its ledger item) and issues on GitHub, so you don't duplicate or contradict work in progress.
5. Only what your task needs: `proofs/lemmas.md` and `proofs/counterexamples.md` for proof work; `src/frontier.py` (module docstring first) for compute work; `attempts/` before trying an approach that may already have failed.

If the person who started your session named a workstream or task, do that. Otherwise, pick the first unclaimed item under "Open items" in LEDGER.md (unclaimed: no open PR, draft or not, names it) and say which one you picked.

## 2. Environment
- Python 3.11+, with `pip install -r requirements.txt` (python-sat, networkx, numpy), and nauty, whose `genbg` enumerates the cores (`apt-get install nauty`, or `brew install nauty`). In Claude Code on the web, `.claude/hooks/session-start.sh` installs all of these when the session starts.
- Lean 4 (`lean/`), toolchain pinned in `lean/lean-toolchain`; the hook installs it too (from GitHub if `release.lean-lang.org` is unreachable). Elsewhere: install [elan](https://github.com/leanprover/elan) and run `lean/check.sh`.
- Claude Code sessions default to Claude Opus 5.5 at xhigh effort (`.claude/settings.json`); a model or effort chosen when starting a session overrides this.
- No other services, credentials or network access are needed.

## 3. Branches, commits, pull requests
- **Never commit to `main`.** All changes reach `main` through a pull request that a human reviews and merges. Never merge your own PR.
- **Branch:** if your session assigned you a branch (e.g. Claude Code on the web's `claude/...` branches), use it as is: you may not be able to push anywhere else. Otherwise create one named after your workstream: `compute/<topic>`, `proof/<topic>` or `formal/<topic>` (e.g. `compute/n7-m12`, `proof/beta2-theta`, `formal/peel-r2`). Start from an up-to-date `main`.
- **Commits:** small and often, with the message `[workstream] what changed and why`, e.g. `[compute/n7-m12] certify n = 7, m = 12 cores (41 hypergraphs)`. Every commit also carries `Co-Authored-By: Evan Lin <113861384+evanlin23@users.noreply.github.com>`; in Claude Code on the web the session-start hook installs `.githooks/prepare-commit-msg`, which adds it. Elsewhere run `git config core.hooksPath .githooks` once, or add the line yourself.
- **Claim before you start:** after your first commit, push and open a **draft** pull request into `main` titled `[workstream] <ledger item>`, so parallel sessions see the item is taken.
- **Pull request:** when the unit of work is done, mark the draft ready for review (or open the PR), titled `[workstream] summary`. Fill in `.github/pull_request_template.md`. If you cannot push or open a PR, produce `git format-patch` output plus any new data files and say so.
- Don't edit another workstream's files. To dispute a claim, open an issue with the counterexample.

## 4. Checks to run before pushing
Fast (under 10 s each; run on every change):
```
python tools/check_ledger.py                     # every PROVED/CERTIFIED/REFUTED row has an existing artifact
python tools/check_certs.py results/certs_5_6.json.gz --expect 5:9:15 6:10:211 6:11:25
```
Full CI (`.github/workflows/verify.yml`, about 1–2 min; it runs only on pull requests, so a branch without a PR gets no CI; run when you touch `src/`, `tools/` or `results/`):
```
cd src
python frontier.py 5 6                           # ~10 s on 4 CPUs; writes src/certs_5_6.json.gz and src/frontier_results_5_6.json (gitignored)
python ../tools/check_certs.py certs_5_6.json.gz --expect 5:9:15 6:10:211 6:11:25
python verify_fail.py                            # needs frontier_results_5_6.json from the previous step
```
Lean (when you touch `lean/`; seconds once the toolchain is installed):
```
lean/check.sh                                    # core only, no sorry, warning-free, standard axioms only
```
Long searches (n = 7 and beyond, `run7.py`; `--n=8` for n = 8) use every CPU and can still take a long time; LEDGER.md "Open items" lists time estimates. Run them in the background, log to `results/`, and commit the log and certificate when done. `run7.py` appends each solved hypergraph to `src/checkpoint_{n}_{m}.jsonl` and resumes from it when rerun (`--fresh` starts over). The checkpoint lives in the container, and a reclaimed container loses it, so start only runs that fit in a session.

## 5. Rules that CI and reviewers enforce
- A ledger status changes only in a PR that adds the required artifact (PROMPT.md §5 rule 1). CI fails if a PROVED, CERTIFIED or REFUTED row points to a missing file.
- New certified results: commit the certificate (gzip JSON, as written by `frontier.py` or `run7.py`) under `results/` and make sure `tools/check_certs.py` accepts it. Files written into `src/` are gitignored, so copy them to `results/`.
- Superseded code is moved to `archive/` (one snapshot folder per version, see `archive/README.md`), never deleted. Don't overwrite result files the ledger cites; write new runs under new names.
- Lean (`lean/`, see `lean/README.md`): core Lean only (no `require` in `lakefile.toml`), the word `sorry` nowhere, a warning-free build, every declaration on `propext`, `Classical.choice` and `Quot.sound` only (so no `native_decide`, no new `axiom`). Give each ledger-facing theorem a `#print axioms` certificate at the end of its file and name it in the ledger's Lean column; `lean/check.sh` and `tools/check_ledger.py` enforce all of this. Reuse the model of evanlin23/mrd-efx (`lean/EFX/Model.lean`) rather than new definitions.
- Random testing is EVIDENCE only; failures here can be 1 in 23,000 profiles.
- UNSAT claims need a second, independently written encoding or a proof certificate.
- Cite only what you have read; mark the rest [unverified].
- Failed approaches go in `attempts/`, one file each, ending with the smallest failing configuration and a script that reproduces it.

## 6. Before you finish a session
The repository is the record; your chat is not. Make sure every result, log, and failed attempt is committed and pushed, the ledger reflects what you established (with artifacts), and the PR description says what is proved, certified, conjectured, and what remains open.
