# Archive
Superseded versions of code, kept verbatim so earlier results stay reproducible. Nothing outside `archive/` imports from here. Superseded code is moved here, never deleted (AGENTS.md §5).

Each folder is a snapshot that mirrors the repository layout, so a snapshot's scripts run against each other (e.g. `cd archive/v1-python-enumeration/src && python frontier.py 5 6`). Result files are not moved here: the ledger links to them by path in `results/`, and new runs write new file names instead of overwriting them.

| Snapshot | Replaced by | What changed | Produced |
|---|---|---|---|
| `v1-ledger-lint/` | `tools/check_ledger.py` | Did not check the ledger's Lean column (added with `lean/`) | — |
| `v1-python-enumeration/` | `src/cores_nauty.py`, `src/frontier.py`, `src/run7.py`, `tools/check_certs.py` | Cores enumerated in pure Python (`gen_cores`, still in `src/frontier.py` for `--enum=python` and the cross-check) instead of nauty's `genbg`; one hypergraph at a time; Minisat instead of Glucose; coverage via flat index arrays | `results/frontier56*.log`, `results/frontier7.log`, `results/certs_5_6.json.gz`, `results/frontier_results_5_6.json`, `results/frontier_results_7.json`, `results/verify_fail.log` |
| `v2-certs-without-shape-check/` | `tools/check_certs.py` | Checked coverage by EFX₀ allocations but not that each allocation has the shape of its record's model (C2, C3s3, C3), so a certificate showed EFX₀ existence without showing conjecture D; no `--require-d` | — |
| `v1-paper-k3-simple-long/` | `paper/k3-simple/main.tex` | `long.tex`, a longer exposition of the same proof as `main.tex` (an informal overview, every proof in the body, the verification as a section). Once `main.tex` became self-contained it only duplicated the paper; this is its last version, with the corrections of the October 2026 review (efx0-three-goods-proof `ffeae05`) | `long.pdf` (25 pages; read by the referee of `k3/simplify/po/referee/simple/REPORT.md` at an earlier commit) |
