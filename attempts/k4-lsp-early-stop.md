# LS4 that stops at the first placement (choice rule -DEARLY)

Workstream `proof/k4-ls-plus` (`k4/ls4plus.md` §1, §4).

**Approach.** Every one of the 8 logged dead ends of LS4 (`attempts/k4-ls-dead-end.md`) is created by its *last* move, in which the last agent adds a second good to its singleton. The state before that move is not a dead end. The idea is to avoid being greedy: before every move, check whether Phase 2 (b) or (c) can already place the pool (both are checked directly, so stopping is sound), and stop if so.

**Counts** (`k4/ls4alg.c -DEARLY`, `results/k4_lsp_variants_19.log`). On the 19 logged LS4 failure states (`results/k4_ls4_failures_4_pure.tsv`), early stopping repairs 6: five of the 8 dead ends and one of the 11 others. The remaining 13 fail. On them, no state of LS4's path ever admits a single dump or a dump plus solo goods.

**Where it breaks (smallest found: n = 4, m = 7, pure core; only the 19 logged failure profiles were tried).** Agents and values:
- agent 0: goods 0:5, 2:8, 5:4, 6:6;
- agent 1: goods 0:4, 3:2, 4:5, 5:8;
- agent 2: goods 1:2, 2:8, 4:5, 6:4;
- agent 3: goods 1:6, 3:2, 5:10, 6:7.

LS4's 16 moves pass through no state with a single-dump or dump-plus-solo placement, nor, after the first move, with any junk placement at all (shape (d)). The final state Y = {2} | {5} | {1, 4} | {3, 6}, U = {0}, is a dead end: no complete EFX₀ allocation gives every agent at least its value in it, so in particular it has no completion.

Reproduce: `python3 k4/lsp_attempts.py` (independent brute force: replays the 16 moves, checks every state on the path for a placement of each shape, and checks that the final state has no completion and is a dead end).
