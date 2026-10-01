# Rule RK with the no-upgrade policy (`-N1`): cloud runs of 2026-10-01

Branch `proof/k4-rulef-n4-3`, from `proof/k4-rulef` at 83eaf32. `k4/rulef.c` sha256 prefix `5721abf3bc9e25b1` in
every log. Machine: 4 CPUs, gcc 13.3.0, Python 3.11.15. Checkpoints were in the session scratchpad (not committed).
All results are EVIDENCE: one implementation of the classes (`k4/rulef.c`), with every rule run's output checked
against the raw EFX₀ definition.

## Runs

1. `python3 k4/rulef_run.py results/k4_certs_4_n4_3.json.gz -A41 -r1 -Y1 -N1 --jobs=4 --checkpoint=<scratch>/ck/step1_rk_4_n4_3_n1.jsonl`
   → `rk_n4_n4_3_n1.log` (the full command line is the log's first line).
2. `CK=<scratch>/ck_runs bash k4/rulef_runs.sh n1`: one worker per step (`-A41 -r1 -Y1 -N1 --checkpoint=...`) →
   `rk_n2_n1.log`, `rk_n3_n1.log`, `rk_n4_n4_1_n1.log`, `rk_n4_n4_2_n1.log`, and a second run of n = 4 with three
   4-good agents. The script writes that run to `rk_n4_n4_3_n1.log`, the same file as run 1. It is kept here as
   `rk_n4_n4_3_n1_runs.log`, so run 1's log keeps its name.

No run was interrupted or resumed. Every run computed all of its cores.

## Counters (from the logs)

K0 and K1 give how many rotations LB₄ʳ needs on RK's sequence: 0 / 1 / fails with ≤ 1.

| class | log | cores | profiles | K0 | K1 | C40 | open | violations | fails or raw-check failures | time |
|---|---|---|---|---|---|---|---|---|---|---|
| n = 2 | `rk_n2_n1.log` | 5 | 189,216 | 189,216 / 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 | 0 | 0 | 1 s (1 worker) |
| n = 3 | `rk_n3_n1.log` | 51 | 299,837,376 | 299,574,040 / 0 / 0 | 0 / 263,336 / 0 | 0 / 0 / 0 | 0 / 0 / 0 | 0 | 0 | 40 s (1 worker) |
| n = 4, one 4-good agent | `rk_n4_n4_1_n1.log` | 135 | 7,247,232 | 7,246,416 / 0 / 0 | 0 / 816 / 0 | 0 / 0 / 0 | 0 / 0 / 0 | 0 | 0 | 2 s (1 worker) |
| n = 4, two | `rk_n4_n4_2_n1.log` | 309 | 724,847,616 | 724,640,736 / 0 / 0 | 0 / 206,880 / 0 | 0 / 0 / 0 | 0 / 0 / 0 | 0 | 0 | 71 s (1 worker) |
| n = 4, three (run 1) | `rk_n4_n4_3_n1.log` | 339 | 34,971,844,608 | 34,961,492,780 / 0 / 0 | 0 / 10,351,828 / 0 | 0 / 0 / 0 | 0 / 0 / 0 | 0 | 0 | 471 s (4 workers; 475 s wall) |
| n = 4, three (run 2) | `rk_n4_n4_3_n1_runs.log` | 339 | 34,971,844,608 | 34,961,492,780 / 0 / 0 | 0 / 10,351,828 / 0 | 0 / 0 / 0 | 0 / 0 / 0 | 0 | 0 | 1845 s (1 worker) |

Times are the `time` field each log prints. The `rulef_runs.sh n1` batch took 1959 s of wall time, from
20:54:48Z to 21:27:27Z. Run 1 took 475 s, from 20:46:29Z to 20:54:24Z. The two runs of n = 4 with three 4-good
agents agree on every counter; only the time differs.

## What changes against `-Y1`

**Open is 0 in every class:** no profile is left open, and C40 is never reached.

`-N1` lets classes K0 and K1 also try LB₄ʳ's run without upgrades. Compared with the `-Y1` logs
(`rk_*_y1.log`), K0 grows by 0 at n = 2 and 0 at n = 3. At n = 4 it grows by 4, 720 and 35,028 with one, two and
three 4-good agents. Those are exactly the counting gaps of `k4/rulef.md` §5.1. K1's "LB₄ʳ needs 0 rotations"
count is now 0 in every class; with `-Y1` it was 32 and 13,620 at n = 4 with two and three 4-good agents.

K0 now equals rule F's no-rotation count from the table of `k4/rulef.md` §5.1 (#44) in every class:

| class | K0 with `-N1` | rule F, 0 rotations (#44) |
|---|---|---|
| n = 2 | 189,216 | 189,216 |
| n = 3 | 299,574,040 | 299,574,040 |
| n = 4, one 4-good agent | 7,246,416 | 7,246,416 |
| n = 4, two | 724,640,736 | 724,640,736 |
| n = 4, three | 34,961,492,780 | 34,961,492,780 |

What follows from this. K0's promise is checked on every profile: there are 0 violations, so LB₄ʳ succeeds without
rotation on every K0 profile. K0 is therefore contained in rule F's no-rotation set, and since the counts are equal,
the two sets are the same. So:
- With kept-out sets as in Remark 4 (`-Y1`) and all three of LB₄ʳ's policies, **Lemma K's counting gap is 0** on
  every exhaustive class (n ≤ 4, at most three 4-good agents).
- Rule RK uses a rotation exactly where rule F needs one: the "RK is not optimal" counts of §5.1 (4, 688, 21,456)
  drop to 0.
- Lemma M still holds, with K0 and K1 alone, on all 3.6·10¹⁰ profiles.

LEDGER.md and `k4/rulef.md` are not edited here.
