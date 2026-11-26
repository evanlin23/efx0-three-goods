# Attempt: a single TTC / YRMH-IGYT priority rule picks the repairing chain (k = 4)

Workstream `proof/k4-ttc` (`k4/ttc.md` §3–§4). Status: **fails** (evidence: every configuration tested has a failing
start; smallest failing configuration below, replayed by brute force).

## The idea

The improving chains of `k4/sdc.md` §29 are request paths of YRMH-IGYT ("you request my house, I get your turn",
Abdulkadiroğlu–Sönmez 1999) in the market where every agent is an existing tenant holding its pick and the junk is
the pool of vacant goods (`k4/ttc.md` §2). §29 found that no value-based rule (most junk, largest gain) selects a
repairing chain. Could a priority rule of TTC type do it? A fixed priority order says whose pick is vacated (the head
of the request path). A fixed request preference says what each agent asks for: its most valuable option, its least
valuable improving option, the fewest junk goods, an inclusion-minimal junk part, or the fewest goods. Run the
mechanism from the picks, once or repeatedly, and test the one-absorber completion (`oc_absorb.extends_A`).

## What happens

`k4/ttc/ttc_test.py`; logs `results/k4_ttc/ttc_test_*.log`, `ttc_grid_*.log`. Counts are hard starts (orders whose
picks have no one-absorber completion) that the mechanism repairs.

| data | hard starts | best configuration | repaired |
|---|---|---|---|
| special | 69 | minval/minval, reverse order, repeated trades | 66 |
| screen | 662 | the same | 564 |
| suite | 797 | the same | 687 |
| random cores n ≤ 3 (3,000) | 480 | minval, priority revdanger, repeated | 393 |
| random cores n = 4 (1,500) | 872 | minimal, reverse order, repeated | 726 |
| logged hard profiles | 4,574 | minimal, reverse order, repeated | 3,622 |

For comparison, a uniformly chosen improving chain repairs a distinct hard start about a third of the time (mean
0.32–0.35, `ttc_test_*.log`, "baseline").

- *Failure modes* (`ttc_fail.py`, `results/k4_ttc/ttc_fail.log`, screen, the best configuration):
  - 39 runs *overshoot*: the first trade leaves the region of states that some complete EFX₀ allocation still
    value-dominates (`ttclib.dominated`), after which no value-monotone step can recover (the phenomenon of P1,
    K4.SDC.P1);
  - 59 runs *stall* inside that region: every request path dead-ends.
- *Choosing the head per start does not save a fixed preference* (`ttc_heads.py`, `results/k4_ttc/ttc_heads.log`):
  with every agent tried as head, the best single preference (minval) repairs 578 of the 662 screen starts.
- *Least-gain chain rules* (`min_rule.py`, `results/k4_ttc/min_rule.log`; the opposite of §29's rules) fail as well.
  On the 194 distinct hard screen starts, the best-ranked chains contain a repairing one for:
  - least total gain: 68;
  - least largest gain: 67;
  - least relative gain: 11;
  - fewest agents: 13;
  - least gain of x₀: 108.

  Pareto-minimal chains contain a repairing one on 10 of the 16 special starts.

## Smallest failing configuration

r428 (n = 3, m = 5), from the random n ≤ 3 cores (`results/k4_ttc/ttc_diag.log`):
- sets [[0, 1, 3, 4], [0, 2, 3, 4], [1, 2, 4]], values [[4, 3, 6, 8], [2, 10, 3, 6], [2, 3, 4]];
- order (0, 1, 2), picks (4, 2, 1), junk {0, 3}.

The best configuration makes no trade:
- head 2 requests its cheapest improvement, good 2 of agent 1;
- agent 1 requests 0's pick plus the junk {0, 3}, and that reserves the junk;
- agent 0, the dangerous agent that should take {0, 3}, has nothing left to request and leaves;
- every path then dead-ends.

The repairing chains are 0 → {0, 3}, {1, 3} or {0, 1, 3} with 2 taking 0's pick 4. The best configuration therefore
fails although one chain repairs.

Reproduce: `python3 k4/ttc/repro_attempts.py` (part (a); the completions are brute force from the raw EFX₀
definition; log `results/k4_ttc/repro_attempts.log`).

## What survives

The repairing chains *are* TTC request paths. Over every head and the 25 head/inner preference pairs, some
YRMH-IGYT run repairs every hard start tested (`ttc_union.py`, `ttc_cover.py`). Two request rules with a free head
suffice on the curated data: candidate TTC₂, `k4/ttc.md` §5. What fails is fixing the selection in advance.
