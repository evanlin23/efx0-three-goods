# The welfare maximum is complete (W(k) with f = 0; kgen/charity.md §6)

**Idea.** Pareto maxima can strand Θ(√n) goods (`attempts/kgen-charity-pareto-maxima.md`), but welfare maxima are
much rarer objects: in S′(2, 3) both the welfare maximum and the leximin maximum over partial EFX₀ allocations are
complete, and S′'s stranded states are not supported points (no rescaling of the agents' values makes them welfare
maxima, `results/kgen_charity/welfare_support.log`). On GM4-E, whose stranded Pareto maximum K4.SDC.P1 reports as a
total-value maximum, the largest total (24) is tied with complete allocations, so "the welfare maximum with the fewest
unallocated goods" is complete there. That statement would imply TARGET_k.

**Where it breaks.** GM4-G (n = 4, m = 7, k = 4, one of the GM4 cores of `k4/de4/gm4_counterexample.py`):

| agent | values |
|---|---|
| 0 | 0: 3, 2: 6, 5: 2, 6: 10 |
| 1 | 1: 1, 4: 6, 5: 8, 6: 4 |
| 2 | 2: 3, 3: 6, 5: 8, 6: 4 |
| 3 | 3: 6, 4: 3, 5: 4, 6: 8 |

The largest total value over partial EFX₀ allocations is 32, attained only by ({0, 2}, {1, 4}, {5}, {6}) with good
3 unallocated (value vector (9, 7, 8, 8)); every complete EFX₀ allocation has total at most 31 (brute force over all
5⁷ partial allocations, and the SAT search `chlib.welfare_max`). So W(4) needs f ≥ 1.

**It fails at k = 3 too.** Cut every agent of GM4-G to three goods, dropping agent 0's good 5 and agent 1's good 6
(and the cross values 6 of agent 2 and 5 of agent 3), and keep the other values:

| agent | values | holds |
|---|---|---|
| 0 | 0: 3, 2: 6, 6: 10 | {0, 2} |
| 1 | 1: 1, 4: 6, 5: 8 | {1, 4} |
| 2 | 2: 3, 3: 6, 5: 8 | {5} |
| 3 | 3: 6, 4: 3, 6: 8 | {6} |

Good 3 is unallocated. The largest total over partial EFX₀ allocations is again 32, attained only by this state; every
complete EFX₀ allocation has total ≤ 31 (brute force, `results/kgen_charity/w_brute.log`). Its hypergraph is that of
S′(2, 3) (sources 0, 1; champions 2, 3); 6,000 uniformly random value vectors on the two hypergraphs never strand a
good at the welfare maximum (`results/kgen_charity/w_gm4g3.log`), so these values are special. So the welfare
maximum, like Pareto maxima and CKMS's stopping states, can strand a good at k = 3. Whether it can strand more than
one good at fixed k (W(k) with f ≥ 1) is open.

**Smallest failing configuration.** The table above (k = 3, n = 4, m = 7); at k = 4, GM4-G itself, which with its
copy gm4-G is the only one among the 168 curated k = 4 instances (`results/kgen_charity/w_screen.log`).

Reproduce: `python3 kgen/charity/w_brute.py` (no SAT), `python3 kgen/charity/w_search.py screen 0 0` (lines
STRANDED), `python3 kgen/charity/w_gm4g3.py 1 6000`.
