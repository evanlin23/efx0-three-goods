# The welfare maximum is complete (W(4) with f = 0; kgen/charity.md §6)

**Idea.** Pareto maxima can strand Θ(√n) goods (`attempts/kgen-charity-pareto-maxima.md`), but welfare maxima are
much rarer objects: in S′(2, 3) both the welfare maximum and the leximin maximum over partial EFX₀ allocations are
complete, and S′'s stranded states are not supported points (no rescaling of the agents' values makes them welfare
maxima, `results/kgen_charity/welfare_support.log`). On GM4-E, whose stranded Pareto maximum K4.SDC.P1 reports as a
total-value maximum, the largest total (24) is tied with complete allocations, so "the welfare maximum with the fewest
unallocated goods" is complete there. That statement would imply TARGET₄.

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

**Smallest failing configuration.** GM4-G itself (n = 4, m = 7); among the 168 curated k = 4 instances it and its
copy gm4-G are the only ones (`results/kgen_charity/w_screen.log`).

Reproduce: `python3 kgen/charity/w_search.py screen 0 0` (lines STRANDED) and the brute force in
`kgen/charity/w_brute.py`.
