# The welfare maximum strands few goods (W(k, f); kgen/charity.md §6)

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

**It does not stop at one good: W(4, 1) is false** (Proposition CH-F). Take S′(3, 4)'s hypergraph (three sources
s_j holding {x_j, x′_j}; six champions c(g, j) holding {y_{g,j}}, each valuing y_{g,j}, x_j and one of the two pool
goods g_0, g_1; s_j valuing x_j, x′_j and the goods of the champions c(·, j − 1)) with the integer values

| agent | values (good: value) | holds |
|---|---|---|
| c(g₀, j₀) | 0: 20, 6: 21, 8: 40 | {8} |
| c(g₁, j₀) | 0: 12, 7: 16, 9: 27 | {9} |
| c(g₀, j₁) | 2: 20, 6: 21, 10: 40 | {10} |
| c(g₁, j₁) | 2: 12, 7: 13, 11: 24 | {11} |
| c(g₀, j₂) | 4: 20, 6: 21, 12: 40 | {12} |
| c(g₁, j₂) | 4: 9, 7: 10, 13: 18 | {13} |
| s₀ | 0: 2, 1: 1, 12: 7, 13: 4 | {0, 1} |
| s₁ | 2: 2, 3: 1, 8: 5, 9: 4 | {2, 3} |
| s₂ | 4: 2, 5: 1, 10: 8, 11: 4 | {4, 5} |

Goods 6 and 7 are unallocated; the total is 198. Every partial EFX₀ allocation leaving at most one good out has
total ≤ 197, by the SAT welfare maximiser (`chlib.welfare_max`) and by a separately written mixed-integer program
(scipy/HiGHS), which agree (`kgen/charity/w_counterexample.py`, `results/kgen_charity/w_counterexample.log`). The
values were found by an exact z3 search over real values on this hypergraph (`kgen/charity/w_synth_family.py`). So a
welfare maximum can strand two goods at k = 4, n = 9.

**Smallest failing configurations.** f = 0: the cut of GM4-G above (k = 3, n = 4, m = 7); at k = 4, GM4-G itself,
which with its copy gm4-G is the only one among the 168 curated k = 4 instances (`results/kgen_charity/w_screen.log`).
f = 1: the S′(3, 4) table (k = 4, n = 9, m = 14). No welfare maximum strands a good with n = 3 at k = 3, and none
strands two with n = 3 (k = 3, 4) or n = 4 (k = 3) (exact z3 search over all values and all m ≤ nk + n,
`results/kgen_charity/w_synth_n*.log`).

Reproduce: `python3 kgen/charity/w_brute.py` (no SAT), `python3 kgen/charity/w_search.py screen 0 0` (lines
STRANDED), `python3 kgen/charity/w_gm4g3.py 1 6000`, `python3 kgen/charity/w_counterexample.py` (f = 1).
