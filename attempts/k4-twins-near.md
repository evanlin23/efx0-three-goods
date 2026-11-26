# Attempt: reduce near-twins (two agents with three common goods) in a minimal counterexample to TARGET₄

Workstream `proof/k4-twins` (`k4/TWINS.md`). Failed unless two of the common goods are valued by nobody else (then the
pair is a closed double edge, reduced by K4.MC8). Generator only (`k4/twins4.py`); reductions DEL, KEEP-e/KEEP-f and
one-agent gadgets with 0–2 gadget goods, all with the unenvied bundle.

**Configurations** near-K1-K2-j: e of kind K1 and f of kind K2 share s0, s1, s2, of which j have degree 2 (interior);
the fourth good of a 4-good agent is its own boundary good (Q4) or private good (P4).

| configuration | profiles | reduced |
|---|---|---|
| near-Q3-Q4-0 | 1,728 | 0 (I = ∅: no reduction exists, same argument as twins-Q3-0) |
| near-Q3-Q4-1 | 1,728 | 740 |
| near-Q3-Q4-2 = dbl-Q3-Q4-c1 | 1,728 | 1,728 (certified) |
| near-Q3-P4-0 | 1,728 | 432 |
| near-Q3-P4-1 | 1,728 | 1,564 |
| near-Q3-P4-2 = dbl-Q3-P4-c1 | 1,728 | 1,728 (certified) |

Not run: the near-twins of two 4-good agents with j ≤ 1 (82,944 profiles each; j = 2 is dbl-K1-K2-c1).

**Smallest failing configuration.** near-Q3-Q4-0 with any types, e.g. e on (s0, s1, s2) = (4, 3, 2): I = ∅, so the only
gadget has one agent and the state "h holds its favourite boundary good, the other two common goods in outside
bundles with outside goods" defeats every extension (`k4/TWINS.md` §3).

Reproduce: `cd k4 && python3 twins4.py explore near-Q3-Q4-0 near-Q3-Q4-1 near-Q3-P4-0 near-Q3-P4-1`;
`python3 twins4.py why near-Q3-P4-1` for a failing state.
