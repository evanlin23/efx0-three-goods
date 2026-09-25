# Attempt: reduce a P3 agent that shares a good of degree 2 with a Q3, P4 or Q4 agent (configuration px)

Workstream `proof/k4-mincex` (`k4/MINCEX.md` §4, K4.MC5). Partly failed; the failures are what the restriction in
K4.MC5 records.

**Configuration px.** A P3 agent f = {g, y, p_f} shares a good g of degree 2 with an agent e of kind Q3 (3 goods, none
private), P4 (4 goods, one private) or Q4 (4 goods, none private). *Closed*: e also values y; *open*: it does not.
Reductions tried: DEL (delete e, f and the interior goods), and every one-agent gadget h on the boundary goods plus
one gadget good z′ when there are fewer than 4 boundary goods, over a menu of all valuation classes with values 0..10
(1,665 classes for 4 goods, 43 for 3). CON-f (h = e with g renamed y) is one of them. All use the unenvied bundle
(Lemma M1(b)).

**Result** (`results/k4_min_cex_reductions.log`, re-checked by `k4/check_reductions4.py`):

| e | open: reduced | closed: reduced |
|---|---|---|
| Q3 | 34 of 36 | 36 of 36 |
| P4 | 1,718 of 1,728 | 1,728 of 1,728 |
| Q4 | 648 of 1,728 | 1,656 of 1,728 |

For Q3 and P4 (open), every profile left has f ranking y > p_f > g and e ranking g first. These are the restrictions
K4.MC5 uses. For Q4 the gadget has no room for a gadget good (h already values the four boundary goods a, b, c, y),
which is why so few profiles reduce.

**Smallest failing configuration.** e = Q3 on {g, a, b} with values g = 4, a = 3, b = 2; f on {g, y, p_f} with
y = 4, p_f = 3, g = 2 (the other profile left swaps a and b).
- DEL fails at the state where the rest puts a, b and y into one outside bundle without outside goods, and nobody
  envies it. Then θ_e({a, b, y}) = v(a) + v(b) − 0 = 5 (y is worthless to e), but e's only interior good g is worth 4.
- CON-f (h = e with g renamed y, values y = 4, a = 3, b = 2) fails at the state where h holds {a}, b and y are
  singletons in outside bundles, and {y} is unenvied. h is safe there, since no bundle has two goods. The extension
  must give a to e or f, and g, p_f to e, f or the unenvied bundle {y}. The reducer's exhaustive search finds no
  placement in which e and f are both safe and every changed bundle is dominated.

What would be needed: a two-agent gadget (two agents with fewer goods), or a reduction that uses more of Y than
Lemma M1 does (for example, which outside agent holds y).

Reproduce: `cd k4 && python3 mincex_attempts.py px-open` (lists the profiles left and one failing state of DEL and of
CON-f for each).
