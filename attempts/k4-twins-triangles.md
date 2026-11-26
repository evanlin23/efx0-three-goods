# Attempt: reduce a triangle of degree-2 goods (three agents pairwise sharing a good nobody else values)

Workstream `proof/k4-twins` (`k4/TWINS.md`). Partly failed. Generator only (`k4/twins4.py`).

**Why try it.** After the double edges of K4.MC8, the next shortest cycles of Γ′ through goods of degree 2 are
triangles. Of the 20,882 β = 5, n = 6 candidates without a certified double edge, 5,660 contain such a triangle
(1,469 with three E3 agents, 730 with kinds Q3–Q3–Q3 or Q3–Q3–P4).

**Configuration tri-K1-K2-K3.** e1, e2, e3 of kinds Q3 / P4 / Q4; g12, g13, g23 of degree 2 (interior); e_i's other
goods boundary (a_i, and b_i for Q4) or private (P4). Reductions DEL and every one-agent gadget h on (a1, a2, a3) plus
a gadget good z′; all with the unenvied bundle.

| configuration | profiles | reduced |
|---|---|---|
| tri-Q3-Q3-Q3 | 216 | 208 |
| tri-Q3-Q3-P4 | 10,368 | 10,288 |

In tri-Q3-Q3-Q3 the 8 profiles left are those in which every agent ranks its boundary good a_i first (and its two
triangle goods either way). Not run: the triangles with two or three 4-good agents (≥ 497,664 profiles; reduce4's
gadget search holds a menu × profiles array).

**What would be needed.** Two-agent gadgets (|S′| = 2 < 3), e.g. the triangle replaced by a double edge.

**Smallest failing configuration.** tri-Q3-Q3-Q3 with e1 on (g12, g13, a1) = (3, 2, 4), e2 on (g12, g23, a2) = (3, 2, 4),
e3 on (g13, g23, a3) = (3, 2, 4).
- DEL fails at the state where a1, a2, a3 lie together in one outside bundle without outside goods, unenvied.
- The gadget h = (z′: 1), the menu item that reduces the most profiles, fails at the state h holds {a1, z′}, {a2, a3} is an outside bundle, h's bundle unenvied.

Reproduce: `cd k4 && python3 twins4.py why tri-Q3-Q3-Q3 --zs=1`; `python3 twins4.py explore tri-Q3-Q3-P4 --zs=0,1`.
