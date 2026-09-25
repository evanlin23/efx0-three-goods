# Attempt: reduce two 4-good agents that share a good of degree 2 (configuration xy)

Workstream `proof/k4-mincex`, round 2 (β = 4, `k4/MINCEX.md` §8). Failed as a reduction, and not needed: β = 4 was
settled by certifying the candidate cores directly (§8). Kept for the record.

**Why try it.** At β = 4 the candidate cores that resist direct search have mostly P4 agents (4 goods, one private). Two
of them share a good of degree 2 (every shared good has degree 2 in the six-agent all-P4 cores). No reduction of
round 1 applies there: K4.MC3 and K4.MC5 need a P3 agent.

**Configuration xy.** Agents e and f, each Q3, P4 or Q4, share a good g of degree 2. *Closed*: they also share e's
first other good. S = {e, f}, I = {g} + their private goods. Reductions: DEL, and every one-agent gadget h on the
boundary goods plus one gadget good z′ when there are fewer than 4 boundary goods (menu of 1,665 valuation classes).
All use the unenvied bundle (Lemma M1(b)).

**Result for P4–P4** (82,944 profiles; `python3 k4/mincex4.py explore xy P4 P4 [closed]`):

| | one-agent gadgets | DEL |
|---|---|---|
| open (e: g, a, b, p_e; f: g, x, y, p_f) | 0 | 9,692 |
| closed (f: g, a, y, p_f) | 73,548 | (not needed for the table) |

The open case is the one in the all-P4 cores. There, h must value the four boundary goods a, b, x, y and has no room
for a gadget good. Without one, a bundle that receives the worthless goods g, p_e, p_f is never "inner" in Y, so it
cannot be dominated. This is the same obstruction as in `attempts/k4-mincex-drop-private.md`. DEL fails whenever the
rest can bundle a, b (for e) with outside goods: e then needs v(g) + v(p_e) ≥ v(a) + v(b), which fails for most types.

**Smallest failing configuration.** The open P4–P4 pair with e and f of type (8, 6, 4, 1) on (a, b, g, p): each ranks its
two boundary goods first. DEL fails at the state where a and b sit in one outside bundle with outside goods, since
v_e(g) + v_e(p_e) = 5 < 14. Every one-agent gadget fails, because h cannot hold a gadget good.

**What would be needed.** Two-agent gadgets (for example e′ = e without g and f′ = f without g, one good fewer). Their
local states number about 3·10⁵ (6 local goods, 2 gadget agents), too many for `reduce4.py`'s Python enumeration; a C
version, or a restriction to "natural" extensions, would be the next step.

Reproduce: `cd k4 && python3 mincex4.py explore xy P4 P4` (and `... xy P4 P4 closed`), ~10 s each.
