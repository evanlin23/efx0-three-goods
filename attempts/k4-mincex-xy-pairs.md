# Attempt: reduce two 4-good agents that share a good of degree 2 (configuration xy)

Workstream `proof/k4-mincex`, round 2 (β = 4, `k4/MINCEX.md` §8). Failed as a reduction, and not needed: β = 4 was settled
by certifying 5,552 of the 5,558 candidate cores directly, and covering the other 6 (graphical) by the multigraph
theorem (§8). Kept for the record.

**Why try it.** The candidate cores that resist direct search are made of P4 agents (4 goods, one private). In the six
all-P4 cores left uncertified, every shared good has degree 2, so every pair of adjacent agents is such a pair. No
reduction of round 1 applies there: K4.MC3 and K4.MC5 need a P3 agent.

**Configuration xy.** Agents e and f, each Q3, P4 or Q4, share a good g of degree 2. *Open*: they share nothing else.
*Closed*: they also share e's first other good. S = {e, f}, I = {g} plus their private goods. Reductions: DEL, and every
one-agent gadget h on the boundary goods plus one gadget good z′ when there are fewer than 4 boundary goods (menu of
1,665 valuation classes). All use the unenvied bundle (Lemma M1(b)).

**Result for P4–P4** (82,944 profiles):

| | one-agent gadgets | DEL |
|---|---|---|
| open (e: g, a, b, p_e; f: g, x, y, p_f) | 0 | 9,692 |
| closed (f: g, a, y, p_f) | 73,548 | 9,692 (all also reduced by gadgets) |

In the open case h must value the four boundary goods a, b, x, y and has no room for a gadget good. Without one, a
bundle that receives the goods g, p_e, p_f (worthless to outside agents) is never "inner" in Y, so it cannot be
dominated. This is the same obstruction as in `attempts/k4-mincex-drop-private.md`.

Every all-P4 core has open pairs. Four of the six uncertified cores also have a closed pair (a double edge: two P4 agents
sharing two goods of degree 2). The two simple ones (agent multigraph the prism or K₃,₃) have only open pairs
(`k4/MINCEX.md` §8 lists them). A certified closed-xy reduction would cut the type domains of those four cores. It was
not certified, because the open pairs remain in every one of them.

**What would be needed.** Two-agent gadgets, for example e′ = e without g and f′ = f without g (one good fewer). Their
local states number about 3·10⁵ (6 local goods, 2 gadget agents), too many for `reduce4.py`'s Python enumeration. A C
version, or a restriction to "natural" extensions, would be the next step.

**Smallest failing configuration.** The open P4–P4 pair with both agents of type (8, 6, 4, 1) on their goods ordered
boundary, boundary, g, private. That is, e on (a, b, g, p_e) = (8, 6, 4, 1) and f on (x, y, g, p_f) = (8, 6, 4, 1):
each ranks its two boundary goods first.
- No one-agent gadget of the menu reduces it (none reduces any open profile).
- DEL fails at the state where a, b, x, y lie together in one outside bundle without outside goods, and nobody envies
  it. Then θ_e({a, b, x, y}) = v(a) + v(b) = 14 (x and y are worthless to e), but e can hold only interior goods, worth
  at most v(g) + v(p_e) = 5 to it.

Reproduce: `cd k4 && python3 mincex_attempts.py xy` (the named profile: 0 of 82,944 reduced by the menu, DEL's count and
its failing state; log `results/k4_attempt_xy.log`, about 30 s). `python3 mincex4.py explore xy P4 P4 [closed]` prints
the coverage counts alone.
