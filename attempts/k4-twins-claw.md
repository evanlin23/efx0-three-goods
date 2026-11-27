# Attempt: reduce a claw (three P3 agents on one good of degree 3) in a minimal counterexample to TARGET₄

Workstream `proof/k4-twins` (`k4/TWINS.md`). **Superseded: the claw is reduced by two-agent gadgets with gadget goods
(K4.MC9, `k4/TWINS.md` §4).** What failed, kept for the record: one-agent gadgets (177 of 216), and the two-agent copy
gadget below. Generator only for these (`k4/twins4.py`).

**Why try it.** K4.MC4's bound n ≤ 3(β − 1) is tight only if every good of degree ≥ 3 is a degree-3 good valued by
three P3 agents (A = 3t in its proof). Excluding claws gives A ≤ 2t and n ≤ 3(β − 1) − t/2.

**Configuration claw.** S = {f1, f2, f3}, f_i on (G, y_i, p_i); G is valued by them only (interior), p_i private, y_i
boundary. 216 profiles. Reductions: DEL, and every one-agent gadget h on (y1, y2, y3) plus a gadget good z′ (menu of
1,665 classes); all with the unenvied bundle.

**Result.** 177 of 216 profiles reduce (DEL 78). The 39 left are exactly those in which no f_i ranks its private
good first and at most one f_i ranks G > p_i > y_i (multisets of rankings, top first: every combination of G>y>p, y>G>p,
y>p>G, plus those with one G>p>y and the other two in {y>G>p, y>p>G}). So in a minimal counterexample a claw's agents
never rank their private good first; and at most one of them has a degree-2 good shared with an E3 agent (by K4.MC5(ii)
such an agent ranks G > p > y). The second statement does not improve K4.MC4's bound: the extremal case t = n₁ is not
constrained by it.

**Two-agent gadget tried.** DEL-f1: delete f1 and p1, keep copies of f2 and f3 (G and their private goods renamed into
I′; |S′| = 2 < 3, and G′ becomes a degree-2 good of two P3 agents in H′, which is allowed: H′ need not be a core). It has
520,264 local states, 56,128 admissible for some profile. On the hardest profile (all three agents G > y > p; 12,440
admissible states):
- with the extension search restricted to keeping each copy's moved items together (`twins4.BlockReduction`, a
  restriction of reduce4's search), it does **not** reduce it (829 s on one CPU);
- reduce4's full extension search did not finish in 30 minutes on 3 CPUs (stopped).
The full search over all 216 profiles would take about 6 CPU-hours in reduce4's Python (~0.4 s per admissible state).

With the C extension search (`k4/reduce4c.c`), the full search of DEL-f1 over all 216 profiles takes 4 minutes: it
reduces 105, all of them already reduced by one-agent gadgets (`results/k4_twins/claw2c.log`). What works instead are
two *fixed* gadget agents with a gadget good each (K4.MC9).

**Smallest failing configuration.** All three agents of type (G: 4, y: 3, p: 2), i.e. G > y > p.
- DEL fails at the state where y1, y2, y3 lie together in one outside bundle without outside goods, unenvied.
- The gadget h = (z′: 1), the menu item that reduces the most profiles (78, the same ones as DEL), fails at the state h holds
  {y1, z′}, {y2, y3} is an outside bundle, h's bundle unenvied.

Reproduce: `cd k4 && python3 twins4.py why claw --zs=1` (coverage, the failing states);
`python3 twins4.py explore claw --zs=1`; `python3 twins4.py claw2 --jobs=1` (the two-agent gadget with the block
search, ~15 min; `--full` for reduce4's full search).
