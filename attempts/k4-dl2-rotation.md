# DL₂ fails at f = 0 too: an isolated pre-allocation whose only repairs rotate a 3-cycle

Workstream `compute/k4-dl2` (PR #70; `k4/dl2.c`). Statement tested: Conjecture DL₂ of `k4/strategy.md` §3 (ledger
K4.STRAT.DL2). The first counterexample is the proof workstream's `dl2-n3m7` (`attempts/k4-dl2-three-agents.md` on
`proof/k4-dl2-k1`, commit 3b498a7): f = 1, where the repair is a role swap of the frozen agent with its needer plus a
release by the third agent. That PR owns the status change of K4.STRAT.DL2. This file records a **different**
failure, at f = 0, which is Theorem Z's case, with a different repair shape. Evidence rows: K4.DL2.KN, K4.DL2.SHAPE.

## The instance (`dl2-rot-n3m7`, `k4/suite/instances/dl2-rot-n3m7.json`)

Core 44 of `results/k4_certs_3.json.gz` (0-based position), a pure connected k = 4 core, n = 3, m = 7. Agent: good:value.

| agent | goods and values | a > b > c > d | private |
|---|---|---|---|
| 0 | 0:6, 2:4, 4:8, 6:5 | 4, 0, 6, 2 | 0 |
| 1 | 1:2, 3:7, 5:4, 6:10 | 6, 3, 5, 1 | 1 |
| 2 | 2:7, 3:4, 4:2, 5:8 | 5, 2, 3, 4 | — |

σ = 2n − m = −1, so ω = f + 1 ≥ 1 for every profile of this core. Here f = 0 and ω = 1. The min-frozen class (here: the
P ∈ 𝒫 without needs) has 36 elements; 35 of them have def ≤ 0, and one has def 1:

**P = ({0, 6}, {3, 5}, {2, 4}), J = {1}, no slot.** Every base is need-free (11 > 8, 11 > 10, 9 > 8), so nobody is frozen.
The owner bundle must have ω + 2 = 3 goods (Lemma H1), so it must contain the junk good 1, and each owner's bundle then
threatens the next agent of a cycle:
- owner 0, X = {0, 6, 1}: agent 1 (holding {3, 5}, 11) sees 6 + 1 = 12 > 11 (1 ∉ R_0: no good to remove) — Lemma H3's
  **e2** (a_1 = 6 ∈ B_0, d_1 = 1 ∈ J, label 1);
- owner 1, X = {3, 5, 1}: agent 2 (holding {2, 4}, 9) sees 4 + 8 = 12 > 9 — **e3** (R_2 ∖ B_2 = B_1, unhittable);
- owner 2, X = {2, 4, 1}: agent 0 (holding {0, 6}, 11) sees 4 + 8 = 12 > 11 — **e3**.

So def(P) = 1 (each owner keeps only its base: 2 goods, one short).

**P is isolated.** Every other min-frozen P′ differs from P in all three bases. Each agent's top lies in another
agent's base: a_0 = 4 ∈ B_2, a_1 = 6 ∈ B_0, a_2 = 5 ∈ B_1. With the other two bases fixed, each agent's only need-free
base avoiding its top is the one it holds (agent 0: {0, 6}, {0, 2}, {2, 6} avoid 4, and only {0, 6} misses {3, 5} and
{2, 4}; similarly for 1 and 2). Changing two agents fails for the same reason. So k*(P) = 3 = n and DL₂ fails.
Every repair at distance 3 is a **rotation of the cycle**: goods move around 1 → 2 → 0 → 1 (agent 2 takes a good
of B_1, agent 0 one of B_2, agent 1 one of B_0; the rest goes to the junk). An example is P′ = ({0, 4}, {3, 6}, {2, 5}),
with def(P′) = 0, where each agent takes its top from the agent that held it. Every agent strictly gains, so P is not
Pareto-maximal: the rotation is a Pareto-improvement, as in Theorem Z's Lemmas P and R and Theorem H0's rotation along
a cycle of the exposure relation.

## What it says

- DL₂ fails in Theorem Z's case f = 0, where C₄ᵐⁱⁿ is proved. The obstruction is not the proof workstream's role swap
  (there is no frozen agent): the only improving moves rotate a threat cycle through all n agents.
- m = 7 is the least m with f = 0 and ω ≥ 1 at n = 3 (f = 0 needs σ < 0, i.e. m ≥ 2n + 1), so this is a smallest f = 0
  failure. n = 2 cannot fail (k* ≤ n).
- Any corrected target has to count a rotation along a cycle of the exposure relation (of any length) as one move.
  Whether k* = n recurs at n ≥ 4 is measured in K4.DL2.KN (`k4/dl2_data.md`).

## Reproduce

```
python3 attempts/k4_dl2_rotation.py                       # raw re-derivation from the definitions (third implementation)
python3 k4/suite/run.py --pred=k4/dl2_pred.py:dl2_c --only=dl2-rot-n3m7       # k4/dl2.c
python3 k4/suite/run.py --pred=k4/dl2_pred.py:dl2_suite --only=dl2-rot-n3m7   # k4/suite/deficit_local.py (model.py)
```
