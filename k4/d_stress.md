# Stress test of K4.D (the D2 shape) on large structured cores of 4-good agents

Workstream `compute/k4-d-stress`. Ledger rows `K4.DS.*`, all EVIDENCE: random and hill-climbed value profiles on fixed
structures, where every single decision is exact (SAT), confirmed by a second, independently written encoding.

**Question.** Does the D2 shape of K4.D survive on large structured instances made of many 4-good agents? K4.D says
every strict k = 4 core has an EFX₀ allocation with at most one bundle of more than two goods. The instances include
the cores H_t of `k4/c4.md` §7, on which the bounded construction LB₄ʳ fails.

**Answer (evidence).** Yes, on every structure tried, up to n = 29 agents (m = 73 goods, β = 21, all agents 4-good):
- 5,200 random strict profiles over 20 structures: every one has a D2 EFX₀ allocation;
- the paper's values of H_t (t ≤ 7) have one too.

The margin does not shrink with n:
- adversarial hill-climbing toward fewer *feasible large-bundle owners* (agents o such that some D2 allocation keeps
  every other bundle at ≤ 2 goods) never went below n − 1;
- on every structure with n ≥ 6 it stayed at n.

D2 allocations are plentiful: every count we took hit its cap (8–32). No counterexample, so nothing to confirm; no
K4.DS row is REFUTED.

## 1. Method

**Instances.** A structure is a hypergraph (every agent's goods). It must be a k = 4 core: `check4.is_core`
(connected, 3 or 4 goods per agent, at most d − 2 private goods). A profile gives each agent one type from
`search4.domain`: strictly balanced, strict, and p + q < s + t for an agent with two private goods. That is, a strict
core profile.

**Decision** (`k4/d_stress.py`). search4.Core's SAT model with each agent's domain fixed to its one type, model D2 ("at
most one bundle with more than 2 goods"). One SAT call decides a profile, exactly. With (s, c) = (None, None) the same
model decides EFX₀ of any shape, and (2, 2) allows two large bundles; neither was needed.

**Second encoding** (`k4/d_stress_check.py`, written from scratch). pysat, with:
- an owner per good;
- reified "more than 2 goods" indicators, at most one of them;
- EFX₀ as forbidden patterns derived directly from v_i(X_i) ≥ v_i(X_j) − v_i(g), with a forced "X_j holds a good
  outside R_i" indicator.

Every allocation it finds is re-checked by the plain definition. Agreement with `d_stress.py`
(`results/k4_dstress_check_selftest.log`): 600 of 600 random profiles on four structures, both for D2 and for "all
bundles ≤ 2" (the latter unsatisfiable in 4 non-trivial cases and in all 150 trivial ones with m > 2n).

**Margin.** `owners(profile)` (second encoding, one solver, assumptions per candidate owner) is the set of agents that
can own the large bundle in some D2 allocation. D2 fails iff it is empty. `--owners=STEPS` hill-climbs profiles (one or
two agents' types changed per step, accepted if not worse) toward fewer owners. Counting D2 allocations with blocking
clauses was tried first, but every count hit its cap (8–32). So the count carries no gradient, and the owner count
replaced it.

## 2. Families

- **chain t** (H_t of `k4/c4.md` §7): a head ℓ = {g_1, z, u, u′}, then t gadgets. Gadget j has three x's
  {a_{j,i}, b_{j,i}, c_{j,i}, g_j} and a y {a_{j,1}, a_{j,2}, a_{j,3}, e_j}, with e_j = g_{j+1} and e_t = z.
  n = 4t + 1, m = 10t + 3.
- **chain t h**: h heads, each with its own chain of t gadgets; all heads and all chain ends share z.
- **cycle t**: the gadgets in a cycle (e_t = w), with the head on {g_1, w} and two private goods.
- **tree t**: gadgets in a binary tree (heap order). Gadget j's y links to its first child's g. A second child is
  joined to g_j by a head-like agent {g_j, g_child, p, q}.
- **pure n m**: random connected pure cores (every agent 4-good) with small m, hence high β = 3n − m + 1 (β = 11 to 21
  for n = 6 to 12).

## 3. Results (`results/k4_dstress_*.log`)

| structure | n | m | β | random profiles | without D2 | owner climb: min feasible owners |
|---|---|---|---|---|---|---|
| chain 1 (H_1) | 5 | 13 | 3 | 500 | 0 | 4 of 5 (3 climbs × 60 steps) |
| chain 2 | 9 | 23 | 5 | 400 | 0 | 9 of 9 (2 × 30) |
| chain 3 | 13 | 33 | 7 | 300 | 0 | not finished (stopped) |
| chain 4 | 17 | 43 | 9 | 200 | 0 | — |
| chain 5 | 21 | 53 | 11 | 120 | 0 | — |
| chain 6 | 25 | 63 | 13 | 80 | 0 | — |
| chain 7 | 29 | 73 | 15 | 60 | 0 | — |
| chain 2, 2 heads | 18 | 45 | 10 | 200 | 0 | — |
| chain 2, 3 heads | 27 | 67 | 15 | 120 | 0 | — |
| cycle 2 | 9 | 23 | 5 | 300 | 0 | 9 of 9 (2 × 20) |
| cycle 4 | 17 | 43 | 9 | 150 | 0 | — |
| tree 3 | 14 | 35 | 8 | 250 | 0 | not finished (stopped) |
| tree 5 | 23 | 57 | 13 | 120 | 0 | — |
| pure 6 8 | 6 | 8 | 11 | 500 | 0 | 6 of 6 (3 × 60) |
| pure 7 9 | 7 | 9 | 13 | 500 | 0 | 7 of 7 (3 × 50) |
| pure 8 10 | 8 | 10 | 15 | 400 | 0 | 8 of 8 (2 × 40) |
| pure 9 12 | 9 | 12 | 16 | 300 | 0 | 9 of 9 (2 × 30) |
| pure 10 13 | 10 | 13 | 18 | 300 | 0 | 10 of 10 (2 × 20) |
| pure 11 15 | 11 | 15 | 19 | 200 | 0 | — |
| pure 12 16 | 12 | 16 | 21 | 200 | 0 | — |

The paper's values of H_t (§7 of `k4/c4.md`) have a D2 allocation for every t ≤ 7, and every agent of H_1 and H_2 can
own the large bundle.

*All profiles.* H_1 is a pure n = 5 core, so K4.R5p already certifies D2 on it under every strict profile. For
H_2 (n = 9, about 10¹⁹ profiles) exhaustive certification was not attempted.

## 4. What this does and does not show

- It is EVIDENCE (PROMPT.md §5 rule 3). Random profiles miss rare failures: at k = 3, some failures occurred in 1 of
  23,000 profiles. The owner climb is a local search.
- The D2 shape has a lot of slack on these structures. D2 allocations are too many to count to a useful cap, and almost
  every agent can hold the large bundle. Nothing here suggests the target shape needs to change.
- LB₄ʳ's failure on H_t (`k4/c4.md` §7) is a failure of that construction's bounded rotations, not of the D2 shape.
- Not done (handoff):
  - gadgets of other sizes and shapes (y with fewer a's, x's with one private good);
  - gadgets sharing goods;
  - exhaustive profile certification beyond n = 5;
  - an adversarial objective with a real gradient. Candidates: the least number of goods in the large bundle over D2
    allocations, compared with the counting bound m − 2n + 2; or the number of feasible owners restricted to
    non-heads.

## Reproduce

```
cd k4
python3 d_stress.py chain 7 --values=paper --profiles=60 --seed=7         # one line of the table; see the logs for all
python3 d_stress.py pure 8 10 --profiles=400 --owners=40 --restarts=2 --seed=16
python3 d_stress_check.py --selftest pure 3 5 150                          # the two encodings agree
```
