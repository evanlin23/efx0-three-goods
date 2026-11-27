# Referee report: Lemma SDPO, Lemma MAXSD, Lemma MAX (`k4/sdc.md` §28, §31 on `claude/kind-lamport-y8fdme`; `k4/oc1_hall.md` §19)

Referee: `proof/k4-referee`, 2026-11-26.
- Read: `k4/sdc.md` §28 and §31 at `d48084e` (coordinator branch), and `k4/oc1_hall.md` §19 at `e2b4701`.
- Check: `k4/referee/maxsd_ref.py`, log `results/k4_referee/maxsd_ref.log`. Written from the text, brute force, no
  shared code.

OC₁^max (`k4/sdc.md` §31) is the new central conjecture. Lemmas SDPO and MAXSD are what make it imply TARGET₄.

## Verdicts

| item | verdict |
|---|---|
| Lemma SDPO (strict values: SD outcomes over all orders = Pareto-optimal matchings; MD ⟺ VD) | **CORRECT** (strictness is essential; with ties both inclusions fail) |
| Lemma MAXSD (some SD order's picks form a maximum matching) | **CORRECT**. It also holds with ties broken by index (remark below) |
| Lemma MAX (no agent reachable from a pickless agent by an alternating path values a junk good) | **CORRECT** |

## 1. Lemma SDPO

- **(⊆).** Let μ′ Pareto-dominate Y = SD(π), and let i be the first agent of π where they differ.
  - The agents before i hold their Y-goods in μ′ as well, so μ′_i (if any) was not taken before i's turn, and i
    values it.
  - Y_i = none is then impossible. Otherwise i took its favourite available good, so v_i(μ′_i) < v_i(Y_i) by strict
    values, against domination.
  - μ′_i = none is impossible when Y_i is a good.
  - Hence μ′ = Y. Correct.
- **(⊇).** Pareto-optimality has three consequences:
  - an agent's favourite good is held (else it takes it);
  - pointers to holders of favourites cannot form a cycle (trading along it improves everyone on it), so some matched
    agent holds its favourite;
  - an unmatched agent's goods are all held.

  Putting that agent first and removing it with its good keeps Pareto-optimality in the rest (a domination there
  extends). Inducting with "favourite remaining good", and putting unmatched agents last, reproduces μ. Correct.
- **MD ⟺ VD.** Every matching is dominated by a Pareto-optimal one (finite dominance order), which is an SD outcome.
  Correct.
- **Ties.** Both inclusions fail. Example: agent 1 values goods a and b equally and breaks the tie to a; agent 2 values
  only a. Order (1, 2) gives (a, –), which (b, a) dominates. My ties run finds SD ≠ PO on 1,105 of 2,000 instances.
  The lemma states strict values, and OC₁^max is for strict cores, so this is consistent.

## 2. Lemma MAXSD

Take a maximum matching M that is Pareto-optimal among maximum matchings; it exists because there are finitely many.
A Pareto improvement M′ of M keeps every matched agent matched, since its value stays positive. So |M′| ≥ |M|, M′ is
maximum, and M′ = M. Hence M is Pareto-optimal among all matchings, and an SD outcome by SDPO. Correct.

**Remark.** MAXSD holds with ties too, for SD with tie-breaking by index. Perturb each agent's values by the
tie-breaking order: v_i(g) + ε·(rank) gives strict values, the same SD outcomes and the same relevance graph, so the
same ν. My ties run agrees: some SD outcome is maximum on all 2,000 instances.

## 3. Lemma MAX

- If an agent j reachable from a pickless agent u by an alternating path (u, g₁, j₁, …, j) values a junk good g′,
  then the path plus the edge j–g′ is augmenting: u and g′ are both unmatched. That contradicts maximality.
  - The alternating walk can be shortened to a path, since reachability is the same.
- Want arrows from a pickless agent form such a path. Wanting means valuing, so the next edge is a non-matching
  edge to a pick, followed by the matching edge to its holder. Want-chains are acyclic at SD picks.
- Hence no dangerous frozen agent lies above a pickless agent.

Correct.

## 4. Computation (evidence)

Random instances with ≤ 4 relevant goods per agent. All matchings are enumerated, SD runs over every order, and the
Pareto-optimal matchings are computed by brute force.

| set | instances | SDPO (SD outcomes = PO matchings) | MAXSD (some SD outcome maximum) | MAX at maximum SD outcomes |
|---|---|---|---|---|
| strict, n = 2–5, m = 2–7 | 4,000 | 0 failures | 0 failures | 12,914 starts, 0 failures |
| strict, n = 6, m = 4–8 | 500 | 0 failures | 0 failures | 4,933 starts, 0 failures |
| ties (values 1–3), n = 2–5 | 2,000 | **1,105 failures** (expected: strictness is needed) | 0 failures | 6,858 starts, 0 failures |
