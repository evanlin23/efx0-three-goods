# The owner swap without its θ-b exception (proof/k4-sx)

**Candidate.** `k4/sx.md` §3, Lemma A without the exception θ-b. At a Z′-maximum Q of a non-completable f = 1 key
(g, x), let o be a terminal leaf: o needs g, and its bundle X_o = Q_o ∪ L threatens no free agent but threatens x. Then
the (T3) move "o takes g, x takes a set admissible for x inside X_o" ends at a state with deficit below def*(g, x).

**Why it fails.** If o is big-top on g, all three of its lower goods lie in X_o, and ω ≥ 2, then X_o threatens o once o
holds g: θ_o(X_o) = u₁ + u₂ + u₃ > g by balance. x's bundle must then drop one of o's lower goods. Lemma A therefore
excludes this case, and Lemmas C and C′ of `k4/sx.md` §3 handle it with another owner.

**Smallest failing configuration found.** n = 4, m = 10, ω = 3. This is the first such instance in (n, m) order among
#53's n = 3 catalogue and the n = 4 hunts of `results/k4_sx/hunt/`. The n = 3 exhaustive check is `results/k4_sx/zprime/`.

| agent | goods: values |
|---|---|
| 0 (x) | 0:4, 2:5, 6:6, 9:8 |
| 1 (o) | 1:4, 5:2, 8:3, 9:8 |
| 2 | 3:4, 6:2, 7:3, 9:8 |
| 3 | 4:2, 7:4, 8:3 |

- The key is (9, 0) with def* = 1.
- The Z′-maximum has Q_1 = {1, 8}, Q_2 = {3, 6}, Q_3 = {4, 7} and L = {0, 2, 5}. Agent 1 is big-top on 9 (4 + 3 < 8),
  and U_1 = {1, 5, 8} ⊆ X_1.
- x's only admissible set inside X_1 is {0, 2}. After the swap the state ({0, 2}, {9}, {3, 6}, {4, 7}) still has deficit 1.
- Lemma C′ repairs this configuration: agent 2, the other terminal, owns {1, 3, 6, 8} and unfreezes agent 1.

**Reproduce.** `python3 attempts/k4_sx_attempts.py`, case 1 (`results/k4_sx/attempts_replay.log`). It uses two
implementations: `k4/suite/model.py` through `k4/sx_keygraph.py`, and main's `k4/c4x_check.py` through
`k4/sx_xcheck.py`.
