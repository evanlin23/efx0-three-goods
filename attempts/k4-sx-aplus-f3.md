# Lemmas A⁺ and B⁺ do not reach every non-completable key at f ≥ 2 (proof/k4-sx)

**Candidate.** At every key κ with f ≥ 2 and def*(κ) > 0, some configuration maximizing (r′, Λ′) at κ satisfies the
hypotheses of Lemma A⁺ or of Lemma B⁺ (`k4/sx.md` §6). For Lemma A⁺ these are:
- a free-valid owner o whose bundle X_o threatens exactly one agent, the frozen x;
- a need chain x = w₀ → w₁ → … → w_j of frozen agents (w_i needs φ(w_{i−1})), with o needing φ(w_j);
- θ_o(X_o) ≤ v_o(φ(w_j)).

Lemma B⁺ asks for the same leaf o and chain, with a free needer τ of φ(w_j) on a threat path τ → … → o.

Either lemma would then give a (T3⁺) neighbour with def* ≤ 0.

**Why it fails.** The instances below show three obstructions, alone or together:
- every free-valid owner's bundle threatens two frozen agents;
- the free needers of the chain's end are off the threat paths to the leaves;
- the owner that needs the chain's end is threatened by its own bundle once it holds that good (the f ≥ 2 analogue of
  θ-b), or the leaf is an (R) agent with its fourth good in the pool.

**Smallest failing configuration found.** n = 4, m = 8, f = 2, ω = 2. It was found by the f ≥ 2 referee of the PR #80
review. Every agent values its four goods 2, 3, 8, 4, in the order listed:

| agent | goods: values |
|---|---|
| 0 | 0:2, 2:3, 4:8, 6:4 |
| 1 | 0:2, 2:3, 5:8, 6:4 |
| 2 | 1:2, 3:3, 4:8, 7:4 |
| 3 | 1:2, 3:3, 5:8, 7:4 |

- The key is (agent 0 on 4, agent 1 on 5), with def* = 1 in four implementations: model.py, c4x_check, main's
  `k4/rt4_n5_indep.py`, and `k4/sx_indep.py`'s deficit.
- It has 6 maxima of (r′, Λ′). At each, every leaf's bundle threatens both frozen agents, by `k4/sx_f2.py` and by
  a separate computation on `k4/sx_indep.py`'s primitives. So neither Lemma A⁺ nor Lemma B⁺ applies.
- The key (agent 2 on 4, agent 3 on 5) is symmetric and fails the same way.
- DL on the key graph holds at this key, even with plain (T3) edges. From every maximum's state, e.g.
  P_Q = ({4}, {5}, {7}, {1,3}), the move x = 0 → {0,2}, z = 2 → {4}, with no helper, reaches
  ({0,2}, {5}, {4}, {1,3}) with deficit 0.

**Second instance.** n = 4, m = 9, f = 2, ω = 3, from the PR #80 audit. Sets [[0,2,4,8],[1,3,6,7],[2,3,4,5],[5,6,7,8]],
values [[2,4,3,8],[3,8,4,2],[4,8,3,2],[2,3,6,10]].
- The key is (–, 3, –, 8), with def* = 1 by model.py, c4x_check and rt4_n5_indep.
- It has 2 maxima. At each, a leaf threatens both frozen agents, and the free needers are off the path to the leaf.
- A plain (T3) move without helper repairs it: x = 3 → {7}, z = 0 → {8}, deficit −1.

**Further example.** n = 5, m = 12, f = 3, ω = 5. It is one of the coordinator's DL_RT4 failure profiles (branch
`compute/k4-rt4-n5c`, `results/k4_rt4/n5c_FAILURES.md`; instance list `results/k4_sx/f2/rt4_n5c_inst.json`).

| agent | goods: values |
|---|---|
| 0 | 0:2, 2:3, 6:6, 10:10 |
| 1 | 1:3, 4:4, 9:2, 11:8 |
| 2 | 3:3, 5:2, 9:4, 11:8 |
| 3 | 6:2, 7:3, 8:10, 10:6 |
| 4 | 7:2, 8:10, 10:6, 11:3 |

- The key is (agent 0 on 10, agent 2 on 11, agent 3 on 8), with def* = 1 in both of this workstream's implementations.
- None of its 6 maxima of (r′, Λ′) satisfies the hypotheses of Lemma A⁺ or B⁺. All three obstructions occur.
- The repair at this key is a plain (T3) move without helper: x = 0, z = 4 (which needs 10), reaching a key with
  def* = −1. The direct (T3) moves listed by `python3 k4/sx_keygraph.py one ...` show it.

Of the 26 non-completable keys of the n5c profiles, 7 have no maximum to which Lemma A⁺ or B⁺ applies
(`results/k4_sx/f2/rt4_n5c.log`).

**Reproduce.** `python3 attempts/k4_sx_attempts.py`, cases 3a, 3b and 3c (`results/k4_sx/attempts_replay.log`). The
script says which implementation computes each fact. The A⁺/B⁺ verdicts are by `k4/sx_f2.py` (model.py) alone. Case
3a's leaf threats are also computed from `k4/sx_indep.py`'s primitives.
