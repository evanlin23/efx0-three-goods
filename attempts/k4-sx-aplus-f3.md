# Lemma A⁺ does not reach every non-completable key at f ≥ 2 (proof/k4-sx)

**Candidate.** At every key κ with f ≥ 2 and def*(κ) > 0, some configuration maximizing (r′, Λ′) at κ satisfies the
hypotheses of Lemma A⁺ (`k4/sx.md` §6):
- a free-valid owner o whose bundle X_o threatens exactly one agent, the frozen x;
- a need chain x = w₀ → w₁ → … → w_j of frozen agents (w_i needs φ(w_{i−1})), with o needing φ(w_j);
- θ_o(X_o) ≤ v_o(φ(w_j)).

Lemma A⁺ would then give a (T3⁺) neighbour with def* ≤ 0.

**Why it fails.** In one of the cases below, the free-valid owners' bundles threaten two frozen agents. In the other, the
owner that needs the end of the chain is threatened by its own bundle once it holds that good: the f ≥ 2 analogue of
θ-b.

**Smallest failing configuration found.** n = 5, m = 12, f = 3, ω = 5. It is one of the coordinator's DL_RT4 failure
profiles (branch `compute/k4-rt4-n5c`, `results/k4_rt4/n5c_FAILURES.md`; instance list
`results/k4_sx/f2/rt4_n5c_inst.json`).

| agent | goods: values |
|---|---|
| 0 | 0:2, 2:3, 6:6, 10:10 |
| 1 | 1:3, 4:4, 9:2, 11:8 |
| 2 | 3:3, 5:2, 9:4, 11:8 |
| 3 | 6:2, 7:3, 8:10, 10:6 |
| 4 | 7:2, 8:10, 10:6, 11:3 |

- The key is (agent 0 on 10, agent 2 on 11, agent 3 on 8), with def* = 1 in both implementations.
- None of its 6 maxima of (r′, Λ′) satisfies the hypotheses of Lemma A⁺.
- DL on the key graph with (T3⁺) ∪ (T4) edges holds at this key: a role swap of agent 4 (which needs 10) with agent 0,
  with agent 1 as the owner (see `k4/sx.md` §6). The direct (T3) moves listed by
  `python3 k4/sx_keygraph.py one ...` show it.

Of the 26 non-completable keys of the n5c profiles, 7 have no maximum to which Lemma A⁺ applies
(`results/k4_sx/f2/rt4_n5c.log`).

**Reproduce.** `python3 attempts/k4_sx_attempts.py`, case 3: def* by two implementations, and Lemma A⁺'s hypotheses
by `k4/sx_f2.py`.
