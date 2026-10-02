# Failed: ZMOVE from every pool-optimal configuration whose free threats form a forest

Workstream `proof/k4-zmove-hall` (`k4/zmove_hall.md` §2). REFUTED (a candidate strengthening of ZMOVE, not a ledger
claim).

**Statement tried.** For every key κ with def*(κ) > 0 and every configuration Q at κ that is pool-optimal and whose
threats among the free agents have no cycle (the two properties of a Z′-maximum that Lemma F / F⁺ of `k4/sx.md` derives
from it and that a Hall argument would use first), some (T3⁺) move with at most one helper from P_Q reaches a state of
deficit ≤ 0.

If it held, a proof of ZMOVE could use pool-optimality and the forest only, and never the maximality of (r′, Λ′)
itself. It fails, so the argument has to use the maximality of r′ (as the proof of Proposition S1c₃, §3, does in its
Case (ii)). It also shows that the forest of Lemma F⁺ alone does not force a repair.

**Smallest failure found** (n = 5, m = 12, f = 2, ω = 4; compute/k4-rc's core 4515, one of its 1,076 profiles):
`{"sets": [[0,2,4,8],[1,8,10,11],[3,9,10,11],[4,5,6,7],[5,6,7,9]], "vals": [[4,3,8,2],[8,3,6,10],[2,8,3,4],[8,2,3,4],[3,2,4,8]], "m": 12}`
- key κ: agent 0 frozen on 4, agent 4 frozen on 9; def*(κ) = 1;
- the state P = ({4}, {1,8}, {10,11}, {6,7}, {9}), with def(P) = 1 = def*(κ), carries the configuration
  Q = {1: {1,8}, 2: {10,11}, 3: {6,7}}, L = {0,2,3,5}: pool-optimal, threats 1 → 0, 2 → 1, 3 → 4 (no cycle; leaves 1
  and 3); its potential is (r′, Λ′) = (2, 18). Agent 1 is of kind (R) (a = 11, s = 10 ∈ Q_2), threatened by agent 2;
- no (T3⁺) move with at most one helper from P reaches deficit ≤ 0;
- the Z′-maximum of κ is ({4}, {1,11}, {3,10}, {6,7}, {9}) with potential (3, 21) (agent 1 robust on {1,11}), and it has
  such a move (Lemma C′⁺'s shape: one (T3) move without helper, x = agent 0 the new owner).

**Extent** (`k4/zmh_classes.py`, `results/k4_zmove_hall/classes_*.log`): on compute/k4-rc's 369 + 1,076 profiles and
PR #80's n = 4 hunts, 42 of 12,693 pool-optimal configuration states lack a move (all at core 4515), while every state of
a configuration that maximizes r′ alone (16,171 states) has one. At n = 3 (every 10th profile of compute/k4-cover's
screen) and in PR #80's n = 4 hunts every state of every key with def* > 0 has a move.

**Reproduce** (both implementations, seconds): `python3 attempts/k4_zmh_attempts.py`
(`results/k4_zmove_hall/attempts_replay.log`). Implementation A is `k4/zmh_lib.py`; implementation B is main's repo-free
`k4/rt4_n5_indep.py` for the deficits and move kinds, with the configuration over P, its pool-optimality and its threat
digraph written out in the replay script.
