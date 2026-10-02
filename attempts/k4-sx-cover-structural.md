# Coverage by the repair lemmas with structural hypotheses only (proof/k4-sx)

**Candidate.** K4.SX.COVER in the form first stated in `k4/sx.md` §5, before the n = 4, 400,000-per-core hunt. At every
Z′-maximum of every non-completable f = 1 key, one of the following applies:
- Lemma A;
- Lemma B with path length 1;
- Lemma B′ with path length 1 under (H_B′*): the good y that the (R) leaf gives up is valued by nobody but x;
- Lemma C under (H*): no third agent values a good that τ₁ releases;
- Lemma C′ under (H′*).

These hypotheses are structural, read off the goods. The candidate held on every strict profile with n ≤ 3 and on the
first n = 4 and n = 5 hunts.

**Why it fails.** A third agent may value a good that the swap moves into the owner's bundle without being threatened
by it. The structural hypotheses then fail while the exact ones, (H), (H′) and (H_B′) of `k4/sx.md` §3, still hold: the
new owner's bundle threatens nobody. In the instance below Lemma C applies with the exact (H). The coverage conjecture
is now stated with the exact hypotheses (K4.SX.COV).

**Smallest failing configuration found.** n = 4, m = 9, ω = 2, from the hunt `results/k4_sx/hunt/n4_pure_r400k`
(400,000 random profiles per pure n = 4 core). That hunt has 5 Z′-maxima without a structurally covered lemma, at
keys whose unique Z′-maximum it is. The other two printed instances have the same core, and one has m = 10.

| agent | goods: values |
|---|---|
| 0 | 0:4, 2:5, 4:8, 5:2 |
| 1 | 1:3, 3:4, 4:2, 8:8 |
| 2 | 3:6, 6:2, 7:3, 8:10 |
| 3 (x) | 5:6, 6:3, 7:5, 8:7 |

- The key is (8, 3) with def* = 1. Its unique Z′-maximum has Q_0 = {0, 2}, Q_1 = {1, 4}, Q_2 = {3, 7} and L = {5, 6}.
- The free-valid owners (the leaves) are V = {0, 2}, and the terminals are T = {1, 2}.
- Agent 2 is a θ-b terminal leaf: big-top on 8, with U_2 = {3, 6, 7} ⊆ X_2. So Lemma A does not apply.
- Agent 1 is a terminal whose threat path ends at the leaf 0. Agent 0 is of kind (R): its top 4 is in Q_1, and its
  fourth good 5 is in L. In Lemma B′ the good y = 1 of Q_1 joins x's bundle, and agent 1 values it, so (H_B′*) fails.
- Lemma C with τ₁ = 2, o = 0 and P_x = {5, 7}: P_x is robust for x and meets U_2, but Q_2 ∖ P_x = {3} is valued by
  agent 1, so (H*) fails.
- The exact (H) holds: agent 1 holds {1, 4}, worth 5, and values only 3 (worth 4) in Y = {0, 2, 3, 6}. So Lemma C
  applies, and DL on the key graph holds at the key.

**Reproduce.** `python3 attempts/k4_sx_attempts.py`, case 4: def* by two implementations, and the lemma checks by
`k4/sx_zprime.py`.
