# The generalized path move to an (R) leaf with its fourth good in the pool (proof/k4-sx)

**Candidate.** `k4/sx.md` §3, Lemma B without its exception. Along a threat path from a terminal τ to a leaf o of a
Z′-maximum at a non-completable f = 1 key (g, x), the following happens: every agent on the path takes its threatener's
pair, τ takes g, and x becomes a valid owner of o's whole bundle X_o (C = ∅).

**Why it fails.** Let the leaf o be of kind (R): it holds {p, q} ⊆ R_o ∖ {a}, its threatener holds a, and its fourth
good s lies in the pool. o then receives {a, y} with y ∉ R_o, worth only a. Meanwhile X_o still holds p, q and s, worth
p + q + s > a, so X_o threatens o. Lemma B′ handles the case: o takes {a, s}, and y joins x's bundle in place of s.

**Smallest failing configuration found.** n = 4, m = 8, ω = 1, from the n = 4 hunt `results/k4_sx/hunt/n4_pure_r40k`.

| agent | goods: values |
|---|---|
| 0 (o) | 0:4, 4:6, 5:3, 6:8 |
| 1 (x) | 1:6, 4:8, 5:3, 7:10 |
| 2 (τ) | 2:3, 3:2, 6:4, 7:8 |
| 3 | 2:6, 3:3, 6:8, 7:10 |

- The key is (7, 1) with def* = 1.
- The Z′-maximum has Q_0 = {0, 4}, Q_2 = {1, 6}, Q_3 = {2, 3} and L = {5}. The threats run 3 → 2 → 0 → x.
- Agent 0 is of kind (R): a = 6 is held by agent 2, and s = 5 lies in L.
- After the plain move agent 0 holds {1, 6}, worth 8 to it, while X_0 = {0, 4, 5} has θ_0(X_0) = 4 + 6 = 10 > 8. So x
  is not a valid owner of X_0.
- The state reached still has deficit −1 through another owner. What fails is the proof's choice of owner, not the
  move. Lemma B′ gives x a valid bundle: agent 0 takes {6, 5}, and x owns {0, 1, 4}.

**Reproduce.** `python3 attempts/k4_sx_attempts.py`, case 2 (two implementations for def*).
