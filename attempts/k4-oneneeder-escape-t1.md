# The swap from an x-alone triple needs a stuck state (workstream proof/k4-oneneeder)

Context: `k4/oneneeder.md` §4. At a one-needer state (f = 1, x big-top, z the only needer of x's good g) with an x-alone
triple (o, X, c), Propositions C and D give the swap of Corollary 8.2 of `k4/dl13.md` to a state of deficit ≤ 0 when
o = z (and u_z(X) = 0), or when o ≠ z has an *escape*. Two candidate strengthenings fail.

**Candidate 1 (per triple).** "At every T1-stuck one-needer state with def = 1, x big-top and an x-alone triple
(o, X, c) with o ≠ z, o has an escape at that triple." Fails at n = 4, m = 11:

- agents 0: (10:8, 0:4, 2:3, 6:2) = x, big-top on 10; 1: (10:8, 1:4, 5:3, 9:2) = z; 2: (7:8, 3:6, 8:4, 6:1);
  3: (7:8, 9:6, 4:4, 8:3) = o (sets [[0,2,6,10],[1,5,9,10],[3,6,7,8],[4,7,8,9]], values [[4,3,2,8],[4,3,2,8],
  [6,1,8,4],[4,8,3,6]]: core (m = 11, idx 8) of `results/k4_certs_4_pure.json.gz`, profile 72,72,145,113);
- P = ({10}, {1}, {3,7}, {4,9}): f = 1, ω = 4, J = {0,2,5,6,8}, def(P) = 1, T1-stuck, not at the T3 stage (a (T2)
  move of agents 2 and 3, e.g. to {7} and {8,9}, gives deficit 0 with z owning six goods);
- the triple (3, X = {0,2,4,8,9}, c = 6) is x-alone, and o = 3 has no escape there: its top 7 is in agent 2's base, so
  its need-free bases outside L = {0,2,6} are the rich pairs {4,9}, {8,9}, both inside Y = X + c.

Other triples of the same state have escapes. The state-level statement with "T1-stuck" (Candidate 3) survives this
instance and every n = 3 state, but fails at n = 4 as well.

**Candidate 2 (state level, no stuckness).** "At every one-needer state with def > 0, x big-top and an x-alone triple,
Corollary 8.2 applies (with at most one helper)." Fails at n = 3, m = 7:

- agents 0: (3:8, 2:4, 0:3, 1:2) = z; 1: (6:8, 4:6, 2:4, 5:3) = o; 2: (3:8, 5:4, 6:3, 4:2) = x, big-top on 3
  (sets [[0,1,2,3],[2,4,5,6],[3,4,5,6]], values [[3,2,4,8],[4,6,3,8],[8,2,4,3]]: core (m = 7, idx 0) of
  `results/k4_certs_3.json.gz`, profile 34,99,213);
- P = ({0,1}, {2,4}, {3}): f = 1, ω = 2, J = {5,6}, def(P) = 1; the triples (1, {2,4,5}, 6) and (1, {2,4,6}, 5) are
  x-alone; o = 1 values all of x's lower goods {4,5,6} (its top is 6); its only good outside L is 2, and {2} is not
  need-free: no escape, and no swap of Corollary 8.2 reaches a smaller deficit;
- P is not T1-stuck: o re-bases to its top {6} (a lower good of x, which protects x), and z then owns every other good:
  deficit −1. This is the mechanism a proof of the escape has to turn into a contradiction.

**Candidate 3 (state level, T1-stuck: Conjecture ES as first stated).** "At every T1-stuck one-needer state with
f = 1, def = 1, x big-top and an x-alone triple, Proposition C applies at a triple with owner z or a triple with owner
o ≠ z has an escape." True at every such state of the exhaustive n = 3 run (244,560 states), but false at 10 states of
#53's n = 4, 5 catalogues (`results/k4_oneneeder/t1_cat_*.log`). Smallest, n = 4, m = 9:

- agents 0: (7:10, 2:6, 1:3, 0:2) = x, big-top on 7; 1: (5:8, 2:7, 4:4, 8:2) = o; 2: (6:7, 3:6, 4:5, 5:3);
  3: (7:8, 8:4, 3:3, 6:2) = z (sets [[0,1,2,7],[2,4,5,8],[3,4,5,6],[3,6,7,8]], values [[2,3,6,10],[7,4,8,2],[6,5,3,7],
  [3,2,8,4]]: core (m = 9, idx 0) of `results/k4_certs_4_pure.json.gz`, profile 7,196,164,44, a record of #53's
  `results/k4_gap/gap_n4_pure_s4000.json.gz`);
- P = ({7}, {2,8}, {4,5}, {3,6}): f = 1, ω = 2, J = {0,1}, def(P) = 1, T1-stuck, not at the T3 stage (the key has
  states of deficit 0, e.g. ({7}, {5}, {6}, {8}));
- the x-alone triples are (1, {0,2,8}, 1) and (1, {1,2,8}, 0); o = 1 holds the lower good 2 of x, and its top 5 is in
  agent 2's base: o has no escape, and **no** move of x, z and at most one other agent lowers the deficit (so no swap of
  Corollary 8.2 with at most one helper). The 30 min-frozen states of smaller deficit with z on {7} all move both 1 and 2
  (1 takes a base containing its top 5, 2 a base without 5): a chain of two helpers.

So at T1-stuck states the one-helper conclusion itself fails; the T3-stage hypothesis (def(P) = def*(κ)) is what has
to exclude this state, whose key has def* = 0.

Counts on `k4/dl13.md` §1's profiles (one-needer states with def > 0, x big-top and an x-alone triple; scratch analysis
reproduced by the script below for the two instances): at the T3 stage 1,009 states, all with Proposition C or D and
Corollary 8.2; T1-stuck but not at the T3 stage 1,658, all with Proposition C or D; not T1-stuck 4,018, of which 1,607
have neither and no Corollary 8.2 swap. Per triple with o ≠ z: 84 T1-stuck triples (n = 4) without an escape at that
triple.

Replay of all three instances, both implementations (`k4/oneneeder_check.py` on `k4/suite/model.py`, and an
implementation in the script that enumerates base maps and computes the removal-only deficit from its definition):
`python3 attempts/k4_oneneeder_attempts.py`.
