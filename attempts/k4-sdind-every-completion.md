# Attempt: insert one agent into an arbitrary completion of the sub-instance (SD-order induction)

Workstream `proof/k4-sd-induct` (`k4/sd_induct.md` §1–§2). Failed; kept for the record.

**Idea.** Grow the instance one agent at a time along a serial-dictatorship order. By Lemma D of the note, deleting
any agent u together with its pick Y_u leaves the other picks and the junk unchanged, so a one-absorber completion
X′ of I − u − Y_u is a map from the same junk J to the other agents. Hope: for a suitable class of u (the last agent
of π, i.e. one whose pick nobody wants; or the first, i.e. one holding its top), *every* such X′ extends to a
one-absorber completion of I by moving a bounded number of junk goods.

**Result** (`k4/sdind/e1_delete.py`, `results/k4_sdind/e1_delete.log`; screen set, n ≤ 5, every SD outcome with a
one-absorber completion).
- Deleting the last agent: the sub-instance often has no one-absorber completion at all, although I has one (28 of
  646 cases). When it has one, every X′ is within distance 2 in only 337 of 618 cases. The worst distance is 4.
- Deleting the first agent: every X′ is within distance 1 in only 521 of 716 cases, and within distance 2 in 667.
- Deleting an agent that is both (it holds its top and nobody wants its pick) works much better. Every X′ is within
  distance 2 in all 120 cases whose sub-instance extends. But see `attempts/k4-sdind-both-one-absorber.md`: the
  sub-instance can extend while I does not.

**Why.** The induction hypothesis hands over an arbitrary completion. The new last agent wants earlier picks, which
must then be singletons. The new first agent's danger sets must stay out of the absorber's bundle, and that bundle
was chosen without knowing them. The induction has to carry a choice, as in K4.IND.X (`k4/induct.md` §2).

**Smallest failing configuration** (deleting the last agent, worst distance 4): Q2 (n = 4, m = 8):
- goods and values: {0, 1, 3, 4} (2, 3, 10, 6), {2, 3, 6, 7} (2, 8, 3, 4), {2, 5, 7} (2, 4, 3), {4, 5, 6, 7} (4, 8, 2, 3);
- order (0, 3, 2, 1), picks (3, 6, 7, 5); agent 1's pick is wanted by nobody;
- I has 3 one-absorber completions and I − 1 − Y_1 has 23; one of the 23 is at distance 4 from all three.

Reproduce (independent brute force): `python3 attempts/k4_sdind_attempts.py every`.
