# Peel, insert, dump everything into one bundle (PID)

**Idea.** Build the allocation by peeling (L2, rule R1: an agent with at most two goods left takes its favourite remaining good as a singleton) and, when stuck in a core state, by insertion (L10: some agent takes its top). Every agent is safe at that point, because the goods it prefers to its own were picked earlier and are singletons. Then put every good nobody picked into one bundle, as in L2's "the last agent takes everything", with the owner chosen freely. The hope was that the leftover goods are "junk" and the single dump is the large bundle of conjecture D.

**Where it breaks.** The leftovers cannot all go into one bundle: the dump makes its owner's good non-alone, and an inserted agent whose b and c are both leftovers is then unsafe. Searching over every peeling order, every insertion choice and every owner (`src/peel_search.py --dump`) still fails.

Smallest failing configuration: n = 2, m = 4, agents (a > b > c) `(0, 1, 2)` and `(0, 1, 3)` (goods 2 and 3 private). Every run gives one agent good 0 (its top) and the other good 1 (its b, case B: it needs 0 alone), leaving {2, 3}. Say agent 0 holds 0. Dumping {2, 3} on agent 0 gives {0, 2, 3}, so 0 is no longer alone and agent 1 is unsafe. Dumping on agent 1 gives {1, 2, 3}, which holds agent 0's b = 1 and c = 2 together in a bundle of three goods, so agent 0 (holding only its top) is unsafe (case T fails). The other assignment is symmetric. All 36 profiles of this core fail. The EFX₀ allocation {0, 2}, {1, 3} splits the leftovers.

Counts (all profiles of all connected cores): n = 2, m = 4: 36 of 36 fail; n = 3, m = 5: 274 of 648; n = 3, m = 6: 216 of 216; n = 4, m = 6: 4,685 of 20,736; n = 4, m = 7: 6,480 of 10,368.

**What replaced it.** PIJ: leftovers first fill free slots (a singleton that nobody needs alone takes one more good, an empty bundle takes two), and only the overflow goes into one large bundle. With a search over the choices this succeeds on every profile of every connected core with n ≤ 5 and with n = 6, m ∈ {9, 10, 11} (`src/peel_search.py`). The deterministic version is construction LB (`src/construct.py`).

Reproduce: `cd src && python peel_search.py 2 4 --dump` (and `python peel_search.py 3 5 6 --dump`, `python peel_search.py 4 6 7 --dump`).
