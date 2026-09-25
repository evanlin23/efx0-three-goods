# The owner processed last

**Idea.** LB⁺'s owner is r, the last agent, or k*, whose rotation makes it "go last" in its block. So choose the
owner o first, run Phase 1 on the other agents, and give o whatever of its goods is left (or any part of it, the rest
going to junk), with o's needs taken from its bundle; the state is automatically valid (every good left is below the
pick of every other agent valuing it). Is some owner always valid?

**Where it breaks.** With o taking all its leftover goods, no owner works in 356 of 20,000 random n = 3 runs; with o
taking any subset of them, in 9 of 20,000. Smallest found (n = 3, m = 8): agents 0 = {0, 2, 6, 7} with values
(6, 3, 5, 7), 1 = {1, 4, 6, 7} with (5, 3, 6, 7), 2 = {3, 5, 6, 7} with (3, 8, 4, 10); insertion choices (2, 6, 5).
For each owner o the other two agents take 6 and 7 (or 0 and 7, …) and every choice of o's part fails; brute force
finds 38 EFX₀ allocations with at most one large bundle, e.g. {0, 1, 2, 3} | {4, 6} | {5, 7}.

**Smallest failing configuration**: the one above (n = 3, m = 8; smallest m among the 9 found).
Reproduce: `python3 attempts/k4_c4_attempts.py owner-last`.
