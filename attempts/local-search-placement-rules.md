# Simple rules for Phase 2 (junk placement) that fail

Workstream `proof/local-search` (`proofs/local_search.md` §6.2). Each rule below is a candidate for proving the placement conjecture TP in a simple form. Each one fails already at n = 4. What works is a placement read off a maximum matching, with a different source for each dirty good; it always exists once Phase 1 includes augmented envy cycles (Theorem C, Claim 4).

1. **All junk into one source** (the shape of conjecture D's large bundle). Fails at n = 4: 24 of 62,058 stable states; n = 5: 2,464.
   Example (n = 4, m = 6): rankings (a, b, c) (0,1,4) (2,3,5) (0,3,2) (2,1,3); Y = {0} {2} {3} {1}; U = {4, 5}.
   - The sources are agents 2 ({3}) and 3 ({1}).
   - {1, 4} is agent 0's bottom pair and {3, 5} is agent 1's, so neither source can take both goods.
   - Placing 4 with agent 2 and 5 with agent 3 works.
   Reproduce: `python src/local_search.py twophase 4 --flags="-1 -l 3" --jobs=1`
2. **Every unallocated good has a clean source** (no a-holder's bottom pair would be completed inside a bundle of ≥ 3 goods). Fails at n = 4: 56 stable states, all with |U| = 1, where the good must sit alone next to a single good.
   Allowing |U| = 1 still fails at n = 5 (436 states).
   Example: rankings (0,5,6) (0,2,3) (4,1,2) (5,1,4) (4,3,5); Y = {5} {0} {4} {1} {3}; U = {2, 6}.
   - Good 2 is dirty at both sources {1} and {3}.
   Reproduce: `python src/local_search.py twophase 5 --flags="-G -l 3"`
3. **Counting: |U| ≤ number of sources holding at most one good.** Fails at n = 4: 4,780 stable states.
   Example: rankings (0,2,3) (1,2,4) (1,2,5) (0,1,2); Y = {0} {1} {5} {2}; U = {3, 4}.
   - There is one one-good source, agent 2 ({5}).
   - It can take both goods: {3, 4, 5} is fine.
   Reproduce: `python src/local_search.py twophase 4 --flags="-c -l 3" --jobs=1`
