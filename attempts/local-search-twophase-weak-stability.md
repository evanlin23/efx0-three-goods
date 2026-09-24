# Two-phase local search with weak stability (no rebundles or champion moves in Phase 1)

Workstream `proof/local-search` (`proofs/local_search.md` §5).

**Approach.** Phase 1 stops at a junk-free EFX₀ partial allocation Y that is only *weakly stable*:
- (s1) Y is EFX₀;
- (s2) nobody envies an unallocated good;
- (s3) the envy graph is acyclic;
- (s4) no unallocated good can be added to the bundle of an agent that values it.

Phase 2 then places the unallocated goods U as junk.

**Where it breaks (n = 3, m = 5).** Core {0, 2, 3}, {1, 2, 4}, {0, 1, 2}. Rankings (a, b, c): agent 0 (2, 0, 3), agent 1 (1, 2, 4), agent 2 (1, 0, 2). Y = {2} {4} {1}, U = {0, 3}.
- Agent 1 holds its c (4), with its top 1 and its b 2 alone. Agents 0 and 2 hold their tops.
- The only source is agent 1, since both singletons {1} and {2} are envied by agent 1.
- Junk can only go to sources (Lemma 6). But {0, 3, 4} contains agent 0's b and c.

Y is weakly stable, but agent 0 can drop its top and take {0, 3} (b and c) from the pool. That is a valued rebundle (M1), which the weak version does not apply.

With (s1)–(s4) only, 128 of the 1,172 stable states for n ≤ 3 cannot be completed. With M1 and M2 (champion paths) added to Phase 1, no failure remains up to n = 5; the next failure is `local-search-twophase-m1m2.md`.

Reproduce: `python src/local_search.py twophase 3 --flags="-w -l 5" --jobs=1`
