# Local search with the four elementary moves only

Workstream `proof/local-search` (`proofs/local_search.md` §2–§4).

**Approach.** Keep an EFX₀ partial allocation of a core and use only the moves E (fill an empty bundle), S (swap for an envied pool good), R (rotate an envy cycle) and A (add a pool good to a bundle). The potential is (sum of levels, number of allocated goods). Theorem A shows that these moves never get stuck on a *junk-free* state, i.e. one where every allocated good is valued by its holder. E and A create junk, however, and junk is where the search stops.

**Where it breaks (smallest configuration: n = 2, m = 4).** Core {0, 1, 2}, {0, 1, 3} (a β = 1 cycle). Rankings (a, b, c): agent 0 (0, 1, 2), agent 1 (0, 3, 1). State: agent 0 holds {0}, agent 1 holds {2, 3}, and the pool is {1}.
- The state is EFX₀. Agent 0 holds its top, and its lower goods 1 and 2 are apart. Agent 1 holds its b (3) plus agent 0's c (2) as junk, and its top 0 is alone.
- Adding good 1 to agent 0 makes 0 non-alone, and agent 1 needs 0 free.
- Adding good 1 to agent 1 gives {1, 2, 3}, a bundle of three goods that contains agent 0's b and c.
- Nobody envies good 1, and the only envy edge is 1 → 0, so there is no cycle.

The fix takes a good away from its holder that the holder does not value: agent 0 takes {1, 2} (its b and c, with 2 from agent 1's junk) and releases 0. Agent 1 then swaps for 0, and the allocation completes. This is the rebundle move U.

All 8 stuck states (6 of the 36 profiles) are of this kind. For n = 2, m = 3 nothing gets stuck.

Reproduce: `python src/local_search.py allstates 2 --flags="-m ESRA -l 3" --jobs=1`
