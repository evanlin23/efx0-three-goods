# LS4 with Phase 2 (d), any junk placement found by exhaustive search, in place of (c)

Workstream `proof/k4-localsearch` (`k4/local_search4.md` §2, §4).

**Approach.** Strengthen Phase 2 as far as possible: accept any assignment of the pool goods to sources that do not value them, provided the result is EFX₀, found by exhaustive search. This drops the dump-plus-solo shape of (c). The question is whether conjecture TP₄ ("a stable state can always be completed") becomes true with (d) in place of (c).

**Counts** (`k4/ls4alg.c`, which has (d) as its fallback). (d) completes states that (c) cannot:
- 1,938 times on the random n = 4 samples with three or four 4-good agents;
- 5,632 times on the exhaustive run for n = 4 with two;
- 839 and 162 times on the n = 5 samples.

It still leaves 20 failures on 21,900,000 random pure n = 4 profiles (`results/k4_ls4_4_sample.log`). Those are states that no move improves and no placement at all completes.

**Where it breaks (n = 4, m = 7).** The dead end of `attempts/k4-ls-dead-end.md` (Proposition 7 of `k4/local_search4.md`): Y = {2} | {6} | {1, 4} | {3, 5}, U = {0}. It admits no placement of the pool good at all, junk or not. So TP₄ with (d) is false as well.

No failing configuration with fewer agents or goods was found. LS4 never fails at n ≤ 3 (exhaustive). Its sampled n = 4 failures have m = 7, 8 or 9. The dead-end search found none at n = 4 with m ≤ 6 (sampled, 424,000 profiles).

Reproduce: `python3 k4/ls4_attempts.py` (the dead-end check: no completion of Y exists).
