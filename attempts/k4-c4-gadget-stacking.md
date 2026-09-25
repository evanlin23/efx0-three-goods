# Stacking hard gadgets to force more rotations (an attempt to refute the bound of three)

**Idea.** If a core needs two nested rotations under LB₄ʳ with index insertion, several copies of it processed in
separate blocks (joined into one connected core through a shared junk good) might need a rotation per copy, and then
more than three rotations: a counterexample to Theorem C₄ as stated for LB₄ʳ.

**Where it breaks.** The copies share slack: a rotation in one copy frees slots that absorb the other copies' excess,
and the owner's bundle grows instead. For each of the 96 n = 3 profiles (one leaf each) where index insertion with
every policy and one rotation fails (`-i0 -u3 -r1 -w1 -c1`, `results/k4_lb4_variants.log`), joining 2, 3 or 4 copies
through the leader's private junk goods gives a core on which **one** rotation succeeds (checked with `lb4.c` compiled with MAXN = 16).
The same holds for a 4-agent core with an earlier-block deficit (`attempts/k4-c4-exposure-counting.md` case 3's
mechanism): 1 to 4 copies need exactly one rotation, and the large bundle grows (3, 4, 5, 6 goods). So this construction does not raise the rotation depth; it
also illustrates why a counting proof must be global (across blocks), not per block.

**Smallest configuration**: agents 0 = {0, 1, 4, 5} with values (1, 4, 6, 8), 1 = {2, 3, 4, 5} with (3, 5, 7, 6),
2 = {2, 3, 4, 5} with (2, 3, 4, 8): index insertion needs two rotations; two copies (n = 6, m = 11, copy 2's private
good 1 identified with copy 1's good 0) need one.
Reproduce: `python3 attempts/k4_c4_attempts.py gadget-stacking`.
