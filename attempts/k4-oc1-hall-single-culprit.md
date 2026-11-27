# OC₁: the deficit is not caused by a single dangerous agent (LB⁺'s bad case does not transfer)

Workstream `proof/k4-oc1-hall` (`k4/oc1_hall.md` §6).

**Idea.** At k = 3, LB⁺'s Theorem A says that owner r fails only in the bad case. There, one frozen exposed agent k*
causes the deficit, and k* has a need chain to r. Theorem B then rotates along that chain
(`proofs/lb_last_step.md` §4–§5). The k = 4 analogue for OC₁ would read:

> At every *hard start* (serial-dictatorship picks with no S\* completion, `k4/oc1_hall.md` §2), some unfrozen owner r
> and some frozen agent k have this property: dropping k's safety requirement makes r's deficit (`k4/oc1_hall.md`
> Lemma 2) at most 0 ("k is the only culprit"). Moreover, a need chain k → … → r repairs.

**Result: false as a description of the hard starts.** `k4/oc1_hall/culprit.py`,
`results/k4_oc1_hall/culprit.log`:

| data | hard starts | some (r, single culprit k) | with a need chain k → r | that chain repairs |
|---|---|---|---|---|
| special | 17 | 15 | 14 | 12 |
| screen | 234 | 170 | 160 | 144 |
| logs | 1,470 | 1,236 | 1,222 | 1,200 |
| random n = 4 | 255 | 161 | 156 | 156 |
| random n = 5 | 31 | 15 | 15 | 15 |

So in about 30% of the hard starts (about half at n = 5), every unfrozen owner's deficit needs the demands of two or
more frozen agents removed. One improving chain still repairs every one of them (`chain_shapes.log`). It does so by:
- passing through several frozen agents; or
- unfreezing agents off the chain, whose wanters improve. This is the "u" term of Lemma Ωʳ, `k4/sdc.md` §26.

**Smallest failing configuration.** Every hard start with n = 3 that has two frozen agents and no holder, e.g.
red-key-without-t0 (screen):
- sets [[0,2,5,6],[1,3,4,6],[3,4,5,6]];
- values [[2,3,4,8],[3,5,6,7],[2,3,6,10]];
- order (1, 0, 2), picks (5, 6, 4), frozen {0, 1}.

The only unfrozen owner, 2, has deficit 3. Dropping agent 0's demand alone, or agent 1's alone, leaves a positive
deficit. The repairing chain 1 → 2 (agent 1 takes {1, 3}, agent 2 takes 6) gives agent 2 its top, so agent 0 is no
longer wanted. One chain removes both demands.

**Repro.** `python3 k4/oc1_hall/culprit.py screen` (prints the counts; `NO CULPRIT CHAIN` lines list starts without a
single culprit that has a chain to its owner).

**Consequence.** A Theorem A₄ for OC₁ cannot have the shape "one culprit". The chain lemma has to credit the demands
it removes along the whole chain and off it.
