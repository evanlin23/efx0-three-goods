# Two uncoupled free agents as owners, no rotation (Claim X)

**Idea** (`k4/p3.md` §5, workstream proof/k4-p3). In the two-owner framework, the failures of "two owners, no rotation"
on the suite come from the owners' picks (a junk good threatening together with both owners' picks). Claim X: in the
Phase 1 state (index insertion, no upgrade) of a (4, 3) core, any two free agents whose picks no frozen agent values
are a valid pair of owners, i.e. the bases extend to an EFX₀ allocation in which every other agent holds at most two
goods. It held on 1,714 of the 1,715 states with such a pair (suite, screen, certified cores, random cores;
`k4/p3/claim_x.py`, fixed sampler, `results/k4_p3x/claim_x.log`).

**Where it breaks.** The owners' views of each other's bundles. Smallest failure found: a certified (4, 3) core with
n = 4, m = 8 (`k4_certs_4_n4_3_p3.json.gz`), strict balanced types, every good with at most two valuers:

| agent | goods (values) | ranking |
|---|---|---|
| 0 | 0 (3), 1 (10), 2 (6), 6 (8) | 1 > 6 > 2 > 0 |
| 1 | 1 (8), 2 (4), 5 (6), 7 (3) | 1 > 5 > 2 > 7 |
| 2 | 3 (7), 4 (6), 5 (10), 6 (2) | 5 > 3 > 4 > 6 |
| 3 | 3 (2), 4 (4), 7 (3) | 4 > 7 > 3 |

Phase 1: agent 0 takes 1; agent 1 (lost 1) takes 5; agent 2 (lost 5) takes 3; agent 3 (lost 3) takes 4. Junk 0, 2, 6, 7.
Agents 0 and 1 are frozen (agent 1 needs 1, agent 2 needs 5); agents 2 and 3 are free and their picks 3, 4 are valued by
no frozen agent. Agent 0 (holding 10) is threatened by {6, 2} and {6, 0}, agent 1 (holding 6) by {2, 7}, so with owners
2 and 3 the colouring is forced up to swapping: 6, 7 to one owner, 0, 2 to the other. Owner 3 with {4, 0, 2} sees
{3, 7} in X_2 = {3, 6, 7} (5 > 4); owner 2 with {3, 0, 2} sees {4, 6} in X_3 = {4, 6, 7} (8 > 7). The two owners value
each other's picks, and the frozen agents' threats push each owner's own junk into the other's bundle. In fact no EFX₀
allocation keeps these four bases at all (brute force over the 4⁴ placements of the junk), so a rotation is required.

Since every good has at most two valuers, the failure is not specific to p = 3.

**Refinement: Claim X′** (also neither owner values the other's pick; `k4/p3/claim_x.py --mutual=1`). It held on
7,110 of the 7,111 states with such a pair and failed on one, a certified (4, 3) core with n = 4, m = 9 (`k4_certs_4_n4_3_p3.json.gz`,
found among 20 profiles per n = 4 core):

| agent | goods (values) | ranking |
|---|---|---|
| 0 | 0 (2), 2 (8), 6 (7), 7 (4) | 2 > 6 > 7 > 0 |
| 1 | 1 (6), 4 (5), 7 (4), 8 (8) | 8 > 1 > 4 > 7 |
| 2 | 3 (2), 5 (3), 8 (4) | 8 > 5 > 3 |
| 3 | 5 (10), 6 (7), 7 (4), 8 (2) | 5 > 6 > 7 > 8 |

Phase 1: agent 0 takes 2 (private); agent 1 is the next leader and takes 8; agent 3 (lost 8, favourite 5 still there)
takes 5; agent 2 (lost 8 and 5) takes 3. Junk 0, 1, 4, 6, 7. Agents 1 and 3 are frozen (agent 2 needs 8 and 5); the
free agents 0 and 2 hold private picks, so they are uncoupled in every sense. Agent 1 is **flat** (5 + 4 > 8) and its
three lower goods 1, 4, 7 are all junk, so one of them must go to a slot; but the only free agents are the two owners,
and the only terminal of agent 1's block (agents 1, 3, 2) is agent 2, an owner. This is exactly the bad case that
Lemma F₂'s count leaves (`k4/p3.md` §5): a flat leader whose block's terminal is used as an owner. Again no EFX₀
allocation keeps the four bases at all.

**What would be needed.** A Theorem A₂ hypothesis of LB⁺'s kind: every flat frozen leader with three junk lower goods
has a terminal in its block other than the two owners, and the owners' views are bounded; otherwise a rotation (in this
example, along the need chain 1 → 2, giving agent 1 a two-good base, is the natural candidate).

Reproduce: `python3 k4/p3/claim_x_cex.py X` and `python3 k4/p3/claim_x_cex.py "X'"` (brute force over all placements of
the junk, raw definition; `results/k4_p3x/claim_x_cex.log`); `python3 k4/p3/claim_x.py cores --count=10000 --files=4_n4
--per=20 --seed=11 --mutual=1` finds the second (`results/k4_p3x/claim_x_mutual.log`).

Claim X's example is found by `python3 k4/p3/claim_x.py cores --count=400 --seed=7` (fixed sampler;
`results/k4_p3x/claim_x.log`).

