# LB₄ in the shape of LB⁺: fixed insertion order, owner r, else one rotation

**Idea.** Carry LB⁺ (`proofs/lb_last_step.md`) to four goods literally: serial dictatorship with priority to agents
that lost a good (LB's key), insertion by index (Theorem C of LB⁺ allows any insertion order), upgrades that shrink an
agent's needs (the k = 4 form of "b takes c"), owner r (the last-processed agent that is not upgraded) tested exactly,
and otherwise one rotation along a need chain. The tested version is more permissive than LB⁺: the rotation may start
at any frozen agent, use any chain, and give the rotated agent any subset of its free goods (`k4/lb4.c -i0 -u1 -o2 -r1`).

**Where it breaks.** Already at n = 2 (2 of the 5 cores; `k4/lb4_run.py results/k4_certs_2.json.gz -i0 -u1 -o2 -r1`),
and in 30 of the 51 cores with n = 3 (6,065,876 of 299,837,376 profiles).

**Smallest failing configuration** (n = 2, m = 5). Agents 0 = {0, 2, 3, 4} and 1 = {1, 2, 3, 4} (goods 0 and 1
private), values 0: (1, 4, 6, 8) and 1: (2, 4, 5, 8) on the goods in that order. Both rank 4 > 3 > 2 > own private.
Agent 0 is inserted and takes 4; agent 1 takes 3 and needs 4. Agent 1's upgrade {3, 2} (worth 9 > 8) removes its need,
which unfreezes agent 0: junk {0, 1}, one slot (agent 0), so ω = 1. Owner 0: X_0 = {4, 0, 1}, and agent 1 values
{4, 1} at 10 > 9. Owner 1 (upgraded, tried by LB₄ though not by this variant) fails too: agent 0 keeps one private good
and values {3, 2} at 10 above {4, private}. No agent is frozen, so there is nothing to rotate. The EFX₀ allocations
with at most one large bundle are {0, 2, 3} | {1, 4} and {2, 3} | {0, 1, 4} (brute force).

**Why.** At k = 3 an upgraded agent holds {b, c} and is envy-free (a < b + c). At k = 4 the upgraded pair {b, c} can be
worth less than a + d, so the upgraded agent is itself threatened by a large bundle containing a and d. Here the upgrade
is harmful; inserting agent 1 first, or not upgrading and rotating instead, works.

Reproduce: `python attempts/lb4_variants.py lbplus-shape`.
