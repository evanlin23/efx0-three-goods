# One rotation for at most one 4-good agent (Conjecture C₄¹ as stated in `k4/c4.md` §6.2)

**Claim tried.** For every core with at most one 4-good agent q and every run of Phase 1, after upgrades some free
agent is a valid owner, or one rotation (any frozen k, any need chain, any O) gives a valid pre-allocation that needs
no owner or has a valid owner. The evidence was n ≤ 4, where every strict profile and every insertion sequence passes
with envy-free upgrades, every owner and one rotation (`lb4.c -i1 -u2 -o0 -r1 -w0 -c0`, `results/k4_c4_variants.log`).

**It fails at n = 5**, whatever the conventions:
- `lb4.c -i1 -u2 -o0 -r1 -w0 -c0` (the conjecture's own search) on the 1,735 certified cores with n = 5 and one
  4-good agent: 140 failing (run, profile) pairs in 5 cores (m = 8, 9, 10).
- With the owner's needs from its bundle, which also gives a rotated agent with a one-good base a slot, as in PR #35's
  definition (`-w1`): 8 pairs in 2 cores. With chains that may end at upgraded agents and all three upgrade policies
  (`-u3 -o0 -r1 -w1 -c1`, LB₄ʳ with one rotation): 2 pairs in the core m = 8 and 4 in the core m = 9.
- With index insertion (`-i0 -u3 -o0 -r1 -w1 -c1`): the core m = 9 still fails (4 profiles).
- Two nested rotations (`-r2 -w1 -c1`, every insertion sequence) succeed on all five cores, and so do LB₄ʳ
  (`-u3 -r3`) and LB₄ (`-i2`).

**Mechanism** (the core m = 9, index insertion; agent 2 = q, values 8, 4, 3, 2 on its goods 7, 8, 6, 2). Phase 1 is a
single block. Agent 0 takes 7, q's top. q takes 8, which the 3-good agents 1 and 4 lose. Agent 3, processed last, is
r. Agent 0 (the leader) is frozen and exposed, and its only need chain ends at q. q is free and exposed, and
protecting itself uses its own slot, which is the only slot other than r's. So owner r fails: one slot, two agents to
protect (A₄ᵀ's case (Tb)). Owner q fails too: its window J ∪ {8} exposes the frozen agents 1 and 4, which lost 8 to q,
and they need two goods kept out while only r's slot is left. No single rotation creates enough room; two do.

**Smallest configuration.** n = 5, m = 9, sets [[0,3,7],[1,5,8],[2,6,7,8],[3,4,5],[4,6,8]], values
[[2,3,4],[2,4,3],[2,3,8,4],[2,3,4],[4,2,3]] (values listed in the order of each agent's goods), index insertion. There
is no failure at n ≤ 4. The every-sequence failure also occurs at m = 8: [[0,2,4,7],[1,2,3],[1,5,6],[3,5,7],[4,6,7]],
values [[2,8,3,4],[3,4,2],[2,4,3],[2,4,3],[2,4,3]], processing order 1 0 3 4 2.

**Checks.** The independent tracer `k4/c4tools/c4trace.py` finds, for the m = 9 profile and each upgrade policy, no
valid owner and no working single rotation under all four conventions (owner's needs from its base or its bundle;
rotated one-good base with or without a slot), and finds a working pair of nested rotations. Brute force over all 5⁹
allocations (`k4/lb4_brute.py`): 167 EFX₀ allocations with at most one bundle of more than 2 goods, so K4.D holds.

Reproduce: `python3 attempts/k4_c4one_attempts.py` (about 20 s).
