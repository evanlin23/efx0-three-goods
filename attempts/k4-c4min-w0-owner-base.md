# C₄ᵐⁱⁿ with the owner's needs from its base fails at n = 4 (pure), not only at n = 2

Workstream `compute/k4-c4min-hunt` (`k4/c4min_hunt.md` §1.1, §5). Conjecture C₄ᵐⁱⁿ (`k4/c4x.md` §5, PR #36) takes the
owner's needs from its bundle: N_o^X = {g ∈ R_o ∖ X_o : v_o(g) > v_o(X_o)}, which can unfreeze the agents holding goods
the owner needed and give them slots. The natural stronger form takes them from its base, N_o (as at k = 3, and as
LB₄'s `-w0`). PR #36 (`attempts/k4-c4x-variant-spaces.md`, item 1) found that form failing at n = 2 (720 of 189,216
profiles, no completable pre-allocation at all). This note records where else it fails.

**Exhaustive runs of the stronger form** (`k4/c4min_hunt.c -E -w0`, `results/k4_c4min_hunt_w0.log`):

| class | profiles | fail |
|---|---|---|
| n = 2 (5 cores) | 189,216 | 720 (as PR #36) |
| n = 3 (51) | 299,837,376 | 0 |
| n = 4, one / two / three 4-good agents (135 / 309 / 339) | 7,247,232 / 724,847,616 / 34,971,844,608 | 0 |
| n = 4, pure (219) | 1,022,496,473,088 | **26,496**, in 14 cores with m = 8–12 |
| n = 5, one / two 4-good agents (1,735 / 5,468) | 574,615,296 / 80,025,864,192 | 0 |

So the owner's needs from its bundle are needed well beyond n = 2: C₄ᵐⁱⁿ as stated holds on all 26,496 of these
profiles (`results/k4_c4min_hunt_n4_pure.log`), the stronger form on none of them. Per-core counts (in
`results/k4_c4min_hunt_w0_pure_cores.ckpt`; the "fails 20" per core in the `.log` is the number of FAIL lines printed,
capped by `-x`): cores 120, 174, 176, 179, 205, 207, 217: 1,296; 122, 175, 178, 216, 218: 2,592; 208: 3,888; 215: 576
(m = 8 for cores 120, 122; 9 for 174–176; 10 for 178–208; 11 for 215–217; 12 for 218). They are sums of products of
per-agent counts: 6 for an agent (the orders of its three lower goods), 4 for an agent with two private goods (core
215: 576 = 4²·6²). The failures depend on each agent's top good and on its kind (a > b + c), not on the finer type.

**Smallest failing configuration with n ≥ 3: pure n = 4, m = 8** (core 120 of `results/k4_certs_4_pure.json.gz`):
agents {0, 2, 4, 6}, {0, 2, 5, 6}, {1, 3, 4, 7}, {1, 3, 5, 7}, each of type (2, 3, 8, 4) in the order of its set, i.e.
a > b + c (8 > 4 + 3). Goods 4 and 5 are each the top of two agents; 0, 1, 2, 3, 6, 7 are shared by two agents.
f* = 2 = σ + 2 (σ = 0), 36 min-frozen pre-allocations. With the owner's needs from its base, every one of them has
deficit ≥ 1 and none is completable even with protecting junk goods (the exact test of `k4/c4x.md` §1); with them from
its bundle, 32 of the 36 have deficit ≤ 0. A second instance, pure n = 4, m = 11 (core 217): {3, 6, 7, 8},
{0, 2, 6, 10}, {1, 5, 9, 10}, {4, 7, 8, 9} with values (2, 8, 3, 4), (2, 3, 8, 4), (3, 4, 8, 2), (2, 3, 4, 8): 46
min-frozen pre-allocations, 0 with deficit ≤ 0 and none completable from the base, 42 with deficit ≤ 0 from the bundle.

Both instances are confirmed by three implementations (the brute force `k4/c4min_brute.py`, `k4/c4min_hunt.c -1`,
`k4/c4x.c -1s -R -a` of PR #36), with and without `-w0`:
```
python3 attempts/k4_c4min_w0_replay.py      # prints ALL CONFIRMED
```
