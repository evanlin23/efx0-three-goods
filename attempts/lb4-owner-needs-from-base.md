# LB₄ with the owner's needs taken from its base (as at k = 3)

**Idea.** In LB⁺ the owner's needs are those of its pick. Keep this at k = 4, and search everything else: every
insertion sequence, every upgrade policy, every owner and completion, one rotation (`k4/lb4.c -i2 -u3 -r1 -w0`).

**Where it breaks.** Nowhere for n ≤ 3 and nowhere with n = 4 and at most three 4-good agents. On the pure n = 4
cores it fails in 13 of 219 (5,040 of 1.02·10¹² profiles), the smallest at m = 8 (`results/k4_lb4_variants.log`, which lists the first three failing cores).

**Smallest failing configuration** (n = 4, m = 8). Agents 0 = {0, 2, 4, 6}, 1 = {0, 2, 5, 6}, 2 = {1, 3, 4, 7},
3 = {1, 3, 5, 7}, all with values (2, 3, 8, 4) on their goods in that order, i.e. type (8, 4, 3, 2) (a > b + c).
Tops: 4 (agents 0, 2), 5 (1, 3); second goods 6 (0, 1), 7 (2, 3). Every EFX₀ allocation with at most one large bundle
has one agent holding {b, c, d}, worth 9 > 8, e.g. {0, 2, 6} | {5} | {1, 4} | {3, 7} (brute force: 12 such
allocations). The owner's large bundle removes its own need for its top. With needs taken from the base, the agent
holding that top stays frozen, cannot take a slot good, and the completion fails.

Fix (adopted in LB₄, `k4/lb4.md` §1): the owner's needs are N_o = {g ∉ X_o : v_o(g) > v_o(X_o)}. This only shrinks
the needs, so validity is kept and more agents are free.

Reproduce: `python attempts/lb4_variants.py owner-needs-from-base`.
