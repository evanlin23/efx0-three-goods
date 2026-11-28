# TARGET₄ with one 4-good agent by local reduction to k = 3: fails (2026-11-28)

**Target.** TARGET₄¹: every instance in which every agent values at most four goods and at most one, z, values four
has an EFX₀ allocation. It is open. K4.ONE.FRAME (Lean) reduces it to C₄∃ on those cores, and C₄¹ is open.

**Idea.** Replace z by gadget agents that each value at most three goods. The resulting H′ is 3-limited, so it has an
EFX₀ allocation by the proved k = 3 theorem, for every H′ and not only smaller ones. If every EFX₀ allocation of H′
extends to H (Lemma M1/M1(b) of `k4/MINCEX.md`, `k4/reduce4.py`), TARGET₄¹ follows, with no minimality and no size
condition on the gadget.

**Result: no such local reduction exists for any of the 288 types of z.** `attempts/k4_one_local_gadget.py`, log
`results/k4_one_local_gadget.log`:

| z (boundary goods) | delete z (M1(b)) | one 3-limited gadget | two 3-limited gadgets |
|---|---|---|---|
| Q4 (4 shared goods) | 0 / 288 | 0 / 288 (146 valuation classes) | 0 / 288 (146² pairs) |
| P4 (3 shared + 1 private) | 0 / 288 | 0 / 288 (43 classes) | 0 / 288 (43² pairs) |

**Why.**
- *One gadget* values at most three of z's goods. The adversarial local state puts the fourth good w, with an
  outside good, into an outside bundle together with another of z's goods. The gadget sees one good and stays safe.
  z sees two goods with a zero-valued good, needs v_z(own) ≥ v_z(x) + v_z(w), and cannot take outside goods.
- *Two gadgets* can watch all four goods, but they hold more than z alone can take back. Example: Y_{h1} = {s},
  Y_{h2} = {t, u}, outside {w}. Then z = {s, t, u} is not dominated by any bundle of Y, so outside agents valuing
  s, t, u may envy it. Placing s elsewhere, even in the unenvied bundle, is not dominated either.
  - Outside agents' valuations are arbitrary, so no local argument can place the surplus.

**Consequence.** A proof of TARGET₄¹ must use global structure of the k = 3 solution, not an arbitrary EFX₀
allocation of a modified instance.
- The natural global variant hides z's least good d, runs K3ALG (D-shaped output), and repairs.
- By the case analysis, that fails only when d lies in the owner's large bundle and z's slack is below v_z(d). Pairs
  and singletons are always fine: θ_z({d, x}) = max(v_z(d), v_z(x)) = θ under the hidden valuation.
- That is exactly the counting gap K4.C4.GAP of the LB₄ program (an exposed 4-good agent needing goods kept out of
  the owner's bundle).

**Part 2: global variant, hide a good and run K3ALG** (`attempts/k4_one_hide_k3alg.py`, log
`results/k4_one_hide_k3alg.log`; EVIDENCE, random instances).
- Instances: `k3algo.random_core` with n = 2..6 (every agent three balanced goods), plus one extra good for z;
  19,175 instances.
- Hiding z's least good and running K3ALG unchanged gives EFX₀ on 95.2%.
  - The 923 failures all have the hidden good in a bundle that also holds a good z values at zero. In 892 of them it
    is the owner's large bundle. In 31 it is a small bundle, when z's own bundle is worth less than that good, so the
    case analysis above also needs "z holds something".
- Also moving the hidden good to z: 97.7%. The best of the 4 hidden goods, with the move: 99.75%. 48 instances fail
  every variant.
- **Smallest failure:** n = 2, m = 5, v₀ = {1: 98, 4: 86, 0: 27}, z = agent 1 with v₁ = {1: 36, 4: 33, 3: 10, 0: 12},
  and good 2 valued by nobody.
  - It has 3 EFX₀ allocations, including ({0, 4}, {1, 2, 3}).
  - No hidden good, with or without the move, gives one. For example, hiding 3 gives ({1, 2, 3}, {0, 4}), where z sees
    36 + 10 = 46 > 45 in agent 0's bundle.
  - Repairing needs re-optimization, not one move: that is the LB₄ repair machinery and its gap.

**Smallest failing configuration (part 1):** a single Q4 agent with boundary goods (s, t, u, w), any type (for instance values
(8, 6, 4, 1)).

    python3 attempts/k4_one_local_gadget.py
    python3 attempts/k4_one_hide_k3alg.py 20000
