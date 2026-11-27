# OC₁ with chains of at least two agents (t ≥ 1) fails at n = 2 and at n = 3, k = 5 (workstream `proof/kgen-n3`)

**Idea.** Conjecture OC₁ (k4/sdc.md §29, row K4.SDC.OC1) as written: from every serial-dictatorship order, the picks
have a one-absorber EFX₀ completion (at most one agent receives two or more goods outside its base), or after one
improving chain the bases have one. §29 defines a chain as distinct agents x₀, …, x_t with **t ≥ 1**.

**What was actually tested at k = 4.** The code behind every count in §29 (`k4/sdc/oc_absorb.py`, through
`k4/sdc/de_free.py`'s `moves` with `CHAIN_ONLY`) also generates chains with **t = 0**: a single agent x₀ adds junk goods
it values to its own pick (`de_free.py` docstring: "t >= 0; t = 0: x_0 just adds or swaps in junk goods"). So the
120,050 starts of §29 support OC₁ with t ≥ 0 moves, not the written t ≥ 1 statement.

**Where the written form breaks.** At n = 3 with five relevant goods for one agent and strict values, the picks of an
order have no one-absorber completion, and no chain with t ≥ 1 gives one. A t = 0 move does.

**Smallest failing configuration found** (n = 3, m = 7, strict values; agent 0 values 5 goods, agents 1 and 2 four
each; found by `kgen/climb3.py`, shrunk by `kgen/shrink3.py`):

| agent | values of goods 0–6 |
|---|---|
| 0 | 74, 72, 5, 0, 73, 71, 0 |
| 1 | 0, 0, 2, 58, 27, 0, 28 |
| 2 | 4, 3, 0, 7, 0, 1, 0 |

- Order (0, 2, 1): agent 0 picks 0, agent 2 picks 3, agent 1 picks 6. The junk is {1, 2, 4, 5}. The orders (2, 0, 1)
  and (2, 1, 0) have the same picks and fail the same way.
- There are 29 complete EFX₀ allocations. None is a one-absorber completion of the picks.
- There are 7 states reachable by one improving chain with t ≥ 1, and none of them has a one-absorber completion.
- The t = 0 move "agent 0 adds good 1 (worth 72 to it)" works: the bases ({0, 1}, {6}, {3}) complete to
  ({0, 1, 2}, {4, 5, 6}, {3}). Agent 0 receives good 2 and agent 1 absorbs {4, 5}.
- That allocation is EFX₀. Agent 0 holds 151 and values {4, 5, 6} at 144. Agent 1 holds 55 and values {0, 1, 2} at 2.
  Agent 2 holds 7; it values {0, 1, 2} at 7 after any removal, and {4, 5, 6} at 1.
- So the t = 0 move acts as a second absorber restricted to goods the agent values. Under the free completion the picks
  extend directly (SD-C holds for this order, with two absorbers).

Three independent checks agree:
- `kgen/oc3.c`: brute force over all 3^m allocations, with the reachability characterization;
- `kgen/verify_oc1.py`: pure Python, every chain enumerated explicitly with all sets H, no shared code;
- k4/sdc's SAT pipeline (`oc_absorb.extends_A` with `de_free.iter_chains`), discarding states in which only one
  agent's base changed.

**Already at n = 2** (`kgen/oc2.py`, which enumerates every chain explicitly):
- Two agents, m = 7, strict values. Agent 0 values goods 0–6 at (0, 28, 8, 27, 55, 26, 21), agent 1 at
  (1, 66, 3, 64, 2, 63, 65). Found by `kgen/oc2.py`, then shrunk greedily.
- Both orders give the picks (4, 1). They have no one-absorber completion, and no t = 1 chain gives one. A t = 0 move
  does.
- Of 8,000 random two-agent starts (`results/kgen_n3/oc2_2_4000_3_13.log`), 2,757 need a move. The t ≥ 1 form fails
  on 2 of them, and the t ≥ 0 form on none.

**How far it reaches.**
- Of 300 adversarial climbs without a k cap (`results/kgen_n3/climb3_strict_1_300_2000_5_11.log`), 18 end in a
  counterexample to the t ≥ 1 form, with m = 7 to 11 and k = 6 to 11. Some of them fail from all six orders.
- OC₁ with t ≥ 0 holds on every one of them.
- With strict values and k ≤ 4, no climb finds one:
  - 200 free-m climbs, which drifted to m = 5–6 (`results/kgen_n3/climb3_strict_k4_3_200_2000_5_12.log`);
  - 160 climbs with m fixed in 7–10 (`results/kgen_n3/climb3_strict_k4_fixm_10_160_1500_7_10.log`).
- So the written form fails at k = 5 (n = 3) and at k = 7 (n = 2) among the instances found. Whether it holds at k = 4
  is untested for n ≥ 4: §29's data tested t ≥ 0.

**Consequence for the campaign.** State OC₁ with t ≥ 0 moves. That is the conjecture the evidence supports, and it
survives at n = 3 for every k tested (`kgen/n3.md`). A proof of the t ≥ 1 form cannot exist at k ≥ 5. At k = 4 the
written form may still hold, but nothing tested so far separates the two forms there.

Reproduce: `python3 attempts/kgen_n3_oc1_strict.py`. The last two lines should read `OC1 with t>=1 REFUTED, OC1 with
t>=0 holds, all three checks agree: True` (n = 3) and `n = 2: t>=1 REFUTED, t>=0 holds, both checks agree: True`.
