# OC₁^max fails on a strict connected k = 4 core with n = 4 (workstream `proof/kgen-rounds`)

**Idea.** Conjecture OC₁^max, ledger row K4.SDC.OC1MAX (`k4/sdc.md` §31): in every strict connected k = 4 core, for
every serial-dictatorship order whose picks form a maximum matching, the picks have a one-absorber EFX₀ completion,
or one improving move (an addition, a chain or a ring) gives bases that have one. With K4.SDC.MAXSD it would imply
TARGET₄. It had no failure on 11.0M maximum-matching orders at n = 5 and on every curated set.

**Where it breaks.** At n = 4, m = 7, on the core C4K below, from two perfect starts (every agent picks, ν = n = 4).

| agent | g0 | g1 | g2 | g3 | g4 | g5 | g6 |
|---|---|---|---|---|---|---|---|
| 0 | 0 | 2030 | 0 | 0 | 1714 | 1395 | 1806 |
| 1 | 0 | 2461 | 0 | 0 | 1674 | 1357 | 1802 |
| 2 | 1025 | 0 | 35 | 818 | 0 | 0 | 934 |
| 3 | 1090 | 901 | 0 | 154 | 0 | 0 | 517 |

- *It is a strict connected k = 4 core.* Every agent has four relevant goods and is strictly balanced (2030 < 4915,
  2461 < 4833, 1025 < 1787, 1090 < 1572). All subset sums are distinct, the only private good is g2 (agent 2), every
  good is valued, and the instance is connected. The test is the core claim of `k4/gm4_counterexample.py`, in
  `kgen/rounds/c4k_core.py`.
- *Starts.* Order (0, 1, 2, 3) gives picks (1, 6, 0, 3) for agents 0–3; order (1, 0, 2, 3) gives (6, 1, 0, 3). The
  junk is {2, 4, 5}. 6 of the 24 orders give one of these two starts.
- *OC₁ fails there.* No one-absorber completion exists at the picks, nor after any addition, chain or ring.
  Four programs agree:
  1. `k4/sdc/oc1_max_orders.py` (the campaign's own OC₁^max test): "instances where some maximum-matching order fails
     OC1: [0]";
  2. k4/sdc's pipeline (sdclib.Enc, de_free.moves with rings, oc_absorb.extends_A);
  3. ksens's `ocsat.py` (SAT);
  4. the pure-Python brute force of `kgen/rounds/verify_k4zero.py` (raw EFX₀, every chain, ring and set).
- *Mechanism* (`results/kgen_rounds/c4k_mechanism.log`).
  - There are 10 EFX₀ allocations; 6 value-dominate the picks.
  - In all six, agent 3 takes agent 2's pick g0, worth 1090 to agent 3 against its own pick, worth 154. Agent 2
    takes both foreign picks g3 and g6, and agent 1 takes the junk {4, 5}.
  - A move gives each base at most one foreign pick. Agent 2's best one-move base is g6 + g2 = 934 + 35 = 969
    < 1025 = v₂(g0), so agent 2 is *starved* (`kgen/rounds.md` §1).
  - The starved agent uses exactly four goods: its pick, two foreign picks and one junk good. The five-good count
    behind RD5 (`k4/ksens.md` §6) therefore does not protect k = 4.
- *What still holds.* Two rounds of vertex-disjoint chains repair both starts (brute force). MD holds, and so does
  SD-C: 18 of the 24 orders satisfy OC₁.
- *How it was found.* `kgen/rounds/stress.py climb` on ε-lifts of k = 4 cores (KEPS = 4, KCORE = 1). Every value
  outside an agent's four real goods is in 1..5, and the zero version must satisfy K4.CORE. The climb minimizes the
  number and the margin of one-round witnesses at the hardest start. The zero version of each ε-failure was then
  tested (`k4zero_scan.py`). Random core sampling had missed it.

**Reproduce.**
```
python3 kgen/rounds/c4k_core.py                         # core test
(cd k4/sdc && python3 oc1_max_orders.py ../../results/kgen_rounds/c4k.json)
python3 kgen/rounds/k4w_check.py '[[0,2030,0,0,1714,1395,1806],[0,2461,0,0,1674,1357,1802],[1025,0,35,818,0,0,934],[1090,901,0,154,0,0,517]]'
                                                        # every order: ocsat, k4/sdc pipeline, brute force (KSENS = checkout of claude/k4-ksens)
```

**What survives:** two rounds (RD² at k = 4), MD, SD-C.
