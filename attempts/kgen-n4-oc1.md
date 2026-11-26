# OC₁ and OC fail at n = 4 for k ≥ 5 (workstream `proof/kgen-n3`) — first record, being shrunk

**Idea.** Conjecture OC₁ (k4/sdc.md §29, row K4.SDC.OC1) in the form k4/sdc's code tests: from every
serial-dictatorship order, the picks have a one-absorber EFX₀ completion, or one improving chain (t ≥ 0) makes one
exist. Also Conjecture OC (K4.SDC.OC): the same with the free completion.

**Where it breaks.** At n = 4 with more relevant goods per agent, both fail. Found by the adversarial climb
`kgen/climb_n.py 4 21 120 1200 7 10 CODE` (`results/kgen_n3/climb_n4_code_21_120_1200_7_10.log`): 5 of 120 climbs end
in a counterexample, m = 8–10, k = 7–10. At every failing order the free completion with one chain (OC) fails as well.
MD holds there, and SD-C holds (another order's picks extend).

**Smallest configuration so far** (n = 4, m = 7, k = 5, *with ties*; shrunk by `kgen/shrink_n.py ... CODE ties`):

| agent | values of goods 0–6 |
|---|---|
| 0 | 0, 155, 1, 0, 0, 155, 0 |
| 1 | 0, 75, 2, 74, 0, 74, 77 |
| 2 | 0, 0, 0, 2, 133, 0, 134 |
| 3 | 1, 4, 0, 2, 0, 0, 0 |

- **Picks.** Order (0, 2, 1, 3): agent 0 takes 1 (155, a tie with good 5, broken by index), agent 2 takes 6, agent 1
  takes 3 (74, a tie with good 5), and agent 3 takes 0. The junk is {2, 4, 5}. The order (2, 0, 1, 3) has the same
  picks.
- **OC₁ fails.** There are 33 EFX₀ allocations. None is a one-absorber completion of the picks, and none completes the
  bases of any of the 28 states one chain reaches (t = 0: 7, t = 1: 15, t = 2: 6).
- **What still works** (`kgen/weaker_n.py`, k4/sdc's `de_free.search` with unbounded sets): **two** chains repair this
  start. That holds with a free completion, with rings, and with one absorber.
- **Checks.** `kgen/ocn.c` (brute force with the reachability characterization, Lemma R of `kgen/n3.md`),
  `kgen/verify_oc1_n.py` (pure Python, every chain and every choice of sets enumerated) and k4/sdc's SAT pipeline
  (`oc_absorb.extends_A` + `de_free.iter_chains`) agree.

**Open (in progress):**
- a counterexample with strict values (one of the climb results is strict, m = 10, being shrunk);
- whether OC₁ or OC fails at k = 4 (n = 4 climbs with k ≤ 4 running).

At k = 4 the curated and logged sets of k4/sdc never need more than one chain (k4/sdc.md §29).

Reproduce: `python3 kgen/verify_oc1_n.py '[[0,155,1,0,0,155,0],[0,75,2,74,0,74,77],[0,0,0,2,133,0,134],[1,4,0,2,0,0,0]]' 0,2,1,3`
(prints no repair for any t, and SAT status None).
