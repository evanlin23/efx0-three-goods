# OC₁ and OC fail at n = 4 for k ≥ 5 (workstream `proof/kgen-n3`)

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

**With strict values** (`kgen/shrink_n.py` on the strict climb result, `results/kgen_n3/shrink_n4_strict.log`):
n = 4, m = 8, k = 5.

| agent | values of goods 0–7 |
|---|---|
| 0 | 34, 0, 0, 0, 38, 35, 37, 33 |
| 1 | 0, 10, 5, 0, 0, 4, 2, 0 |
| 2 | 0, 2, 0, 0, 3, 0, 1, 0 |
| 3 | 52, 54, 53, 4, 0, 0, 0, 51 |

- **Failing orders.** It fails from 5 orders: (0, 3, 1, 2), (0, 3, 2, 1), (3, 0, 1, 2), (3, 0, 2, 1) and (3, 1, 0, 2).
- **Order (0, 3, 1, 2).**
  - Picks: 4 for agent 0, 2 for agent 1, 6 for agent 2, 1 for agent 3. The junk is {0, 3, 5, 7}.
  - There are 127 EFX₀ allocations. None completes the picks, or any of the 159 states one chain reaches (t = 0: 15,
    t = 1: 66, t = 2: 66, t = 3: 12), with one absorber.
  - OC fails too: no free completion after one chain.
  - Two chains repair it (`kgen/weaker_n.py`).
- **Mechanism.** Agents 0 and 3 both value the junk almost as much as their picks (agent 0: 34, 35, 33 against 38;
  agent 3: 52, 51 against 54). Each needs a trade, and one chain cannot serve both.

**At k ≤ 4** (strict values, `kgen/climb_n.py` with `CLIMB_K=4`), no counterexample:
- 160 climbs at n = 4, m = 7–10;
- 40 climbs started from the strict instance above, which penalize goods valued beyond 4 per agent first;
- climbs at n = 5 and at larger m are running.

On the curated and logged k = 4 data of k4/sdc, one chain always suffices (k4/sdc.md §29). So OC and OC₁ remain open
at k = 4. A proof must use k ≤ 4.

Reproduce:
- `python3 kgen/verify_oc1_n.py '[[34,0,0,0,38,35,37,33],[0,10,5,0,0,4,2,0],[0,2,0,0,3,0,1,0],[52,54,53,4,0,0,0,51]]' 0,3,1,2`
- `python3 kgen/verify_oc1_n.py '[[0,155,1,0,0,155,0],[0,75,2,74,0,74,77],[0,0,0,2,133,0,134],[1,4,0,2,0,0,0]]' 0,2,1,3`

Each prints "repairs per t none" and a SAT status of None. `python3 kgen/weaker_n.py '<same>' <same order>` gives
least number of moves 2.
