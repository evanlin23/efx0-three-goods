# k = 4 attack log (parallel campaign, from 2026-11-26)

Goal: settle TARGET₄ (every additive instance in which every agent values at most four goods has a complete EFX₀
allocation), by proof or by counterexample. This file is the coordinator's record: one entry per hourly burst, the
angles in flight, and what each established. Ledger rows change only with artifacts (AGENTS.md §5).

## Where k = 4 stands (start of the campaign)

- **Certified**: TARGET₄ on every core with n ≤ 5 that has a 4-good agent, with n = 6 and exactly one, and for
  β ≤ 4 (rows K4.R5*, K4.R6a, K4.MC6, K4.MC7; ledger open items 15–16).
- **Refuted routes**: every "maximum of a potential is completable" form (K4.SDC.P1: no value-monotone method works,
  n = 4, m = 7), DE4 and its tie-breaks, GM₄, DL₂ and successors, NO/NOF, PHI₄, and the move catalogues (items 17–30,
  `attempts/k4-*.md`).
- **Surviving targets** (`k4/sdc.md`): SD-C, MD, and the sharpest one, **OC₁** (§29): from every serial-dictatorship
  order, the picks have a one-absorber EFX₀ completion, or one improving chain makes one exist. It holds on all
  120,050 starts tested (n ≤ 5) and implies TARGET₄.
- **Proved pieces**: Theorems DT and DT⁺ (distinct tops; no frozen agent values junk), Lemma GDT (completion for
  single goods and satisfied pairs), Theorem DT₁ (one frozen agent with one wanter and an improving pair).
- **Missing**: the count that shows the frozen agents' demands (goods to keep out of the owner's bundle) fit into the
  free slots, or that one improving chain makes them fit (`k4/sdc.md` §30, last paragraph).

## Angles in flight

| angle | session | branch | note |
|---|---|---|---|
| CEGAR counterexample hunt: synthesize values for a fixed core so that no allocation is EFX₀; certify cores for all values otherwise | session_01BYMGeaDXra9RWYSfAKvqid | `claude/k4-hunt-cegar` | `k4/hunt.md` |
| Hall-type count for OC₁: exact completion condition for picks plus owner, then one chain restores it | session_01BYMGeZTVDV38teEA7133jH | `claude/k4-oc1-hall` | `k4/oc1_hall.md` |
| Extend the girth-≥4 hypergraph theorem (Lianeas–Sgouritsa–Sotiriou) to degree-4 hypergraphs with short cycles | session_01BYMGeahqCXt4wer7YeYLty | `claude/k4-girth` | `k4/girth.md` |
| Prove OC₁ at k = 3 with Draft and Exchange's machinery, then lift lemma by lemma to k = 4 | session_01BYMGeZVgBaajhpdHdJtKm2 | `claude/k4-k3-oc1` | `k4/k3_oc1.md` |
| Reconstruct Viswanathan–Mehta's 4-limited EFX algorithm and make it EFX₀ | session_01BYMGebcnNSpPp9qEyjfvuV | `claude/k4-vm` | `k4/vm.md` |

The coordinator (this branch, `claude/kind-lamport-y8fdme`) runs an hourly burst: it checks each angle, verifies any
claimed proof or counterexample independently, integrates verified results here, and works one angle of its own.

## Log

### 2026-11-26 20:35 UTC: campaign started
- Five angle sessions launched from `claude/kind-lamport-y8fdme` (commit `26e79d2`).
- Hourly coordinator burst scheduled (trigger `trig_016DHmg4n61QCy2RopwumejP`, minute 34).
