# Housing-market and TTC view of the improving chains (k = 4)

Workstream `proof/k4-ttc` (branch `claude/k4-ttc`). Code: `k4/ttc/`; logs: `results/k4_ttc/`. Notation as in
`k4/sdc.md` (§2, §29, §30). Everything called evidence below is evidence only (PROMPT.md §5 rule 3). This note does
not change any ledger row; the coordinator integrates.

## Status (burst 1, in progress)

- **Translation** (§2): the serial-dictatorship picks are the Pareto-optimal one-good matchings; the induced market
  has every agent as an existing tenant holding its pick, the junk as the pool of vacant goods, and set demands. With
  unit demand nothing trades (the start is Pareto-optimal and TTC is individually rational), so every repair needs a
  set demand. An improving chain of §29 is exactly a request path of YRMH-IGYT ("you request my house, I get your
  turn") that ends with a request to the pool; a ring is a request loop.
- **Mechanism test** (§3): YRMH-IGYT with set demands, run from the picks, priority = reverse order, each agent
  requesting its least valuable improving option ("just enough"), repairs 66 of the 69 hard special starts after
  repeated single trades (baseline: a random improving chain repairs 35% of the time). Screen and suite runs pending.
- **Literature** (§1): being read; nothing is cited below until it is recorded with its read level.

## 1. Literature

(pending)

## 2. The induced market

(pending)

## 3. Mechanisms run from the picks

(pending)
