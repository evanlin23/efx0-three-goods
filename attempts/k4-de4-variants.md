# Simpler versions of DE4 that fail (k = 4)

Workstream `proof/k4-de4` (`k4/de4.md`). Approach: carry DE (the k = 3 algorithm Draft and Exchange,
`paper/k3-simple` of evanlin23/efx0-three-goods-proof) to four relevant goods by choosing a state space of holdings, a
validity rule and a potential, and asking that **every maximum of the potential be completable**. The version that
survives every test is DE4 (`k4/de4.md` §1–§2). Each simpler version below fails; together they show which feature of
DE4 is needed. Every instance is in `k4/suite/instances/`; "valid" always includes (V1) wanted goods are one-good
holdings and (V2) no holding threatens anyone.

| | variant | fails on | what goes wrong |
|---|---|---|---|
| V1 | DE's holdings: nothing, one good, or a set without the top worth more than the top | `adaptive-cover-multi4` (n = 2, m = 4) | two agents value goods 0–3 at 2, 4, 5, 8; the only EFX₀ allocations are {top, lowest} \| {middle two}, so a holding with the top and another good is necessary |
| V2 | V1 plus the sets {a, x} (all minimal sets worth more than the top), no lower pair | `red-a1-hopeless-key` (n = 3, m = 6) | the maximum [{0}, {5}, {4}] is stuck: agent 2 holds b with c, d leftover and c + d > b; the fix gives it {c, d}, worth less than its top |
| V3 | every minimal set worth more than some single value of the agent | `ls-dead-end-n4m7` (n = 4, m = 7) | contains the dead end of `attempts/k4-ls-dead-end.md`, Y = {2} \| {6} \| {1, 4} \| {3, 5}: valid, value-Pareto-maximal, no completion. Agent 2's {1, 4} is its b and d, worth less than its top, which DE4 forbids |
| V4 | DE4's states, value-Pareto-maxima (no level sum) | `gm4-B` (n = 4, m = 7) | the Pareto-maximum [{0,2}, {1,4}, {6}, {5}] (levels 3, 3, 4, 4) is not completable and no valid state is value-Pareto-better; a state better in the level order moves agent 0 from its lower pair {c, d} to b (same level, lower value) |
| V5 | DE4 with DE's single-owner finishing rule | `hall-cyc6` (n = 6, m = 15) | a maximum (every agent holds an upper pair, J = {12, 13, 14}) is not finished by any single owner, but giving the leftover goods to two agents works: {4, 5, 12, 14} and {6, 7, 13} |
| V6 | owners restricted to agents holding at most one good (as in DE) | `induct-g-r1` (n = 2, m = 5) | the only maximum has both agents holding a pair and one good left over |
| V8 | Conjecture 11 of `k4/de4.md` §7 in its first form: when DE's walk stops, move P (partial path) or move K (two-agent keep-own exchange) improves | a random profile of an n = 4 core (in `k4/de4/variants.py`), found in a run of 50,000 profiles | the walk stops, neither P nor K improves, and no move of at most two agents does; the improvement is a 3-cycle in which one blocker keeps part of its own holding (the refined walk of §7.6 finds it) |
| V7 | algorithm DE4 with DE's ring built from distinct leftover goods chosen greedily for *all* free agents, pair holders included | two random profiles of n = 4 cores (in `k4/de4/variants.py`) | after the draft and one chain, a free agent holding an upper pair takes the only leftover good that the needed ring uses; DE's rule proper (greedy over the free agents holding at most one good, others only when the walk reaches them) builds the ring |

V4 and V5 are the instances behind gaps (G1) of `k4/de4.md` §5.

**Smallest failing configurations** (as found; n = 2 is the least possible n for V1 and V6, the others are the
smallest on the suite, not proved smallest):
- V1, V6: n = 2 (`adaptive-cover-multi4`, `induct-g-r1`);
- V2: n = 3, m = 6 (`red-a1-hopeless-key`);
- V3, V4: n = 4, m = 7 (`ls-dead-end-n4m7`, `gm4-B`);
- V5: n = 6, m = 15 (`hall-cyc6`);
- V8: n = 4, m = 8 (the profile in `k4/de4/variants.py`);
- V7: n = 4, m = 8 and m = 7 (the two profiles in `k4/de4/variants.py`; found in `results/k4_de4/algo_random.log` of
  the first run, 2 of 6,090 runs).

Replay: `python3 k4/de4/variants.py` (prints "confirmed" for each and exits 0 iff all are confirmed;
`results/k4_de4/variants.log`).
