# Attempt (proof/k4-ksens): searching for an OC₁ counterexample at k = 4

**Status:** failed. The searches below found no failure of OC₁ (or OC₁^max) at k = 4, and bursts 1–2 of
`k4/ksens.md` reported "holds on all k = 4 data". A counterexample exists:
- the certifier session's ordinal CEGAR (`compute/k4-oc1max-cert`) found 11 strict n = 4 cores;
- they are replayed here by two independent checkers (`k4/ksens.md` §5).

This file records what was searched, and why it could not have found them.

## What was searched (all at k = 4)

| search | size | result | log |
|---|---|---|---|
| PW design space (`pw4_search.py`): frozen agents with 3-subsets of a pool, every pair dangerous; 1–3 wanters of random subsets of the picks; sometimes one extra random agent | 60,000 + 20,000 instances, n ≤ 8 | 0 failures; 38,601 starts needing a chain | `pw4_search*.log` |
| PW-shaped random instances (`gen.py pw`) | 600 instances, n = 5 | 0 | `survey_pw_n5k4.log` |
| Lemma K4-G4 on curated hard starts (GM4, T3, Q2, the logged climbs) and on PW-design hard starts | 349 + 1,392 starts | always a repairing chain | `g4_after*.log` |
| Climbs against OC₁ from PW starts, n = 5 and 6 | 40 + 30 rounds | bottom out at exactly one repairing state | `climb_oc1_n5k4_pw.log`, `climb_oc1_n6k4_pw.log` |
| Climb against OC₁^max from PW-design starts, n = 5 | 30 rounds | bottoms out at one repairing state | `climb_oc1mx_n5k4.log` |

## Why they missed it

1. **Wrong family.** Every search but the climbs lived in the PW design space, where wanters value only picks and a
   chain releases only a wanter's own good, which nobody else values.
   - The k = 4 failure needs a released pick that a third agent values: g2 in the first instance, which agent 0
     values at 4.
   - That pick and another pick then form a danger set of that agent (7 + 4 > 10, §5).
   - PW cannot produce this. Lemma PL, which explains PW, says nothing about released bases or danger sets built from
     other agents' picks, and those were exactly its listed gaps.
2. **Failing profiles are rare even on the right hypergraph.** On each of the 11 hypergraphs, no random strict
   profile out of 300 fails OC₁^max (3,300 profiles, values distinct integers 1–30: `oc1max_k4_rarity.py`,
   `results/k4_ksens/oc1max_k4_rarity.log`).
   - The failure needs specific inequalities between sums: the released pick plus another pick beats a third agent's
     pick, every pair of the pool beats the frozen picks, and the wanter's values sit below every pick it wants.
   - A random profile almost never satisfies all of them at once.
3. **Climbs with a flat objective.** The climbs minimized the number of repairing states, which bottomed out at 1 and
   gave no gradient towards 0. Starting from PW seeds, they never left the PW structure.

What worked: the certifier enumerated every order type of every core hypergraph with an exact SAT outer loop
(`k4/oc1cert/cegar.py` on its branch). At k = 4, exhaustive search over order types beats sampling values.

## Smallest failing configuration

The first instance of the certifier's list: n = 4, m = 7, every agent with at most four goods.
- sets [[0,1,2,5], [1,2,5,6], [3,4,5,6], [3,4,6]]
- vals [[2,10,4,7], [10,3,4,8], [3,5,6,7], [3,2,4]]
- order (0, 3, 2, 1), picks (1, 2, 5, 6), junk {0, 3, 4}

From these picks, no state with at most one chain, and no state after one round, has a completion, free or
one-absorber. Two chains repair it. The mechanism is analysed by hand in `k4/ksens.md` §5.

Reproduce (both checkers, all 11 instances, about a second):

    python3 k4/ksens/refute_oc1max_k4.py
