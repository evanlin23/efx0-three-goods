# The stuck lemma: single improving moves are not enough

Workstream `proof/k3-simplify` (`proofs/k3_simple.md` §8; `k3/simplify/explore/matching/NOTES.md` §4).

**Idea.** Conjecture ST: a valid state (each agent holds nothing, one of its goods, or its pair {b, c}; every good
needed alone is held alone) in which no single move applies is completable. The single moves are: an upgrade, a
trading cycle among single-good holders, or a rotation (one agent takes {b, c} and its top passes down a need chain).
ST would give the local search "improve until stuck". It implies Conjecture PO and was supported by 0 failures on
every stuck state with n ≤ 3, n = 4, m = 5, and random profiles with n ≤ 5.

**Where it breaks.** Two free agents can each block the other's exposed top holders. The only Pareto improvements
then upgrade two agents at once, along an exchange cycle that alternates "x takes {b_x, c_x}, which contains a free
agent's good" and "that free agent takes a top it needs". No single move does this. Conjecture PO survives: the state
is Pareto-dominated, and every dominating valid state is completable.

**Smallest known failing configuration**, at n = 6, m = 10. Goods are A1 = 0, A1′ = 1, A2 = 2, A2′ = 3, p1 = 4,
p2 = 5, g1 = 6, g1′ = 7, g2 = 8, g2′ = 9.

| Agent | Ranking | Holds |
|---|---|---|
| x1 | (0, 4, 6) | its top 0 |
| x1′ | (1, 4, 7) | its top 1 |
| x2 | (2, 5, 8) | its top 2 |
| x2′ | (3, 5, 9) | its top 3 |
| o1 | (2, 3, 4) | its c, 4 |
| o2 | (0, 1, 5) | its c, 5 |

- The state is valid: NA = {0, 1, 2, 3}, all held alone. The junk is {6, 7, 8, 9}, and the free agents are o1, o2.
- It is not completable.
  - For absorber o1, the exposed agents are x1 and x1′. Their junk goods 6 and 7 are different, so they need two
    protecting goods, but only o2 is free.
  - Absorber o2 fails in the same way.
- No single move applies. There are no b holders, a trading cycle would need a top holder to need something, and a
  rotation by x1 would have to release p1, which no need chain reaches.
- Four valid states dominate it, all completable. One is x1′ → {4, 7}, x2′ → {5, 9}, o1 → 3, o2 → 1.

Random search found no such state at n = 5 (600 random profiles, every valid state checked;
`k3/simplify/po/hard_states.py`).

Reproduce: `python3 k3/simplify/po/st_counterexample.py`
