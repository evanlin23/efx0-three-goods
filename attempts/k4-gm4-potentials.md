# Another potential whose maxima all admit a placement

Workstream `proof/k4-gm4` (`k4/gm4.md` §6).

**Approach.** LS4⁺'s soundness and termination hold for any potential that every M1, R and X move raises, with coalition moves defined by the same potential (`k4/ls4plus.md` Theorem 1⁺). Every strictly increasing function of each agent's level qualifies. The bad maxima of the level sum are the *most equal* ones (`k4/gm4.md` §6). So potentials that favor unequal level vectors were tried:
- tie-breaks among the Σℓ-maxima: largest Σℓ², leximax-largest, and leximin for contrast;
- Σℓ² in place of Σℓ;
- Σ 2^ℓ in place of Σℓ;
- leximax (Σ 16^ℓ) in place of Σℓ;
- fixed priority (the level vector in a fixed agent order, compared lexicographically; the coordinator's suggestion and #29's `POT=2`).

The hope was a potential of which every maximum admits a placement ("GM" for that potential).

**Where it breaks.**
- Tie-breaks and Σℓ²: instance G of `k4/gm4_counterexample.py` (pure n = 4, m = 7; `attempts/k4-gm4-existence.md`). Its unique Σℓ-maximum is a dead end, and so is its unique Σℓ²-maximum (the same allocation).
- Σ 2^ℓ and leximax: pure n = 4, m = 7. Agents and values:
  - agent 0: goods 0:1, 2:6, 5:8, 6:4;
  - agent 1: goods 1:1, 4:6, 5:4, 6:8;
  - agent 2: goods 2:4, 3:5, 4:2, 6:8;
  - agent 3: goods 3:5, 4:4, 5:8, 6:2.

  {0, 2} | {1, 4} | {6} | {5}, with pool {3}, maximizes both potentials and admits no placement. The other maximum of both, {0, 2} | {6} | {3, 4} | {5}, admits one.

- Fixed priority: instance E with agent order 2, 3, 0, 1 (the two 3-good agents first). The unique fixed-priority maximum is E's dead end. Over all 24 orders, 6 of the 7 GM₄ seed profiles, and all 148 profiles whose Σℓ-maxima are all bad, have an order whose maxima are all dead ends (`k4/gm4_priority.py`, `results/k4_gm4_priority_*.log`). Every profile tested had some order that works.

**Consequence.** No potential tried has all its maxima placeable. For Σ 2^ℓ and leximax the existence form ("some maximum admits a placement") had no failure:
- around the seven GM₄ profiles, 2 agents changed: 2,260,332 profiles, 32 with a bad maximum, 0 with only bad maxima;
- around those 32, 2 agents changed: 15,925,248 profiles, 2,688 with a bad maximum, 0 with only bad maxima.

That existence form is conjecture K4.GM.POT (`k4/gm4.md` §6, §7).

Smallest configuration found: pure n = 4, m = 7 for every variant (found only by the neighbourhood searches).

Reproduce: `python3 k4/gm4_counterexample.py` (instances G, P and Q).
