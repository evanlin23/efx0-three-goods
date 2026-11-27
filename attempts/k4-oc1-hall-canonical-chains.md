# OC₁ with canonical chains only is false

Workstream `proof/k4-oc1-hall` (`k4/oc1_hall.md` §6).

**Idea.** The proved one-frozen-agent cases (Theorems DT₁ and F1₁) use *canonical* chains. Such a chain starts at a
dangerous frozen agent k and passes k's pick along agents that each want the pick they receive and take no junk. k
takes an improving set from J ∪ B_{x_t}. A Theorem B₄ for OC₁ could hope to need only these (`k4/sdc.md` §29 found
canonical chains enough when |D| = 1).

**Result: false.** `k4/oc1_hall/greedy_rules.py`, `results/k4_oc1_hall/greedy_rules.log`. With any improving H₀ and
owner k or the chain end, canonical chains leave unrepaired:
- 15 of the 234 screen hard starts;
- 15 of 233 suite;
- 18 of 1,470 logs;
- 0 of 255 random n = 4.

**Smallest failing configuration** (adaptive-p1, screen and suite; n = 3, m = 6):
- sets [[0,1,4,5],[2,3,4,5],[2,3,4,5]];
- values [[1,4,6,8],[2,3,4,8],[2,7,8,4]];
- order (0, 2, 1), picks (5, 3, 4); frozen agents 0 and 2, both dangerous.

Every repair (dump: `python3 k4/oc1_hall/dump_hard.py suite 3 3`) has a middle agent that gains only with a junk good.
For example, chain (2, 0, 1):
- agent 2 takes junk 2 and agent 1's pick 3 (7 + 2 = 9 > 8);
- agent 0 takes agent 2's pick 4 *plus junk 1* (6 + 4 = 10 > 8, while 4 alone is worth 6 < 8 to agent 0);
- agent 1 takes 5.

**Repro.** `python3 k4/oc1_hall/greedy_rules.py screen` (prints `NO CANONICAL RULE` lines; adaptive-p1 is the first).
