# Proving LS4⁺ correct through GM₄ (maxima of the level sum admit a placement)

Workstream `proof/k4-gm4` (`k4/gm4.md`).

**Approach.** Theorem 1⁺ of `k4/ls4plus.md` shows that LS4⁺_n can fail only at a junk-free EFX₀ partial allocation that maximizes the level sum Σℓ and admits no placement of its pool. Conjecture GM₄ says no such maximum exists: every Σℓ-maximum admits a placement. Equivalently, no dead end maximizes Σℓ. The plan was to prove GM₄ by an exchange argument in the style of Theorem C of `proofs/local_search.md`. Suppose a maximum Y has sources s whose single dumps all fail. By Lemma 5 of `k4/local_search4.md`, each such s has a champion (h, Z) with h reachable only from other sources. Following champions around a cycle of sources gives an exchange cycle, which raises Σℓ. A proof would then have to show that maximality excludes every obstruction to that cycle.

**Where it breaks (n = 4, m = 7, two 4-good agents).** Agents and values:
- agent 0: goods 0:3, 2:10, 4:6, 6:2;
- agent 1: goods 1:3, 3:4, 5:8, 6:2;
- agent 2: goods 2:4, 3:2, 6:3;
- agent 3: goods 4:2, 5:4, 6:3.

The partial allocation Y = {0, 4} | {1, 3} | {2} | {5}, with pool {6}, has these properties:
- it maximizes Σℓ (= 18) among all junk-free EFX₀ partial allocations;
- good 6 fits nowhere (`k4/gm4.md` §2.1 checks each agent by hand);
- no complete EFX₀ allocation gives every agent at least its value in Y;
- four single-agent rebundles reach Y from the empty allocation.

The obstruction is the one the proof would have had to exclude. The two sources, 0 and 1, have champions 3 (envying {4, 6}) and 2 (envying {3, 6}), each reachable only from the other source. The exchange cycle 1 → 3 ⇒ 0 → 2 ⇒ 1 needs good 6 twice. At k = 3 this Hall-type conflict is resolved by placing the shared good alone next to a one-good source. Here the only one-good bundles belong to envied agents, and the sources hold two goods each.

**Consequence.** GM₄ is false, and so is its equivalent form. LS4⁺_n fails under some valid choices: M1 has priority, so the four rebundles are a valid run. Its default rule does not fail on the profiles found (`k4/gm4.md` §3). Every counterexample found has *another* maximum that admits a placement. So the existence form GM₄∃ and refined potentials remain open (`k4/gm4.md` §4, §6).

Counts (one implementation, `k4/gm4_fast.c`; `k4/gm4.md` §4):
- no failure for n ≤ 3 (exhaustive), for n = 4 with one 4-good agent (exhaustive), or for all-3-good cores with n = 5 (exhaustive);
- 3 maxima without a placement in 39,150,000 random n = 4 profiles with one to three 4-good agents;
- 4 in 43,800,000 random pure n = 4 profiles;
- more in pure n = 5 (§4).

Smallest configuration found: n = 4, m = 7, two 4-good agents. n ≤ 3 and one 4-good agent at n = 4 are exhausted; m ≤ 6 with two or more 4-good agents is only sampled.

Reproduce: `python3 k4/gm4_counterexample.py` (independent plain-Python brute force from the raw definition; instances A–F). Instance E is the one above.
