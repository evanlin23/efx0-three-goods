# ZMOVE at every Pareto-maximal (or locally optimal) state of the key (proof/k4-zmove-pot)

**Candidate.** The potential of ZMOVE can be weakened to Pareto optimality inside the key: at every state P of a key
κ with def*(κ) > 0 that is Pareto-maximal among the states of κ (no state of κ is at least as good for every free agent
and better for one), or at which every free agent is locally optimal (no set of at most two goods inside its base plus
the junk is worth more than its base), some (T3⁺) move with at most one helper reaches def ≤ 0. Both conditions hold at
every Z′-maximum (a Pareto improvement keeps every robust agent robust and raises Λ′; local optimality is Lemma Z0 of
`k4/zmove_pot.md`), and local optimality implies pool-optimality in every arrangement of the junk, so a proof that used
only them would be simpler. (Whether they also exclude the threat cycles of Lemma F is not shown; the earlier wording
"Lemma F's forest follows from either" was not proved and was removed in the PR #87 review.)

**Why it fails.** The repair from such a state can need a trade inside the key that lowers one free agent's value and
makes another robust (it raises r′). At core 4515 the two agents of that trade are the two helpers of compute/k4-rc's
nearest (two-helper) repair, which trades them in a variant that does not raise r′ (`k4/zmove_pot.md` §2, corrected in
the PR #87 review).

**Smallest failing configuration found.** Core 4515 of compute/k4-rc (n = 5, m = 12, f = 2, ω = 4), sets
[[0,2,4,8],[1,8,10,11],[3,9,10,11],[4,5,6,7],[5,6,7,9]], values [[4,3,8,2],[8,3,6,10],[2,8,3,4],[8,2,3,4],[3,2,4,8]].
Key: agent 0 on 4, agent 4 on 9, def* = 1. The state P = ({4}, {1,8}, {10,11}, {6,7}, {9}) has def 1, is
Pareto-maximal in its key and locally optimal for every free agent, and has no one-move repair. Agent 1 is not robust
(v₁({1,8}) = 11 < v₁({10,11}) = 16) and r′(P) = 2, while the key reaches r′ = 3. It is one of compute/k4-rc's stuck
states (`results/k4_rc/FAILURES.md` §2, on main since PR #89). Over all 1,076 profiles of the core, 42 states fail
this way (`results/k4_zmove_pot/run_rc.log`), with B₃ = {5,6}, {5,7} or {6,7} in place of {6,7}; at each of them a trade
of agents 1 and 2 raises r′ and lowers agent 2's value, and none that raises r′ is a Pareto improvement
(`results/k4_zmove_pot/referee_rc.log`). Every r′-maximal state, and every Z′-maximum, has a one-move repair. Nothing smaller
was found: the n = 4 and n = 5 hunts of `results/k4_zmove_pot/run_hunts_n4n5.log` have no failure of either form, nor
does any key at n = 3 (`results/k4_zmove_pot/run_n3.log`, exhaustive).

**Replay.** `python3 attempts/k4_zmove_pot_attempts.py pareto` (log `results/k4_zmove_pot/attempts.log`): main's
`k4/sx_keygraph.py` and main's repo-free `k4/rt4_n5_indep.py` agree on every deficit of the profile and on the absence of
a one-move repair at P.
