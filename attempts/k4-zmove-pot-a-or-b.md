# Lemma A or B at some Z′-maximum, after re-choosing the arrangement (proof/k4-zmove-pot)

**Candidate.** At f = 1, at some Z′-maximum of every key with def* > 0, in some arrangement of the junk into fillers and
pool (all of which are Z′-maxima, `k4/zmove_pot.md` Lemma Z0), Lemma A or Lemma B with threat path length 1 of
`k4/sx.md` §3 applies. Re-choosing the arrangement can move a θ-b terminal's third lower good into another agent's
slot, which removes θ-b (`k4/zmove_pot.md` Lemma S′); the candidate asks whether that always replaces Lemmas C and C′.

**Why it fails.** When no free agent holds a single good there is no slot, the arrangement is unique, and two θ-b
terminal leaves need Lemma C or C′.

**Smallest failing configuration found.** n = 3, m = 7, ω = 2: sets [[0,2,5,6],[1,4,5,6],[3,4,5,6]], values
[[3,6,2,10],[6,3,2,10],[3,5,6,7]]. Key (6, agent 2), def* = 1, a single Z′-maximum Q = {0: {0,2}, 1: {1,4}}, L = {3,5}.
Both free agents are terminal leaves and θ-b, so Lemma A fails at both, and there is no non-leaf terminal for Lemma B.
A plain (T3) move still reaches def ≤ 0 (Lemmas C and C′; `k4/zmove_pot.md` Lemmas C₁, C₂).

**Replay.** `python3 attempts/k4_zmove_pot_attempts.py ab` (two implementations, log `results/k4_zmove_pot/attempts.log`).
