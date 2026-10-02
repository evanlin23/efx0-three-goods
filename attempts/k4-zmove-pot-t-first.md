# The potential (−t, r′, Λ′) for ZMOVE (proof/k4-zmove-pot)

**Candidate.** #41's potential with the pool threat first, restricted to one key: among the configurations of a key κ
with def*(κ) > 0, maximize (−t, r′, Λ′), where t is the number of frozen agents threatened by the pool alone
(`k4/c4min.md` §4). Then at some (or every) maximum Q, a (T3⁺) move with at most one helper from P_Q reaches def ≤ 0.
Putting t first protects the frozen agents before anything else, the order that `k4/c4min_reduce.md` §5 found necessary
for completability over all keys.

**Why it fails.** Inside one key, t first can force a state at which a free agent is not robust although a move inside
the key would make it robust; that state can be a stuck state.

**Smallest failing configuration found.** Core 4604 of compute/k4-rc (n = 5, m = 13, f = 1, ω = 4), sets
[[0,2,9,11],[1,6,10,12],[3,7,11,12],[4,8,11,12],[5,9,10,12]], values [[3,5,6,7],[6,5,4,8],[2,3,8,4],[3,2,8,4],[7,6,2,10]].
Key (11, agent 0), def* = 1. The maxima of (−t, r′, Λ′) have value (0, 3, 20) and a single state,
({11}, {12}, {3,7}, {4,8}, {5,9}): compute/k4-rc's stuck state, with no one-move repair. The Z′-maximum (value (4, 26) of
(r′, Λ′), so t ≥ 1 there) has one. All 369 profiles of the core fail the same way (`results/k4_zmove_pot/run_rc.log`, class TRL);
the n = 4 and n = 5 hunts have no failure (`run_hunts_n4n5.log`).

**Replay.** `python3 attempts/k4_zmove_pot_attempts.py trl` (two implementations, log `results/k4_zmove_pot/attempts.log`).
