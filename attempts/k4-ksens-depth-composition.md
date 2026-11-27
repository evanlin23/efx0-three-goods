# A depth-two version of RD5, against two rounds: fails

Workstream `proof/k4-ksens` (`k4/ksens.md` §6, §8). Idea: RD5 needs two rounds because agent 0 must collect two other
agents' picks, 3 and 4, and one of them has to be released by an earlier move.
- Make the holder of 4 (agent 2) movable only by collecting two foreign picks c and c′ itself.
- C, the holder of c, gains only from the pick of a new agent X, which gains only from junk of its own.
- C′, the holder of c′, gains only from the pick of a new agent U, which likewise gains only from junk.
- Then c′ is released in round 1 (U → C′), good 4 in round 2 (X → C → agent 2), and agent 0 collects in round 3.

**Why it fails** (`k4/ksens/fam_depth.py`, `results/k4_ksens/fam_depth.log`).
- In both variants (agent 2 keeping or dropping its RD5 values for goods 1, 2, 3), the picks of the designed order
  already have a one-absorber completion, with no chain at all.
- The new agents C, X, C′ and U are unfrozen, so each offers a free slot: a two-good bundle of its pick and one junk
  good.
- Those slots absorb the shared pool goods {0, 5} that made agents 0 and 3 need repairs in RD5.

**Smallest failing configuration:** the n = 8, m = 15 design in `fam_depth.py`, with the picks extending directly.

**What a working design would need:** every added agent frozen (its pick wanted). Every want path ends at an
unfrozen agent, though, and that agent is again a slot. Climbs against two rounds from RD5 plus two random agents
(n = 6) are in `results/k4_ksens/climb_rd2mx_n6k*.log`.

Reproduce: `python3 k4/ksens/fam_depth.py`.
