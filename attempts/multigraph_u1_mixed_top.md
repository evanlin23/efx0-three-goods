# U1 when a top has three valuers but is not everyone's top

**Idea.** Run the construction of `proofs/multigraph_extension.md` (popular matching, then the moves Up, U1 and R1, then the dump of Lemma 4.2) on every core, not just on classes 𝒰 and 𝒯. The dump lemma (Lemma 2.1) needs only invariants I1 and I2, but the facts behind Lemma 4.2 (F1, F2) use I3: every envied agent holds its top.

**Where it breaks.** Lemma 3.1 needs this: whenever U1 hands the top a_w of an envied agent w to an envier k, and a_w has a third valuer, k ranks a_w first. That holds in class 𝒰 (every valuer of a good with three or more valuers ranks it first) and trivially in class 𝒯 (no such good is a top). When a good with three or more valuers is the top of some valuers but not others, the other enviers of w now envy k, which may hold a good that is not its top, while k itself still envies someone. So k both envies and is envied, and I3 fails. This is the core form of the paper's obstacle "moving a good drags a third agent's envy along" (digest §4 item 5).

Smallest failing configuration: none at n = 3; first at n = 4, m = 5 (62 profiles). Core [[1, 2, 3], [1, 2, 4], [0, 1, 2], [0, 1, 2]], rankings (a, b, c):
- agent 0: 1, 2, 3;
- agent 1: 1, 4, 2;
- agent 2: 0, 1, 2;
- agent 3: 0, 1, 2.

Good 1 has four valuers; it is the top of agents 0 and 1 and the b of agents 2 and 3.
- The popular matching gives agent 0 good 1, agent 1 good 4, agent 2 good 2 and agent 3 good 0.
- U1 applies to agent 0, which is envied, holds its top, has its b (good 2) held by its envier agent 2, and its c (good 3) free. Agent 0 takes {2, 3}, and agent 2 takes good 1, its b.
- Agent 1 still envies the holder of good 1 (now agent 2), and agent 2 envies agent 3 (good 0). I3 fails.

EFX₀ allocations exist for this core (R1), so this is a failure of the proof's invariant, not of TARGET. Choosing the envier cannot help here: agent 2 is the only envier of agent 0 that holds one of agent 0's goods b, c.

**What would be needed.** A repair step after such a U1, for example the paper's Reduce Trees (Lemma 4.6), which in its general form hits the same third-valuer problem. Alternatively, restrict U1 to enviers that rank a_w first, and handle an envied agent whose b and c are free but whose only eligible envier ranks its top second.

Reproduce: `python attempts/multigraph_limits.py u1` (searches n = 3, 4 and prints the first example; under a second).
