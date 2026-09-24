# β = 2: collector scheme in which every shared good goes to an agent that values it

Workstream `proof/beta2`. The second intermediate hypothesis on the way to Theorem D2 (`proofs/beta2.md`); its only
failures are the dumbbells whose two Q-agents share a single bridge good, which Case 3c of the proof handles.

**Scheme (GPC).** As in `beta2-pc-scheme.md`, but the collector ("deficient agent") d may be any agent. Quotas: one
shared good for an agent with a private good, two for a Q-agent; d gets one shared good fewer than its quota and
collects its own private good (if any) and the private goods of J. Every shared good is held by an agent that
values it.

**What survived.** Exhaustively for n ≤ 7, every β = 2 core with at most one Q-agent, and every core with two Q-agents
except those below.

**Where it breaks.** Two Q-agents u, v joined by a single good g (a dumbbell whose bridge is u, g, v), both ranking g
first. Under GPC the goods of each loop can go only to that loop's agents and its Q-agent, and a loop has one good
more than it has agents. So the Q-agent holding g also holds a good of its loop (g is never alone), and the loop at
the other Q-agent is one good short; when its agents rank their private goods last, nobody there can absorb the
shortfall. Case 3c instead gives the spare good of one loop to the other Q-agent, which values it at 0.

Smallest failing configuration (n = 4, m = 7): agents (a > b > c) 0: (0, 1, 5), 1: (3, 4, 6), 2: (2, 0, 1), 3: (2, 3, 4);
goods 5, 6 private; agents 2, 3 are Q-agents with bridge good 2. If agent 2 holds 2, goods 0 and 1 (valued only by
agents 0 and 2) go to agents 0 and 2, and since agent 0 takes at most one, agent 2 holds 2 in a pair; then 3 and 4
go to agents 1 and 3: either agent 3 holds both and agent 1 (c = 6) needs 3 and 4 alone, or agent 3 holds one of them
(its b or c) and needs 2 alone. Either way someone is unsafe; the case "agent 3 holds 2" is symmetric. An EFX₀
allocation exists, and it gives a shared good to an agent that does not value it: {0, 5}, {4, 6}, {2}, {1, 3} (agent 3
holds its b = 3 plus good 1, and a = 2 is alone). Case 3c of the proof builds exactly this.

At n = 4, 1 of 8 β = 2 cores fails (64 of 1,296 profiles); at n = 5, 1 of 15 (208 of 7,776); at n = 6 and 7, 2 cores
each, all of this shape.

Reproduce: `python attempts/beta2_schemes.py gpc 4 5`
