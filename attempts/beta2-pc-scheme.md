# β = 2: private-collector scheme with the collector restricted to agents that have a private good

Workstream `proof/beta2`. An intermediate hypothesis on the way to Theorem D2 (`proofs/beta2.md`); it fails as soon as
the core has an agent without a private good (a Q-agent), which is what Lemma O and Case 3 of the proof handle.

**Scheme (PC).** The collector w is an agent with a private good. Every Q-agent holds two of its shared goods. Every
other agent e with a private good holds one of its shared goods, either together with its private good or alone; in
the second case (e ∈ J) its private good goes to w, whose bundle is {p_w} ∪ {p_e : e ∈ J}. Shared goods are assigned
bijectively.

**What survived.** For cores without Q-agents (π = n), PC covers every ranking profile: exhaustively for all β = 2
cores with n ≤ 7, and in general by the collector theorem (Theorem 5 and Case 1 of `proofs/beta2.md`).

**Where it breaks.** A Q-agent that always holds two goods never makes a good alone, so it blocks every chain of
alone goods the collector needs.

Smallest failing configuration (n = 3, m = 5): agents (a > b > c) 0: (0, 2, 3), 1: (1, 2, 4), 2: (0, 1, 2); goods 3 and 4
are private, agent 2 is a Q-agent. With w = 0 (private good 3 = c₀), w needs goods 0 and 2 alone; but agent 2 must
hold two of 0, 1, 2 while agent 1 takes one of 1, 2, so agent 2 holds 0 in a pair. With w = 1, symmetrically, good 1
is never alone. An EFX₀ allocation exists: agent 2 holds its top good 0 alone and the others two own goods each
(Lemma O): {2, 3}, {1, 4}, {0}.

At n = 3, 2 of the 3 β = 2 cores fail (78 and 144 of 216 profiles); at n = 4, 6 of 8.

Reproduce: `python attempts/beta2_schemes.py pc 3 4`
