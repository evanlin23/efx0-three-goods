# Hand-checkable counterexamples

## X3: outside cores, bundles of at most two goods can fail
Four agents with identical additive valuations x = 4, y = 3, z = 2 (balanced: 4 < 3 + 2), plus three goods worthless to everyone: n = 4, m = 6 = 2n − 2.
With all bundles of at most two goods, an agent holding none of x, y, z is safe only if x, y, z each sit alone (L5, case E). If some agent held two of x, y, z, at least two agents would hold none of them and need all three alone: impossible. So three agents hold one each, the fourth holds none, x, y, z are singletons, and the fourth agent must take all three worthless goods: a bundle of three.
An EFX₀ allocation exists: {x}, {y}, {z}, {w1, w2, w3} (cases T, B, C, E).

## X2: the n = 6, m = 10 example refuting conjecture A
Agents (a > b > c): 0: (1, 0, 6), 1: (1, 0, 7), 2: (2, 0, 8), 3: (3, 0, 9), 4: (2, 4, 5), 5: (3, 4, 5). Goods 6–9 are private.
EFX₀ allocation: {0, 6}, {1, 7, 8, 9}, {2}, {3}, {4}, {5}. Agent 0 holds its b and c (P); agent 1 holds a with its c (T); agents 2 and 3 hold their tops, and their b = 0 and c ∈ {8, 9} are never together in a bundle of three or more (T); agent 4 holds b = 4 with a = 2 alone (B); agent 5 holds c = 5 with a = 3 and b = 4 alone (C).
No allocation with all bundles of at most two goods exists: SAT, confirmed by the independent encoding in src/verify_fail.py. Informal reason: three top-collisions (goods 1, 2, 3); the bottom pairs of agents 0–3 all contain good 0 and agents 4, 5 share one bottom pair, so at most two collisions can be fixed by case P; the third needs a chain, and by L7 a size-≤2 allocation of 10 goods among 6 agents leaves at most 2 goods alone. A complete hand proof is an open item.
