# Hand-checkable counterexamples

## X1 (smallest): a core with n = 3 where bundles of at most two goods fail
Found in Step 0: the cores with m ≤ n + 3 had been delegated to Mahara and never searched. `src/c2_small.py` (log `results/c2_small.log`) finds this core both with the SAT search of `frontier.py` and with a SAT-free brute force over every allocation with bundles ≤ 2 (raw EFX₀ definition). It fails for 14 of the 216 ranking profiles; no core with n = 2 fails, so n = 3 is the smallest possible.
Agents (a > b > c): 0: (0, 1, 2), 1: (0, 1, 3), 2: (0, 1, 4). Goods 2, 3, 4 are private; n = 3, m = 5 = 2n − 1 (β = 2, a subdivided theta).
*No EFX₀ allocation has all bundles of at most two goods.* By L7 exactly 2n − m − 2e = 1 − 2e goods are alone, so e = 0 and one good is alone. Good 0 is everyone's top and has one holder, so two agents are not in case T. Case E needs three alone goods and case C two, so each of these two agents is in case P (holds {1, c_i}) or B (holds 1): both hold good 1. Contradiction.
*An EFX₀ allocation:* {0}, {1}, {2, 3, 4}. Agent 0 holds a, and its b = 1 and c = 2 are not together (T); agent 1 holds b = 1 with a = 0 alone (B); agent 2 holds c = 4 with a = 0 and b = 1 alone (C).

## X2 (smallest): conjecture A fails at n = 4, m = 6 = 2n − 2
Also found in Step 0, in the range m ≤ n + 3 that had not been searched: 3 of the 16 connected cores with n = 4, m = 6 have a profile with no EFX₀ allocation of bundles ≤ 2 (SAT search and brute force agree; `results/c2_small.log`). One of them:
Agents (a > b > c): 0: (0, 2, 3), 1: (1, 2, 4), 2: (1, 2, 5), 3: (0, 1, 2). Goods 3, 4, 5 are private.
*No EFX₀ allocation has all bundles of at most two goods.* Now 2n − m − 2e = 2 − 2e goods are alone. Tops collide on good 0 (agents 0, 3) and good 1 (agents 1, 2), so some u ∈ {0, 3} and some w ∈ {1, 2} are not in case T. Every P-bundle ({2, 3}, {2, 4}, {2, 5}, {1, 2}) contains good 2, so at most one agent is in case P. If e = 1, no good is alone, cases B, C, E are out and u, w both need P: contradiction. So e = 0 and exactly two goods are alone; E (three alone goods) is out.
Agent w (b = 2) is in case P or B, both of which hold good 2, or in case C, which needs goods 1 and 2 alone.
- If agent 0 is not in case T, take u = 0 (b = 2): like w, it holds good 2 (P, B) or is in case C and needs good 2 and its top alone. At least one of u, w does not hold good 2, so it is in case C. If the other holds good 2, that good is alone, so the holder's bundle is {2}: case B, which needs its top alone; otherwise the other is in case C too. Either way both tops 0 and 1 and good 2 are alone: three alone goods. Contradiction.
- Otherwise agent 0 holds good 0 and agent 3 is not in case T. Case P for agent 3 is {1, 2}, leaving w neither good 2 nor an alone good 2. Case C for agent 3 holds good 2 and needs 0 and 1 alone; w then needs good 2 alone, a third alone good. Case B for agent 3 holds good 1 and needs good 0 alone; agents 1 and 2 are then both not in case T, at least one of them does not hold good 2, and that one is in case C, which needs goods 1 and 2 alone: with good 0, three alone goods. Contradiction.

*An EFX₀ allocation:* {0}, {1}, {2}, {3, 4, 5}. Agents 0 and 1 hold their tops, with b = 2 alone (T); agent 2 holds b = 2 with a = 1 alone (B); agent 3 holds none of its goods, and 0, 1, 2 are all alone (E).

## X3: outside cores, bundles of at most two goods can fail
Four agents with identical additive valuations x = 4, y = 3, z = 2 (balanced: 4 < 3 + 2), plus three goods worthless to everyone: n = 4, m = 6 = 2n − 2.
With all bundles of at most two goods, an agent holding none of x, y, z is safe only if x, y, z each sit alone (L5, case E). If some agent held two of x, y, z, at least two agents would hold none of them and need all three alone: impossible. So three agents hold one each, the fourth holds none, x, y, z are singletons, and the fourth agent must take all three worthless goods: a bundle of three.
An EFX₀ allocation exists: {x}, {y}, {z}, {w1, w2, w3} (cases T, B, C, E).

## X2: the n = 6, m = 10 example refuting conjecture A
Agents (a > b > c): 0: (1, 0, 6), 1: (1, 0, 7), 2: (2, 0, 8), 3: (3, 0, 9), 4: (2, 4, 5), 5: (3, 4, 5). Goods 6–9 are private.
EFX₀ allocation: {0, 6}, {1, 7, 8, 9}, {2}, {3}, {4}, {5}. Agent 0 holds its b and c (P); agent 1 holds a with its c (T); agents 2 and 3 hold their tops, and their b = 0 and c ∈ {8, 9} are never together in a bundle of three or more (T); agent 4 holds b = 4 with a = 2 alone (B); agent 5 holds c = 5 with a = 3 and b = 4 alone (C).
No allocation with all bundles of at most two goods exists: SAT, confirmed by the independent encoding in src/verify_fail.py, and by the hand proof below (Step 0).

**Hand proof that no EFX₀ allocation has all bundles of at most two goods.** Write a_i, b_i, c_i for agent i's ranked goods. With all bundles of size ≤ 2, no bundle has ≥ 3 goods, so by L5 agent i is safe iff it is in case
T (holds a_i), P (holds {b_i, c_i}), B (holds b_i, a_i alone), C (holds c_i, a_i and b_i alone) or E (a_i, b_i, c_i alone).
By L7 (the counting needs no connectivity), with e empty bundles exactly s = 2n − m − 2e = 2 − 2e goods are alone, so e ≤ 1 and s ≤ 2.

1. *Collisions.* The top goods are a_0 = a_1 = 1, a_2 = a_4 = 2, a_3 = a_5 = 3. A good has one holder, so in each of the disjoint pairs {0, 1}, {2, 4}, {3, 5} at least one agent is not in case T: at least 3 agents are not in case T.
2. *P-capacity.* The P-bundles are {0, 6}, {0, 7}, {0, 8}, {0, 9} (agents 0–3, all containing good 0) and {4, 5} (agents 4 and 5). So at most one of agents 0–3 and at most one of agents 4, 5 is in case P: at most 2 agents in all.
3. *E is impossible*: it needs three alone goods, and s ≤ 2. *C* needs two alone goods, so when some agent is in case C the alone goods are exactly its a and b.
4. *e = 1.* Then s = 0, so cases B, C, E (which need a alone) are impossible, every agent is in case T or P, and by 1 and 2 at least 3 agents need P while at most 2 can have it. Contradiction. So e = 0 and s = 2.
5. *e = 0, no agent among 0–3 in case C.* Cases P and B of agents 0–3 need good 0 (b_i = 0), which one agent holds, so at most one of agents 0–3 is not in case T. By 1 it is agent 0 or 1, so agents 2 and 3 are in case T: agent 2 holds good 2 and agent 3 holds good 3, and agents 4 and 5 (tops 2 and 3) are not in case T. If one of them is in case P it holds both goods 4 and 5, which are the goods the other needs in cases P, B and C (b = 4, c = 5). So neither is in case P, both are in case B or C, and goods 2 and 3 (their tops) are alone: these are the two alone goods. Then good 4 is not alone, so neither agent is in case C; both are in case B and both hold good 4. Contradiction.
6. *e = 0, some agent k among 0–3 in case C.* By 3 the alone goods are exactly {0} and {a_k}. No agent among 0–3 is then in case P ({0, c_i} would contain the alone good 0), and one in case B holds {0} and needs a_i alone, so a_i = a_k; one in case C also needs a_i = a_k. So every agent among 0–3 not in case T has top a_k.
   - a_k = 1: agents 2 and 3 (tops 2, 3) are in case T, holding goods 2 and 3, so agents 4 and 5 are not in case T. Case C is out for both (it would need good 4 alone). Case B for agent 4 (resp. 5) needs good 2 (resp. 3) alone, which is not among {0, 1}. So both are in case P and both hold {4, 5}. Contradiction.
   - a_k = 2 or 3: agents 0 and 1 (top 1 ≠ a_k) are both in case T, and both hold good 1. Contradiction.

Every case is contradictory, so every EFX₀ allocation of this instance has a bundle of at least three goods. `src/step0_checks.py` confirms this by brute force over all 4,082,400 allocations with bundles of at most two goods, using the raw EFX₀ definition.
