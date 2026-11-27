# Lemma PL does not settle the other dangerous agents when the danger sets are disjoint

Workstream `proof/k4-oc1max-multi` (`k4/oc1max_multi.md` §4).

**Idea** (step 2 of the coordinator's plan). One chain repairs one dangerous agent's danger set. By Lemma PL
(`k4/ksens.md`, refereed CORRECT), each other dangerous agent then has at most one pool good left, which is never a
danger set at k ≤ 4. So after one ED chain the remaining demands are trivial.

**Result: false for disjoint junk sets.** Lemma PL(c) bounds the leftover of an agent z only when z values two goods
of the set H that the chain gives away. If J_d ∩ H₀ = ∅, the chain does not touch d's junk, and a truly dangerous d
keeps its whole danger set in the pool.

**Smallest failing configuration on the data:** n4_3#211.0 (random profile of an n = 5 core; n = 5, m = 9).
- sets [[0,2,4,7],[1,3,5,7],[4,6,8],[5,6,7,8],[5,6,8]];
- values [[15,16,13,26],[15,18,29,16],[2,28,29],[19,13,30,14],[29,27,11]];
- order (0, 1, 3, 4, 2), picks (7, 5, 4, 8, 6), J = {0, 1, 2, 3};
- D = D_T = {0, 1}. The junk sets are disjoint: agent 0 has {0, 2}, worth 31 > 26; agent 1 has {1, 3}, worth
  33 > 29.

Every canonical chain from 0 or 1, with every improving H₀, leaves the other agent frozen and threatened by the pool
(DEMAND):
- after any chain from 0, agent 1 is still wanted by 4 and still values {1, 3};
- after the chain from 1, agent 0 is still wanted by 3 and still values {0, 2}.

The start is still repaired, by a slot. After the chain 0 → 3 → 2, the head 2 takes junk good 1, and that breaks agent
1's danger set: [[0,2,3,4],[5],[8,1],[7],[6]].

On the data, 95 starts whose dangerous agents are all truly dangerous, with pairwise disjoint junk sets, have this
property. So what step 2 needs is a slot count, sub-lemma SLOT in `k4/oc1max_multi.md` §7, not a leftover bound.

**Repro.** `python3 k4/oc1max_multi/repro.py disjoint`.
