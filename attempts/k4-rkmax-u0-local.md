# Attempt: HS-MAX in class U0 by a local argument (proof/k4-rkmax)

**Setting** (`k4/rkmax.md` §6). Class U0 consists of the perfect starts with:
- one receiver z;
- Θ(z) = {k}, i.e. k is the only dangerous agent threatened by J ∪ {Y_z};
- no truly dangerous agent.

Corollary U1 already covers the case where k is truly dangerous. In U0, Lemma S′ reduces to a two-agent condition:
- take a longest canonical chain from k (it ends at z);
- z is unfrozen after the chain;
- the only agent that W = (J ∪ {Y_z}) ∖ {h} can threaten is z itself.

So S′ fails only through a competition for junk between k and z. k needs Y_z and some junk good j to beat p_k. z,
holding the good a it receives on the chain, is threatened by {Y_z, j, …}.

**Idea.** Show that this conflict, at a σ-maximal start, forces a σ-raising change between k and z. Examples: "z takes
Y_k, k falls back to Y_z" (a swap), or "k takes j, z takes Y_k" (a chain). Lemma 2AG gives the exact rank test for
both. That would prove HS-MAX (and HS-MAX′) in U0 from the local data of k and z alone.

**Result: impossible as a local argument.** `python3 k4/rkmax/rk_u0_local.py 20` (log
`results/k4_rkmax/rk_u0_local_n4.log`) samples 1 in 20 of the n = 4 export profiles:
- 5,763 U0 residue starts (hard, no Lemma S′ case);
- at 436 of them no σ-raising maximum matching differs from Y only on {k, z};
- at 122, none differs only on k, z and the agents of the longest canonical chains.

The ranks of k and z are logically independent of the value conflict, so no rank inequality between them follows from
it.

**Smallest failing configuration** (n = 4, m = 7):
- sets [[0,1,2,6],[1,2,5,6],[3,4,5,6],[3,4,5,6]], vals [[1,4,8,6],[2,8,7,4],[3,5,7,6],[4,5,8,6]], picks (2, 5, 4, 6);
- ranks (1, 2, 3, 2), junk {0, 1, 3}, z = 2, k = 3, canonical chain (3, 2) with a = 6;
- *the conflict:* k needs 3 and 4 = Y_z (4 + 5 > 6). z, holding 6, is threatened by {3, 4, …} (3 + 5 > 6);
- *σ-raising inside {k, z}:* none. The swap gives equal rank intervals, and "k takes 3, z takes 6" lowers σ;
- *the only σ-raising changes* run through z's top good 5, held by agent 1, whose top good 2 is held by agent 0. Agent
  0 falls back to the junk good 1 (rank 1 → 3), agent 1 takes 2 (2 → 1), z takes 5 (3 → 1), so σ rises at level 1;
- OC₁ holds there by a 3-ring through k and the two outside agents: agent 0 takes Y_3 = 6 plus the junk good 1,
  agent 1 takes Y_0 = 2, and k = 3 takes Y_1 = 5. Afterwards agent 0 absorbs the junk good 0 and z takes the junk good
  3 (rklib, raw EFX₀).

**Lesson.** A proof of HS-MAX′ in U0 has to use the agents outside the conflict, through hardness. The U0 start is
hard only because the other agents block every completion, and σ-maximality has to be applied to them. The
U0-targeted climbs never bring a U0 start closer than three σ-better maximum matchings to σ-maximality
(`results/k4_rkmax/rk_climb_sink1_n4_u0.log`), so the global argument has slack.

Reproduce: `python3 k4/rkmax/rk_u0_local.py 20`; `python3 k4/rkmax/rk_u0_class.py 10`.
