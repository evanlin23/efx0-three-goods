# OC₁ as tested fails at k = 3 (n = 5, m = 9): the picks need two chains

Workstream `proof/k4-k3-oc1` (`k4/k3_oc1.md` §9).

**The claim tested.** Conjecture OC₁ (`k4/sdc.md` §29, K4.SDC.OC1): "for every order, the picks have a one-absorber
completion, or after one improving chain the bases have one". It is stated for every instance with at most four
relevant goods per agent, so k = 3 instances are included. All of §29's evidence uses `k4/sdc/de_free.py`. There a
chain stops at an agent that holds nothing (`if ... not B[x_t]: return`), as Draft and Exchange's chains do.

**Counterexample** (k = 3, strictly balanced; values a, b, c = 10, 8, 7 for every agent, though any strictly balanced
values give the same result):

| agent | goods a > b > c |
|---|---|
| 0 | 0 > 1 > 2 |
| 1 | 0 > 1 > 2 |
| 2 | 0 > 3 > 4 |
| 3 | 1 > 5 > 6 |
| 4 | 2 > 7 > 8 |

**Order (2, 3, 4, 0, 1).**
- Agents 2, 3, 4 take their tops 0, 1, 2; agents 0 and 1 find all their goods taken and get nothing.
- Goods 3–8 are unallocated: each is a private good of agent 2, 3 or 4.
- Agents 2, 3, 4 are frozen, since the empty-handed agents want their goods. They cannot take junk: a two-good bundle
  {top, h} would be envied by agent 0 or 1, which cannot be compensated.
- So the six junk goods go to agents 0 and 1, and with one absorber, one of them gets at least five. Five goods of
  three private pairs contain two complete pairs, and the owner of a complete pair sees b + c > a in a bundle of three
  or more goods.

The independent replay (`python3 attempts/k4_k3oc1_oc1_cex.py`: no repository code, no SAT, the raw EFX₀
definition, every chain of every length and every set) finds:
1. the picks have no one-absorber completion;
2. of the 51 improving chains in de_free's sense, **none** gives a one-absorber completion. A chain repairs one agent
   of 2, 3, 4 (it takes its private pair and passes its top to agent 0 or 1), and the other two still need an
   absorber each;
3. two such chains suffice, e.g. bases ({1}, ∅, {2, 3, 4}, {5, 6}, {7, 8});
4. with the free completion (any number of absorbers; Conjecture OC of §29), 6 of the 51 chains suffice.

The exhaustive run over DE's general core case at n = 5 (`k4/k3oc1/oc1_general.py 5 0`: all 652 hypergraph classes,
every profile and order) finds 288 hard drafts that no chain of this kind repairs. All 288 belong to this one
hypergraph class (`results/k4_k3oc1/oc1_general_5_dead0_*.log`).

**What survives.**
- *The literal text of §29.* There "x_i takes B_{x_{i−1}} ∪ H_i" with B_{x_{i−1}} = ∅ is allowed, so a chain may pass
  through an empty-handed agent. Its successor then takes only junk, so a second sub-chain starts there. Then 34
  chains repair, e.g. the chain 3 → 1 → 4 → 0: agent 3 takes {5, 6}, agent 1 receives good 1, agent 4 receives nothing
  from agent 1 and takes {7, 8}, and agent 0 receives good 2. All 288 drafts are repaired this way.
- *The free completion* (Conjecture OC): all 288.
- *The ledger's cores.* The instance is not one: agents 2, 3, 4 each have two private goods, so rule R2 (PROMPT.md L2)
  peels them. On every core tested (`k4/k3_oc1.md` §1) OC₁ holds with de_free's chains.

**Consequence for K4.SDC.OC1.** Either restrict the conjecture to cores, which is enough for TARGET₄ by peeling, or
say explicitly that a chain may pass through an agent holding nothing. Every k = 4 data set of §29 was tested with
de_free's chains. The screen and suite sets are cores or near-cores, which is why this case never appeared there.
