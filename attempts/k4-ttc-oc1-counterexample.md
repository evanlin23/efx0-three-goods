# Counterexample: Conjecture OC₁ as stated fails for non-core instances (k = 4, and even k = 3)

Workstream `proof/k4-ttc` (`k4/ttc.md` §13). Status: **OC₁, as literally stated in `k4/sdc.md` §29 ("every instance
with at most four relevant goods per agent"), is refuted.** No counterexample is a core: every instance found
violates the core conditions (R1 or R2 applies, or there are ties). **OC₁ on strict connected cores, the form that
implies TARGET₄ through the peeling reduction, is not refuted.** OC (free completion), MD, SD-C and TARGET₄ are not
affected.

Two independent implementations agree:
- *SAT:* `oc_absorb.extends_A` over de_free's moves (`head_bign_climb.py`, rechecked by `oc1_false_check.py`);
- *brute force:* `refute_oc1.py`, written from the definitions with no SAT and no shared code. It enumerates
  additions, chains and rings, with no cap on set or base sizes, and checks completions against the raw EFX₀
  definition.

**Scope.** `k4/c4_verify_H/hcore.py`'s `is_core4` rejects all 84 instances of the climb:
- each has a top-heavy agent, which R1 peels; in the instance below, agent 4 values 9, 3, 6 at 10, 7, 2, and
  10 ≥ 7 + 2;
- most also have ties (equal disjoint subset sums), or two private goods with p + q ≥ s + t.

The smaller family below (n = 5, m = 9, every agent with three goods, strict and balanced) fails only because agents
0–2 have two private goods worth at least their pick, so R2 peels them. So the counting obstruction needs a non-core
instance in every example found so far. Whether it can occur inside a strict core is open; a core-constrained climb is
`k4/ttc.md` §13.

## The statement refuted

Conjecture OC₁ (K4.SDC.OC1, `k4/sdc.md` §29). In every instance with at most four relevant goods per agent, for every
order, either the serial-dictatorship picks have a one-absorber completion, or after one improving move the bases
have one.
- *One-absorber completion:* an EFX₀ allocation keeping every base in which at most one agent receives two or more
  goods outside the bases.
- *Improving move:* an addition, a chain or a ring of de_free.py.

## The instance (n = 6, m = 10, k = 4; not a core)

Found by `k4/ttc/head_bign_climb.py 6 300 10 41 6 6 ends seeded`, which climbs on values and incidences starting
from the OC₁-H counterexample of `attempts/k4-ttc-head-owner.md` (log `results/k4_ttc/head_bign_climb_ends_seeded.log`).
The climb produced 84 distinct instances of this kind, saved in `results/k4_ttc/oc1_counterexamples.json`.

| agent | goods (value) | pick (order 0, 1, …, 5) |
|---|---|---|
| 0 | 0 (2), 2 (7), 3 (8), 1 (3) | 3 |
| 1 | 1 (3), 4 (6), 5 (4), 9 (9) | 9 |
| 2 | 1 (12), 2 (2), 0 (4), 8 (8) | 1 |
| 3 | 1 (12), 6 (6), 7 (3), 8 (4) | 6 |
| 4 | 3 (7), 6 (2), 9 (10) | none |
| 5 | 1 (7), 3 (8), 6 (4), 9 (1) | none |

m = 10, and the junk is {0, 2, 4, 5, 7, 8}.

## Why the picks have no one-absorber completion

**Frozen agents.** Agents 4 and 5 hold nothing and want every pick they value. So the picks of 0, 1, 2 and 3 are
wanted, and by Lemma 2(a) of `k4/sdc.md` §2 these agents keep their picks alone: they take no junk.

**Danger pairs.** The junk splits into three disjoint pairs, each worth more to an agent than its pick:
- {0, 2} to agent 0 (2 + 7 = 9 > 8);
- {4, 5} to agent 1 (6 + 4 = 10 > 9);
- {7, 8} to agent 3 (3 + 4 = 7 > 6).

A bundle of three or more goods may not contain a whole pair (Lemma 2(b)).

**The count.** All six junk goods must go to agents 4 and 5.
- With one absorber, it takes at most one good of each pair: three goods.
- The other agent may take one good.
- That places four goods, not six.

**Free completion.** There are exactly 8 free completions, and each gives three junk goods to agent 4 and three to
agent 5, one of each pair. For example ({3}, {9}, {1}, {6}, {0, 4, 7}, {2, 5, 8}).

## Why no move helps

`python3 k4/ttc/refute_oc1.py` enumerates every move: 97 in all, namely 16 additions, 71 chains and 10 rings. After
none of them do the bases have a one-absorber completion. After 6 of them the bases have a free completion. The
replay is logged in `results/k4_ttc/refute_oc1.log` and was repeated on 6 more of the 84 instances. Take the chain (0, 4), for example: agent 0 takes its danger pair {0, 2}, and agent 4 takes agent 0's pick 3.
- Agent 4 is now frozen itself: agent 5 wants 3.
- The junk {4, 5, 7, 8} still holds the two danger pairs {4, 5} and {7, 8}.
- Besides the absorber, only agent 0 (now holding its pair) can take a junk good.

The count fails again, by one good.

## A smaller family: n = 5, m = 9, k = 3, strict and balanced (not a core: R2 applies)

`results/k4_ttc/oc1_counterexample_n5.json`, first entry:
- agents 0, 1, 2 value {i, 3 + 2i, 4 + 2i} at (10, 6, 5);
- agents 3 and 4 value {0, 1, 2} at (4, 3, 2) and (2, 4, 3);
- order (0, 1, 2, 3, 4), picks (0, 1, 2, none, none).

The same count applies:
- three frozen agents, each with a disjoint junk danger pair worth 11 > 10;
- two pickless agents, so two absorbers are needed.

`refute_oc1.py` on this instance: 56 moves (9 additions, 42 chains, 5 rings), none with a one-absorber completion, 6
with a free completion. 36 value variants were checked by SAT. Each of agents 0–2 has two private goods with
6 + 5 ≥ 10, so R2 would peel it (P = its private pair) before any core argument applies.

## What survives, and what this says

- **OC (free completion) holds here with zero chains**, and so do MD and SD-C. The failure is in the *one-absorber*
  shape of the completion, which OC₁ took from LB⁺ and Draft and Exchange.
- **OC₁ᵖ** (the natural repair, untested beyond these instances): count only absorbers that hold a pick; agents
  without a pick may take any number of junk goods. All 84 instances satisfy it with zero chains
  (`oc1_false_check.py`, `results/k4_ttc/oc1_false_check.log`).
- *Why n ≤ 5 never showed it.* It needs at least two pickless agents and three disjoint danger pairs held by frozen
  agents. This is the k = 4 analogue of the k-sensitivity session's PW family at k = 5, where one chain cannot fix
  several disjoint danger sets. Here the obstruction is the number of absorbers, not the number of chains.
- *Every one-absorber statement for arbitrary instances inherits this counterexample:* OC₁-H, OC₁-E, OC₁-ED
  (`k4/ttc.md` §8, §10), OC₁-ED\* and Finding S\* of the Hall session. *On cores, none of them is refuted by it.*
- *Why the core conditions may matter.* The pigeonhole needs frozen agents whose junk danger sets are private or
  nearly private, and pickless agents whose every good is picked. R2 removes agents with two valuable private goods,
  and R1 removes top-heavy agents. In both examples the counted danger pairs are private goods of the frozen agents,
  and in the n = 6 instance one pickless agent is top-heavy.
