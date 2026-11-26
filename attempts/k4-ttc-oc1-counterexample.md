# Counterexample: Conjecture OC₁ fails at k = 4 (n = 6, m = 10)

Workstream `proof/k4-ttc` (`k4/ttc.md` §13). Status: **OC₁ is refuted** at k = 4, by two independent implementations.
- *SAT:* `oc_absorb.extends_A` over de_free's moves (`head_bign_climb.py`, rechecked by `oc1_false_check.py`).
- *Brute force:* `refute_oc1.py`, written from the definitions with no SAT and no shared code. It enumerates additions,
  chains and rings, with no cap on set or base sizes, and checks completions against the raw EFX₀ definition.

OC (free completion), MD, SD-C and TARGET₄ are not affected: the picks extend with two absorbers.

## The statement refuted

Conjecture OC₁ (K4.SDC.OC1, `k4/sdc.md` §29). In every instance with at most four relevant goods per agent, for every
order, either the serial-dictatorship picks have a one-absorber completion, or after one improving move the bases
have one.
- *One-absorber completion:* an EFX₀ allocation keeping every base in which at most one agent receives two or more
  goods outside the bases.
- *Improving move:* an addition, a chain or a ring of de_free.py.

## The instance

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

## What survives, and what this says

- **OC (free completion) holds here with zero chains**, and so do MD and SD-C. The failure is in the *one-absorber*
  shape of the completion, which OC₁ took from LB⁺ and Draft and Exchange.
- **OC₁ᵖ** (the natural repair, untested beyond these instances): count only absorbers that hold a pick; agents
  without a pick may take any number of junk goods. All 84 instances satisfy it with zero chains
  (`oc1_false_check.py`, `results/k4_ttc/oc1_false_check.log`).
- *Why n ≤ 5 never showed it.* It needs at least two pickless agents and three disjoint danger pairs held by frozen
  agents. This is the k = 4 analogue of the k-sensitivity session's PW family at k = 5, where one chain cannot fix
  several disjoint danger sets. Here the obstruction is the number of absorbers, not the number of chains.
- *Every statement built on OC₁ inherits this counterexample:* OC₁-H, OC₁-E, OC₁-ED (`k4/ttc.md` §8, §10), and the
  Hall session's "the count holds at the picks or after one chain" with a single owner.
