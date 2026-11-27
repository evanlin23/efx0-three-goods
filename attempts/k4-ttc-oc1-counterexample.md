# Counterexample: Conjecture OC₁ fails on strict connected k = 4 cores (n = 5 and n = 6), but only with agents holding two private goods

Workstream `proof/k4-ttc` (`k4/ttc.md` §13). **Status:**
- *Refuted:* OC₁ (K4.SDC.OC1, `k4/sdc.md` §29), also on strict connected cores.
- *Open:* OC₁ on the class that matters for TARGET₄. Every core counterexample has agents with **two private goods**,
  and K4.MC2 (CERTIFIED) excludes such agents from a minimal counterexample to TARGET₄. So OC₁ restricted to strict
  connected cores without an agent holding two private goods (the K4.MC2 class) is not refuted, and it still implies
  TARGET₄.
- *Not affected:* OC (free completion), MD, SD-C and TARGET₄. On every counterexample, OC₁ᵖ holds as well. That
  variant counts absorbers only among agents holding a base; agents with an empty base may take any number of junk
  goods.

**The core counterexamples:**
- **n = 5, m = 9** (this note; built by hand): every 4-good agent has two private goods, which are exactly its danger
  pair.
- **n = 6, m = 10** (found by the Hall session, `claude/k4-oc1-hall`, `k4/oc1_hall.md` §16): the strict perturbations
  B< and B> of instance 36 of the climb's list `results/k4_ttc/oc1_counterexamples.json`. Agents 1 and 3 have two
  private goods. OC₁ fails for 24 of the 720 orders. Rechecked here in `results/k4_ttc/hall_core_cex_check.log`:
  `is_core4` returns [], and OC₁ᵖ holds on all 24 orders.
- Both were verified independently by the coordinator (`k4/sdc/oc1_core_cex_verify.py` on its branch) and by the Hall
  session (`k4/oc1_hall/verify_ttc_cex.py`).

**Update (burst 5): an MC2-class counterexample exists.** It refutes OC (free completion) as well as OC₁, for one
order; see `attempts/k4-ttc-oc-every-order.md`. In it, every frozen agent's junk is a danger triangle. R1-priority and
maximum-matching orders are not refuted.

**In the K4.MC2 class the pigeonhole breaks in the first natural construction.** Make each danger pair {aᵢ, bᵢ} of
the n = 5 core share bᵢ with the next frozen agent at value 2 (`results/k4_ttc/oc1_mc2_candidate.json`). Then OC₁
holds: a chain lets agent i take {aᵢ, bᵢ, bᵢ₋₁}, which breaks two danger pairs at once. Climbs inside the class are in
`k4/ttc.md` §13.

The checks of the n = 5 counterexample:
- *SAT:* `oc_absorb.extends_A` over de_free's moves.
- *Brute force:* `k4/ttc/refute_oc1.py`, written from the definitions with no SAT and no shared code. It enumerates
  every addition, chain and ring, with no cap on set or base sizes, and checks completions against the raw EFX₀
  definition.
- *By hand:* the core conditions, and the count at the picks below.

## The statement refuted

OC₁: for every order, either the serial-dictatorship picks have a one-absorber completion, or after one improving move
(an addition, chain or ring of `k4/sdc/de_free.py`) the bases have one. A *one-absorber completion* is an EFX₀
allocation keeping every base, in which at most one agent receives two or more goods outside the bases.

## The core (`results/k4_ttc/oc1_core_candidate.json`)

Goods: y₀ = 0, y₁ = 1, y₂ = 2, and the private pairs {a₀, b₀} = {3, 4}, {a₁, b₁} = {5, 6}, {a₂, b₂} = {7, 8}.

| agent | goods (value) |
|---|---|
| 0 | y₀ (10), y₁ (3), a₀ (6), b₀ (5) |
| 1 | y₁ (10), y₂ (3), a₁ (6), b₁ (5) |
| 2 | y₂ (10), y₀ (3), a₂ (6), b₂ (5) |
| 3 | y₀ (4), y₁ (3), y₂ (2) |
| 4 | y₀ (2), y₁ (4), y₂ (3) |

**Core conditions** (K4.CORE, LEDGER.md):
- *Degrees:* 4, 4, 4, 3, 3.
- *Strictly balanced:* 10 < 3 + 6 + 5 = 14 for the 4-good agents, and 4 < 3 + 2 for the 3-good ones.
- *Private goods:* agents 0–2 have the two private goods aᵢ, bᵢ, with 6 + 5 = 11 < 10 + 3 = 13 (the shared goods).
  Agents 3 and 4 have none.
- *Relevance and connectivity:* every good is relevant to someone, and the core is connected.
- *Strict:* no two disjoint sets of an agent's goods have equal value. For (10, 3, 6, 5): the singles are distinct;
  10 vs the pairs 9, 8, 11; 3 vs 11; 6 vs 8; 5 vs 9; the triples 14, 18, 19, 21 vs a single; the pairs 13 vs 11,
  16 vs 8, 15 vs 9. For (4, 3, 2) the only comparison is 4 vs 5.

## The order and why it fails

Order (0, 1, 2, 3, 4), or the R1-priority order (0, 2, 1, 3, 4). Picks (y₀, y₁, y₂, none, none), junk
{a₀, b₀, a₁, b₁, a₂, b₂}.

**Frozen agents.** Agents 3 and 4 hold nothing and want y₀, y₁ and y₂. So agents 0, 1 and 2 are frozen, and by Lemma
2(a) of `k4/sdc.md` §2 their picks stay alone: they receive no junk.

**Danger pairs.** Each {aᵢ, bᵢ} is worth 11 > 10 to agent i. So no bundle of three or more goods may contain a whole
pair (Lemma 2(b)).

**The count** (a written proof that the picks have no one-absorber completion).
- All six junk goods must go to agents 3 and 4.
- If the absorber's bundle has three or more goods, it contains at most one good of each pair, so at most three
  goods. Its only other option is to hold exactly one pair and nothing else, which is not a strict superset of the
  danger set and places two goods.
- The other agent may take one good.
- That places at most four goods, not six. ∎

**Free completion.** The picks have free completions. Agents 3 and 4 each take one good of every pair, as in
({y₀}, {y₁}, {y₂}, {a₀, a₁, a₂}, {b₀, b₁, b₂}).

**No move helps.** `python3 k4/ttc/refute_oc1.py results/k4_ttc/oc1_core_candidate.json 0` (log
`results/k4_ttc/refute_oc1_core.log`) finds 62 improving moves: 9 additions, 48 chains and 5 rings. After none of them
do the bases have a one-absorber completion; after 6 of them they have a free completion. For example, take the chain
in which agent 0 takes {a₀, b₀} and agent 3 takes y₀:
- agent 3 is then frozen itself, because agent 4 wants y₀;
- the two pairs {a₁, b₁} and {a₂, b₂} remain;
- besides the absorber, only agent 0, now holding its pair, can take a junk good: three places for four goods.

**The other orders** (same log, by SAT). The core has 11 distinct serial-dictatorship outcomes: 4 have a
one-absorber completion at the picks, 6 need one move, and only (y₀, y₁, y₂, none, none) fails. So "some order
works" statements (SD-C) are not affected; OC₁'s "every order" is.

## How it was found

The first counterexamples were 84 instances at n = 6, m = 10 (`results/k4_ttc/oc1_counterexamples.json`). They were
found by `k4/ttc/head_bign_climb.py 6 300 10 41 6 6 ends seeded`, a climb started from the OC₁-H counterexample of
`attempts/k4-ttc-head-owner.md`. They were rechecked by SAT (`oc1_false_check.py`, `oc1_false_check.log`) and
replayed on 7 instances by `refute_oc1.py` (`refute_oc1.log`).

None of the 84 is a core (`is_core4`): they have top-heavy agents, ties, or two private goods with p + q ≥ s + t. A
strict, balanced k = 3 family with n = 5, m = 9 (`oc1_counterexample_n5.json`) fails OC₁ in the same way, but there R2
peels agents 0–2, whose two private goods are worth at least their pick.

The core above was then built by hand from the counting argument:
- keep each frozen agent's danger pair private;
- make it worth less than the agent's two shared goods (C4), by giving each frozen agent a second shared good, the
  next agent's pick, worth 3;
- make the pickless agents balanced.

## What this says

- **One absorber is the wrong completion shape at k = 4.** The Draft-and-Exchange / LB⁺ finisher shape has a junk
  capacity of one absorber plus one good per other unfrozen agent. Three frozen agents with disjoint private danger
  pairs need more as soon as only two agents are unfrozen.
- **Refuted with it** (all one-absorber statements):
  - OC₁-H, OC₁-E and OC₁-ED (`k4/ttc.md` §8, §10);
  - the Hall session's OC₁-ED\* and Finding S\* (`k4/oc1_hall.md`);
  - "the count holds at the picks or after one chain" for a single owner.
- **What survives** on this core: OC (free completion) with zero chains, MD and SD-C. The candidate OC₁ᵖ, which counts
  absorbers only among agents holding a pick, also holds here with zero chains (both absorbers are pickless). But
  pickless absorbers are not essential to the pigeonhole: with four frozen agents and three unfrozen ones, holding
  picks nobody wants, the same count would need two absorbers among agents holding picks. That variant is untested.
- **Why the data missed it.**
  - The n = 5 core lists used by the OC₁ runs have at most two 4-good agents, and this core has three.
  - Random profiles of the lists with three, four and five 4-good agents also pass: 200 profiles each, 72,000 starts
    (`results/k4_ttc/oc1_n5_many4.log`).
  - On this hypergraph, 5 of 259 random strict core profiles fail OC₁ (1.9%), and OC holds on all of them
    (`oc1_core_profiles.py`, `results/k4_ttc/oc1_core_profiles.log`).
  - Random instances at n = 6–10 rarely have two pickless agents together with three disjoint private danger pairs.
