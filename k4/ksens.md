# k-sensitivity: where SD-C, MD, OC and OC₁ break as k grows

Angle `proof/k4-ksens` of the TARGET₄ campaign (`k4/attack_log.md`), branch `claude/k4-ksens`, PR #98. Code
`k4/ksens/`, logs `results/k4_ksens/`. Definitions as in `k4/sdc.md` §2 (SD-C), §28 (MD), §29 (OC, OC₁): a *start* is
the serial-dictatorship picks of an order, the *junk* is what nobody picked, an *improving chain* is §29's move (every
agent on it strictly gains), and a *completion* keeps every base. Random and climbed instances are evidence only
(PROMPT.md §5 rule 3).

## Status (burst 1)

- **OC and OC₁ are false at k = 5** (§1). PW5 has n = 5, m = 9, three agents with five relevant goods and two with
  four. From one order, neither the picks nor any of the 537 states one improving chain reaches has a completion,
  free or with one absorber. Checked by two independent programs and by a written proof.
  - The same family at k = 4 (pool of three goods) satisfies OC₁, and the proof shows why. After one repair a frozen
    agent's pool has k − 3 goods left, which is 1 at k = 4 and fits the one free slot the order always leaves; at
    k = 5 two are left (§2).
  - MD and SD-C hold on PW5. PW5 needs exactly two chains.
  - **The failing order is not R1-priority.** OC₁ restricted to R1-priority orders (LB's Phase 1) holds on every PW
    instance at k = 5, 6. It fails at k = 7 (PW(4, 3, 6), checked by both SAT encodings and by a SAT-free
    enumeration of the 29,683 one-chain states, `refute_oc1_r1_k7.log`). A k = 4 proof that uses only R1 orders, or
    one well-chosen order, is not refuted by PW below k = 7 (§4).
- **A ladder** (§4). The least number of improving chains the PW family needs is exactly ⌊(k − 1)/2⌋, computed by
  a second SAT encoding (`ocseq.py`) for k = 5–9:

  | k | 5 | 6 | 7 | 8 | 9 |
  |---|---|---|---|---|---|
  | chains | 2 | 2 | 3 | 3 | 4 |

  The same formula matches the known bottom rungs:
  - k ≤ 2: 0 chains (serial dictatorship);
  - k = 3: 1 (LB⁺'s single rotation; at most one chain on all k = 3 data);
  - k = 4: 1 (OC).

  This suggests the **ladder conjecture L**: from every order, ⌊(k − 1)/2⌋ improving chains suffice. At k = 4 it is
  OC; for all k it would contain EFX₀ existence. OC₁ at k = 4 is the rung c = 1, k ≤ 2c + 2.

  One *round* of vertex-disjoint chains, followed by a one-absorber completion, repairs every PW and POOL instance
  tested, k = 5–10. That variant survives this obstruction at every k.
- **The k ≤ 4 steps of the proved lemmas are sharp** (§3).
  - Theorem DT's conclusion fails at k = 5 (n = 2, m = 6, distinct tops: no one-absorber completion).
  - Theorem DT₁'s conclusion fails at k = 5 (n = 3, m = 8: hypothesis (G3) of Lemma GDT fails after the swap).
  - Both are checked by SAT and brute force; OC₁ still holds on both instances. At k = 4, DT₁ held on all 1,022 swaps
    tested.
- **k = 4 itself** (§5): no counterexample to OC₁.
  - A structured search over the PW design space at k = 4 (`pw4_search.py`): 60,000 instances with n ≤ 8, 178,308
    starts, 28,175 of them needing a chain, no failure.
  - Climbs at n = 5, 6 bottom out at exactly one repairing state, as the k = 4 climbs of `k4/sdc.md` did.
  - Two copies of the k = 4 instance that refutes the strict dichotomy (n = 6) satisfy OC₁: one copy's absorber takes
    the other's danger-free junk (`attempts/k4-ksens-union.md`).
- **Tools.**
  - `k4/ksens/ocsat.py` decides SD-C, MD, OC and OC₁ for one start with one SAT call each, at any k. The chain (or a
    round of disjoint chains) is encoded in SAT, with no bound on set sizes. `k4/ksens/kchains.py` gives the least
    number of chains by breadth-first search.
  - `k4/ksens/brute.py` is an independent brute force from the definitions (numpy, no SAT).
  - ocsat agrees with k4/sdc's enumerative chains on 1,758 starts (exact repairing-state counts included).
  - ocsat agrees with brute.py on 296 starts, PW5, its k = 4 version and the §3 instances included
    (`xcheck_brute_*.log`, `refute_oc_k5.log`, `refute_dt_k5.log`; 0 mismatches).
- **Random junk-rich surveys** (`survey_*.log`): no failure of any of the four conjectures.
  - n = 4, k = 5, 6, 8: 4,800 instances;
  - n = 5, k = 5, 6: 7,200 instances, about 87,000 starts;
  - PW-shaped, n = 5, k = 4: 600 instances.

  Random sampling misses PW-type structure, which needs every pair of a shared pool to be dangerous for every frozen
  agent.
- **Not found at any k: a failure of MD or SD-C.**
  - Both hold on every PW instance; in PW, MD holds provably (§4, the count closes when all repairs happen at once).
  - Climbs bottom out at exactly one dominating allocation or extendable outcome, never zero:
    - MD: n = 3 with up to 8 relevant goods per agent (30 rounds), n = 4 at k = 6 (25 rounds);
    - SD-C: n = 3, up to 8 goods (30 rounds), n = 4 at k = 6 from PW starts (25 rounds).
  - MD at every k contains EFX₀ existence for all additive instances (take the empty matching). So a proof of MD at
    k = 4 must use k ≤ 4 somewhere or solve that problem, and no k-sensitive mechanism for MD has been found.

## 1. OC and OC₁ fail at k = 5: the instance PW5

**Instance** (`k4/ksens/refute_oc_k5.py`; values in brackets):
| agent | goods (value) |
|---|---|
| x₁ = 0 | p₁ = 0 (10); D = 5 (9), 6 (8), 7 (7), 8 (6) |
| x₂ = 1 | p₂ = 1 (10); D as x₁ |
| x₃ = 2 | p₃ = 2 (10); D as x₁ |
| w₁ = 3 | p₁ (6), p₂ (4), p₃ (2), q₁ = 3 (1) |
| w₂ = 4 | p₁ (6), p₂ (4), p₃ (2), q₂ = 4 (1) |

Order π = (x₁, x₂, x₃, w₁, w₂). The picks are p₁, p₂, p₃, q₁, q₂; the junk is D. Every x_j is frozen: both wanters
want every p_j. Every pair of D is worth at least 6 + 7 = 13 > 10 to every x_j, and every single good of D less than 10.

**Claim.** Neither the picks nor any state reached from them by one improving chain has a complete EFX₀ completion
(free: the junk may go anywhere). So OC fails from π, and OC₁ with it.

**Proof.** Let X be a complete EFX₀ allocation containing the bases of a state reached by at most one chain.
1. *Who can gain.* An x gains only if its new base holds at least two goods of D. The only other goods it values is
   its own p, and a single good of D is worth less than 10. A wanter gains only by receiving some p_j, since it values
   nothing else above its q. All five agents have nonempty bases, so a chain agent other than x₀ receives a nonempty
   base.
2. *A frozen x holds its pick alone.* If an off-chain wanter w holds no p, then v_w(X_w) = 1 < v_w(p_j) for every j.
   So every x_j that still holds p_j has X_{x_j} = {p_j}: any further good g could be removed, leaving p_j for w.
   - Then x_j's value is 10, and no bundle of three or more goods may contain two goods of D. Remove a good outside
     the pair (or a third good of D); what remains is worth at least 13 to x_j.
3. *Let S be the set of x's on the chain.* By step 1 each takes two goods of D, so |S| ≤ 2.
   - *|S| = 0.* No wanter can gain, so there is no chain. Both wanters want every p, so by step 2 the x's hold their
     picks alone. The four goods of D go to the wanters' bundles, which then have at least three goods with two of D.
     ✗
   - *|S| = 2.* Each member holds exactly two goods of D, so the third x holds no good of D and has value 10.
     - The member that is not x₀ holds a nonempty received base plus its pair: at least three goods with two of D.
       Removing a received good leaves the pair, worth at least 13 > 10 to the third x. ✗
   - *|S| = 1, S = {x_a}.* Only p_a can make a wanter gain, so exactly one wanter w is on the chain and the other, w′,
     is off it and holds no p. By step 2, x_b and x_c hold their picks alone.
     - If x_a ≠ x₀, x_a holds a received base plus two goods of D. ✗ (step 2)
     - If x_a = x₀ with t = 0, x_a keeps p_a and adds D goods, so w′ is threatened through p_a. ✗
     - Otherwise x_a's bundle is exactly two goods of D, by step 2. w holds p_a, which w′ wants, so X_w = {p_a}.
       The other two goods of D can then only go to w′, whose bundle has three or more goods with two of D. ✗ ∎

**Checks** (`results/k4_ksens/refute_oc_k5.log`):
- ocsat.py (SAT; EFX₀ clauses from sdclib) and brute.py (every one of the 5⁹ allocations against the raw definition;
  chains enumerated by depth-first search from the definition) agree on all 19 distinct starts of the 120 orders.
- π is the only order that fails: 7 starts need a chain, and 6 of them are repaired by one.
- 537 distinct states are reachable by one chain from π; none has a completion.
- MD holds on every start; SD-C holds (some order's picks extend).
- *The k = 4 version* (D = three goods worth 9, 8, 7; `PW4` in the log) satisfies MD, SD-C, OC and OC₁ from every
  order.

**Robustness.** The random family PW(f, W, r) (`k4/ksens/fam_pw.py`) has f frozen agents sharing a pool of r goods
and W wanters that each want every frozen pick.
- PW(3, 2, 4) and PW(4, 2, 4) fail in 60 of 60 random draws each, at k = 5.
- PW(3, 3, 5) and PW(4, 3, 5) fail in 20 of 20, at k = 6.
- POOL(4, 7) (`fam_pool.py`: dedicated wanters) fails at k = 8, n = 8.
- Every PW with r = 3 holds: 7 shapes × 60 draws (`fam_pw.log`). That is k = 4 when f ≤ 3; for f ≥ 4 the
  wanters value f + 1 goods.
- PW(2, 2, 4), PW(3, 1, 4) and PW(4, 1, 4) hold at k = 5. Two frozen agents can both be repaired, and a single wanter
  stops wanting once it takes its favourite pick.

## 2. What k ≤ 4 buys here

The proof uses four facts.
1. A frozen agent that values a pool D of junk in which every pair is dangerous must hold its pick alone, and then
   no bundle of three or more goods may hold two goods of D.
2. Repairing such an agent costs two goods of D; only the head x₀ of a chain can be repaired that way, because a
   later agent also holds the base it received.
3. Wanters that are not on the chain keep the other agents frozen.
4. Each agent with an unwanted pick gives one slot for a single good of D.

After the one repair, |D| − 2 goods of D need slots. Here the only slot is w′, so |D| − 2 ≤ 1 is needed. A frozen
agent with k relevant goods has a pool of at most k − 1, so the leftover is at most k − 3: **0 or 1 at k = 4, 2 at
k = 5.** That is the property a k = 4 proof of OC₁ can use, and a proof valid for all k cannot exist.

> **(K4-leftover)** At k = 4, after a dangerous frozen agent x takes a danger pair H₀ ⊆ J (two of its three
> lower goods), at most one good of x's pool is left, and a single good is never a danger set (Lemma 2(c) of
> `k4/sdc.md`). So the repaired agent's pool needs no further protection.

At k = 5 the leftover pair is still a danger set for the other frozen agents that share the pool. That forces a second
repair, which one chain cannot give: a second repaired agent is not the head x₀, so it holds a received base next to
its pair.

## 3. Theorem DT fails at k = 5

Instance (`results/k4_ksens/dt_k5.log`, both checkers): agent 0 values goods 0 (100), 2, 3, 4, 5 (91, 92, 93, 94);
agent 1 values goods 1 (100), 2, 3, 4, 5 (94, 93, 92, 91). The tops are distinct.
- Every one-absorber completion of the picks fails. The agent with at most one junk good has value at most 194,
  while the other bundle, minus its top, holds three junk goods worth at least 276 to it.
- The free completion {0, 2, 3}, {1, 4, 5} works, and OC₁ holds via a chain with t = 0 (agent 0 adds two junk goods
  to its base).
- With four goods per agent (three junk goods) the same instance has a one-absorber completion. Theorem DT uses
  k ≤ 4 only in (F4): {a, g} is robust for every g except the exception d. At k = 5, {a, b} is not robust once
  c + d + e > a + b.

So at k = 5 even distinct tops need a chain under one absorber. The same instance refutes Theorem DT⁺ and Lemma GDT
at k = 5: with no pair holders and no frozen agent, GDT's conclusion is DT's. GDT's proof runs DT's moves, so it uses
(F4) as well.

**Theorem DT₁ at k = 5** (`k4/ksens/dt1_k5.py`, `dt1_k5.log`; replay `refute_dt_k5.py`, `refute_dt_k5.log`).
DT₁'s proof uses k ≤ 4 in step 3: R_x ∖ H₀ is a_x (now w's base) and at most one other good, which gives GDT's
(G3). At k = 5 there can be two other goods, both in the junk, worth more together than H₀.
- *Instance DT1-5:* agent 0 values goods 1, 2, 3, 6, 7 at 33, 19, 27, 18, 28; agent 1 values 0, 1, 2, 4, 7 at 22, 32,
  14, 26, 28; agent 2 values 2, 3, 4, 5, 7 at 6, 5, 9, 14, 10.
- *Setting.* Order (0, 1, 2) gives picks 1, 7, 5. The only want is agent 1 for good 1, so x = 0 is the only frozen
  agent and w = 1 its only wanter. x values H₀ = {3, 6} at 45 > 33.
- *After the swap* the bases are {3, 6}, {1}, {5} and the junk is {0, 2, 4, 7}. x's other goods 2 and 7 are worth
  47 > 45.
- GDT's completion with owner 2 does not exist (SAT; brute force: 0 allocations). 17 EFX₀ completions of the swapped
  state exist, all of which give x a junk good. So OC₁ survives; DT₁'s shape does not.
- *Frequency* (random n = 3, 4, five goods per agent): the conclusion fails for every owner in 73 of 2,580 swaps.
  With four goods per agent it held on all 1,022 swaps, as the proof says.

## 4. How many chains: a ladder in k

The question: the least number of improving chains, applied one after another (each from the current bases), after
which a start extends. Two methods:
- `k4/ksens/kchains.py`: breadth-first search. The states of each level are listed by SAT; the last level is
  tested with one SAT call per state. On PW5 it lists the same 537 one-chain states as the brute force.
- `k4/ksens/ocseq.py`, which encodes c chains applied one after another in one SAT call. The intermediate bases are
  variables; the encoding is written separately from ocsat's. It agrees with ocsat at c ≤ 1 on 2,266 start ×
  completion pairs and with the breadth-first search at c = 2 on 30 starts (`xcheck_ocseq.log`, 0 mismatches).

| instance (`fam_ladder.py`, clean values) | k | n | m | least chains (free / one absorber) |
|---|---|---|---|---|
| PW(3, 2, 4) = PW5 | 5 | 5 | 9 | 2 / 2 |
| PW(4, 2, 4) | 5 | 6 | 10 | 2 / 2 |
| PW(3, 3, 5) | 6 | 6 | 11 | 2 / 2 |
| PW(4, 3, 5) | 6 | 7 | 12 | 2 / 2 |
| PW(4, 3, 6) | 7 | 7 | 13 | 3 / 3 |
| PW(5, 3, 6) | 7 | 8 | 14 | 3 / 3 |
| PW(5, 4, 7) | 8 | 9 | 16 | 3 / 3 |
| PW(5, 4, 8) | 9 | 9 | 17 | 4 / (running) |

(`results/k4_ksens/ladder.log`; the breadth-first search confirms PW(3, 2, 4), PW(4, 2, 4), PW(3, 3, 5) and
PW(4, 3, 5), `ladder_pw436.log` shows PW(4, 3, 6) needs more than one.)

*The count behind it.* In PW(f, W, r) every frozen agent values the whole pool (r = k − 1 goods), and the W
wanters each want every frozen pick.
- While some frozen agent stays unrepaired, each chain can repair only its head x₀. Each repair costs two pool goods
  and uses up one wanter, which then holds a pick the other wanters want.
- After c chains, r − 2c pool goods are left, and only the W − c unused wanters can take one each.
- So c chains fail when r − 2c > W − c ≥ 1, i.e. when k − 1 − 2c ≥ 2: **k ≥ 2c + 3.** With c = 1 that is k ≥ 5.
- The bound is attained by PW(c + 2, c + 1, 2c + 2).

This matches what is known at the bottom of the ladder.
- c = 0 (the picks of every order extend) holds for k ≤ 2 (serial dictatorship, K3.SD2) and fails at k = 3, where
  LB⁺ needs its rotation.
- c = 1 is OC, which holds on all k = 4 data and fails at k = 5 (§1).

So in PW the least number of chains is ⌊(k − 1)/2⌋. This is proved for k = 5 (§1, c = 1) and computed for k = 5–9
(table). The general count is a heuristic: later chains can move pool pairs between frozen agents, and a full proof
for every c has not been written.

**Conjecture L (ladder).** For every k, from every serial-dictatorship order, the picks extend after ⌊(k − 1)/2⌋
improving chains.
- k ≤ 2: proved (serial dictatorship, K3.SD2).
- k = 3: evidence only (`k4/sdc.md` §29, at k = 3 no start needs more than one chain).
- k = 4: OC, evidence only.
- Tight (some start needs that many) for k = 3, 4 by the data and for k = 5–9 by PW.
- Its upper side at k = 5, 6 ("two chains suffice") is under test: `climb.py oc2`, from PW starts.

A proof of OC₁ at k = 4 is the c = 1 rung. It must use **pool leftover ≤ 1**: after a repair consumes a danger pair,
the frozen agent's pool has at most k − 3 = 1 good left, and that good fits one slot.

**Which orders.** OC and OC₁ quantify over every order; TARGET needs one.
- *Every order fails at k = 5.* In PW5 the failing order serves the three frozen agents before the wanters. It is
  not R1-priority: after x₁ takes p₁, the wanters have lost a good, and R1 serves them next.
- *R1 orders* (`k4/ksens/r1_pw.py`, `r1_pw.log`). OC₁ holds on every R1-priority start of PW(3, 2, 4), PW(4, 2, 4)
  and PW(3, 3, 5), clean and random values (k = 5, 6).
- *It fails at k = 7.* On PW(4, 3, 6), 6 of the 198 R1-priority starts fail. Example: service order (x₁, w₁, x₂, x₃,
  x₄, w₂, w₃).
  - w₁ takes p₂, and x₂ (having lost p₂) takes a pool good.
  - That leaves three frozen agents (x₁, x₃, x₄; w₁ is frozen too) sharing the five other pool goods, with two slots
    (w₃, and x₂'s two-good bundle).
  - R1 costs PW two pool goods.
  - Checks (`refute_oc1_r1_k7.py`, `refute_oc1_r1_k7.log`): ocsat and ocseq say no one-chain repair and a two-chain
    one; brute.py independently enumerates the 29,683 one-chain states and finds no completion of any of them.
    The completions are decided by backtracking from the raw definition, validated against the full enumeration on
    PW5.
- *Some order* (SD-C, zero chains): holds on every PW instance.
- So for a k = 4 proof:
  - "from every order, one chain" is a k ≤ 4 statement with a k = 5 counterexample;
  - "from every R1 order" has its first known counterexample at k = 7;
  - "from some order" (SD-C) has none.
- Climbs against OC₁ on R1 orders at k = 5, 6 (`climb.py oc1r1`, from PW starts) are running.

**One round of disjoint chains** (`ocsat.OC.holds(..., multi=True)`: any number of vertex-disjoint chains at once,
each x₀ taking only from its own chain's end; `k4/ksens/round_pw.py`, `round_pw.log`). Every PW and POOL instance
tested is repaired by one round followed by a one-absorber completion:
- 90 PW instances with k = 5–9;
- POOL(4, 7) and POOL(5, 9) (k = 8, 10).

In PW the repairs are independent: each takes a fresh frozen agent and a fresh wanter. So "one round of disjoint
chains, then one absorber" is not refuted by this mechanism at any k. A climb against it (`climb.py round1`, n = 4, 5,
k = 5, 6) has not found a failure (`climb_round1_*.log`).

## 5. k = 4

- *PW-shaped instances at k = 4* (`gen.py pw`: frozen agents sharing a pool of three or four, wanters of random
  subsets of their picks, extra agents): no failure of OC₁ (`survey_pw_n5k4.log`, 600 instances at n = 5).
- *Climbs against OC₁* from those starts, n = 5 (40 rounds) and n = 6 (30 rounds, all 720 orders per evaluation)
  (`climb_oc1_n5k4_pw.log`, `climb_oc1_n6k4_pw.log`). They bottom out at exactly one repairing state, as the k = 4
  climbs of `k4/sdc.md` §29 did.
- *Disjoint unions* (`attempts/k4-ksens-union.md`). Two copies of the dichotomy counterexample K4.SDC.DICH need two
  absorbers if each copy keeps its own junk. They do not: one copy's absorber takes the other copy's junk that holds
  no danger set, and OC₁ holds (n = 6).
- *Complete want* (`attempts/k4-ksens-complete-want.md`, `fam_cw.py`). Every frozen pick stays wanted after a chain,
  yet the chain can dump the last frozen pick on a wanter as that wanter's one junk good, which satisfies it. OC₁
  holds on all 240 instances, k = 5–8.
