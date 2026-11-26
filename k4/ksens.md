# k-sensitivity: where SD-C, MD, OC and OC₁ break as k grows

Angle `proof/k4-ksens` of the TARGET₄ campaign (`k4/attack_log.md`), branch `claude/k4-ksens`, PR #98. Code
`k4/ksens/`, logs `results/k4_ksens/`. Definitions as in `k4/sdc.md` §2 (SD-C), §28 (MD), §29 (OC, OC₁): a *start* is
the serial-dictatorship picks of an order, the *junk* is what nobody picked, an *improving chain* is §29's move (every
agent on it strictly gains), and a *completion* keeps every base. Random and climbed instances are evidence only
(PROMPT.md §5 rule 3).

## Status (burst 1)

**Bottom line.**
- The every-order conjectures OC and OC₁ are genuinely k-sensitive: true on all k = 4 data, false at k = 5. So a
  proof of them at k = 4 does not have to solve general EFX₀, but it must use k ≤ 4. The property it can use is
  identified in §2.
- SD-C and MD have no failure at any k tested. MD at all k contains EFX₀ existence, so for MD the k ≤ 4 ingredient is
  still unknown.

| statement | k = 4 | smallest k found to fail | instance | checks |
|---|---|---|---|---|
| OC₁ / OC: from every order, one improving chain, then a completion (one absorber / free) | holds on all data | **5** | PW5, n = 5, m = 9; smaller: n = 4, m = 8 found by `proof/kgen-n3` | SAT, full brute force, written proof (the n = 4 one re-checked here by both checkers) |
| the same from R1-priority orders, or from the neediest-first order (need = y₁ − y₂ − y₃) | holds | **6** | PWR1-6, NF2-6 (n = 6, m = 11) | 2 SAT encodings, SAT-free enumeration |
| c chains from every order | c = 1 holds | **2c + 3** (c = 1, 2, 3) | PW(c + 2, c + 1, 2c + 2) | c = 1 as above; c = 2, 3 by ocseq.py only |
| one round of disjoint chains, then one absorber (Conjecture RD₁, §6) | holds | none found (k ≤ 10) | repairs every counterexample above | |
| SD-C (some order, no chain) | holds | none found (k ≤ 8) | | |
| MD (every order's picks value-dominated) | holds | none found (k ≤ 8) | | |
| conclusion of Theorem DT (and DT⁺, Lemma GDT) | proved | **5** | DT5, n = 2, m = 6 | SAT, brute force |
| conclusion of Theorem DT₁ | proved | **5** | DT1-5, n = 3, m = 8 | SAT, brute force |

### Lemma PL (pool leftover): where k ≤ 4 enters

*Setting.*
- Y = SD(π) is the serial-dictatorship outcome of some order, and J is the set of goods nobody picked (the junk).
- x is an agent with pick y_x and |R_x| ≤ k.
- H ⊆ J ∩ R_x satisfies v_x(H) > v_x(y_x): a junk danger set of x, used by x as its improving set. That is H₀ when x
  heads a chain, or H_i when x is a middle agent.

**Lemma PL.**
- **(a)** |H| ≥ 2, and x values at most k − 3 goods of J ∖ H.
- **(b)** If |R_x| ≤ 4, x values at most one good of J ∖ H, and that good is worth at most v_x(y_x) < v_x(H). So once
  x's base contains H, no subset of J ∖ H is a danger set of x.
- **(c)** Let z be any agent with a pick y_z, |R_z| ≤ 4, that values at least two goods of H. Then z values at most
  one good of J ∖ H, worth at most v_z(y_z). So while z holds y_z, no subset of J ∖ H is a danger set of z.
  - In particular, when the frozen agents share their junk (J ∩ R_z = J ∩ R_x, the pool of PW), one repair of any one
    of them leaves no agent of the pool with a junk danger set.
- **(d)** For every k ≥ 5 the bound k − 3 ≥ 2 of (a) is attained, and it is fatal for OC₁. In PW5 (k = 5, §1), after
  any repair of x₁ by a pair of the pool D, the other frozen agents x₂ and x₃ still value the two remaining goods of D.
  Those are worth 13 or more against their pick 10, and one chain cannot repair a second agent (§1, case |S| = 2).

*Proof.*
1. *Junk is worth at most the pick (property (I2) of k4/sdc.md §2).* Every g ∈ J ∩ R_x was still available when x
   picked, and x took its favourite available good, so v_x(g) ≤ v_x(y_x). The inequality is strict for strict values;
   with ties broken by index it is ≤, which is all that is used below.
2. *(a).* A single good of J is therefore not worth more than y_x, so |H| ≥ 2. Since y_x ∉ J,
   |J ∩ R_x| ≤ |R_x| − 1 ≤ k − 1, hence |(J ∩ R_x) ∖ H| ≤ k − 1 − 2 = k − 3.
3. *(b).* With |R_x| ≤ 4 the bound of (a) is 1. By step 1 that one good is worth at most v_x(y_x) < v_x(H). A danger
   set against a holding that contains H must be worth more than v_x(H), so none exists inside J ∖ H.
4. *(c).* As in step 2, |J ∩ R_z| ≤ |R_z| − 1 ≤ 3. Two of these goods lie in H, so at most one lies in J ∖ H, and by
   step 1 (for z) it is worth at most v_z(y_z). A danger set of z against a holding containing y_z must be worth more
   than v_z(y_z); a set of at most one such good is not.
5. *(d).* This is the computation of §1. ∎

*What PL does not cover.* These are the parts a k = 4 proof still has to handle; the data say a suitable chain
exists (Lemma candidate K4-G4, §2).
- An agent z that shares only one good with H keeps up to two junk goods, which can be a danger set.
- PL speaks of the old junk J ∖ H only. The chain's end releases its old base into the junk, and PL says nothing
  about it.
- Danger sets that use another agent's pick, like {y_j, d} inside a three-good bundle of j. In the n = 4, k = 5
  counterexample of `proof/kgen-n3` (verified here, `kgen_n4_check.log`) such a set appears: agent 3 values agent
  1's pick 2 at 53 and the junk good 3 at 4, and 53 + 4 > 54.

*The same count elsewhere.* Theorem DT's (F4) ({a, g} robust for a 4-good agent, except the d case) and Theorem
DT₁'s step 3 (R_x ∖ H₀ is a_x plus at most one good) are the one-agent forms of (a) with k = 4. §3 shows that both
fail at k = 5.

Details:

- **OC and OC₁ are false at k = 5** (§1). PW5 has n = 5, m = 9, three agents with five relevant goods and two with
  four. From one order, neither the picks nor any of the 537 states one improving chain reaches has a completion,
  free or with one absorber. Checked by two independent programs and by a written proof.
  - The same family at k = 4 (pool of three goods) satisfies OC₁, and the proof shows why. After one repair a frozen
    agent's pool has k − 3 goods left. At k = 4 that is one good, never a danger set; at k = 5 it is two (§2).
  - MD and SD-C hold on PW5. PW5 needs exactly two chains.
  - **The failing order is not R1-priority.** The other order classes fail later (§4, "Which orders"):
    - R1-priority orders (LB's Phase 1) and the neediest-first order of `k4/sdc.md` §9 first fail at k = 6;
    - some order (SD-C) never does.

    Each k = 6 case is checked by two SAT encodings and by a SAT-free enumeration of all one-chain states.
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
  - Lemma candidate (K4-G4) (§2): from every hard start, some repairing chain leaves no dangerous frozen agent. It
    holds on all 349 curated and 1,392 PW-design hard starts; PW5 breaks it at k = 5.
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
  - Both hold on every PW instance tested. Heuristically MD should hold throughout PW: all repairs can happen at
    once, and the §4 count then closes. No written proof.
  - Climbs bottom out at exactly one dominating allocation or extendable outcome, never zero:
    - MD: n = 3 with up to 8 relevant goods per agent (30 rounds), n = 4 at k = 6 (25 rounds), n = 5 at k = 5 from
      PW starts (20 rounds);
    - SD-C: n = 3, up to 8 goods (30 rounds), n = 4 at k = 6 (25 rounds) and n = 5 at k = 5 (20 rounds) from PW
      starts.
  - **Caveat: the climbs are weak.** The OC₁-R1 climb at n = 6, k = 6, started from PW instances, also bottoms out at
    1 (15 rounds), although PWR1-6 (n = 6, k = 6) refutes OC₁-R1. Every counterexample here came from a hand-designed
    family (PW), none from a climb. So "no failure found" for SD-C, MD and the round variant is weak evidence.
  - MD at every k contains EFX₀ existence for all additive instances (take the empty matching). So a proof of MD at
    k = 4 must use k ≤ 4 somewhere or solve that problem, and no k-sensitive mechanism for MD has been found.

## 1. OC and OC₁ fail at k = 5: the instance PW5

*A smaller counterexample* was found independently by the general-k session (`attempts/kgen-n4-oc1.md` on branch
`claude/kgen-n3`, read here).
- It has n = 4, m = 8, k = 5, strict values; its failing order is (0, 3, 1, 2).
- Re-checked here (`kgen_n4_check.log`): ocsat and brute.py agree on all 6 starts, there are 127 EFX₀ allocations,
  and two chains repair it.
- Every fifth good is needed: dropping any one good of either five-good agent restores OC₁ and OC from every order.
- Its mechanism is not PW's shared pool. Agent 3's three junk goods are pairwise dangerous only because of a good it
  values at 4, which also forms a danger set with agent 1's pick (Lemma PL, "what PL does not cover").

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
1. *Who can gain.*
   - An x values only its own p and D, and no other agent's base contains its p.
   - So on a chain with t ≥ 1 an x gains only if its new base holds at least two goods of D: a single good of D is
     worth less than 10. On a chain with t = 0 (x alone), it keeps p_x and adds goods of D.
   - A wanter gains only by receiving some p_j, since it values nothing else above its q, and no junk at all.
   - All five agents have nonempty bases, so a chain agent other than x₀ receives a nonempty base.
2. *A frozen x holds its pick alone.* If an off-chain wanter w holds no p, then v_w(X_w) = 1 < v_w(p_j) for every j.
   So every x_j that still holds p_j has X_{x_j} = {p_j}: any further good g could be removed, leaving p_j for w.
   - Then x_j's value is 10, and no bundle of three or more goods may contain two goods of D. Remove a good outside
     the pair (or a third good of D); what remains is worth at least 13 to x_j.
3. *Let S be the set of x's on the chain.* A chain with t = 0 has one agent. On a longer chain each x takes two
   goods of D (step 1). So |S| ≤ 2.
   - *|S| = 0.* No wanter can gain, so there is no chain. Both wanters want every p, so by step 2 the x's hold their
     picks alone. The four goods of D go to the wanters' bundles, which then have at least three goods with two of D.
     ✗
   - *|S| = 2.* Each member holds exactly two goods of D, so the third x holds no good of D and has value 10.
     - The member that is not x₀ holds a nonempty received base plus its pair: at least three goods with two of D.
       Removing a received good leaves the pair, worth at least 13 > 10 to the third x. ✗
   - *|S| = 1, S = {x_a}.* The other x's are off the chain, so p_a is the only p that can move.
     - *t = 0* (x_a alone). x_a keeps p_a and adds goods of D. Both wanters are off the chain and hold no p, so they
       want p_a and are threatened by X_{x_a} minus a good of D. ✗
     - *t ≥ 1.* Exactly one wanter w receives p_a: it is x_a's successor, or x₀ taking p_a from x_t = x_a. The other
       wanter w′ cannot gain, so it is off the chain and holds no p, and by step 2 x_b and x_c hold their picks alone.
       - If x_a ≠ x₀, x_a holds a received base plus two goods of D. ✗ (step 2)
       - If x_a = x₀, its bundle is exactly two goods of D, by step 2. w holds p_a, which w′ wants, so X_w = {p_a}.
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

After the one repair, |D| − 2 goods of D need slots. In PW5 the only slot is w′, so |D| − 2 ≤ 1 is needed. A frozen
agent with k relevant goods has a pool of at most k − 1, so the leftover is at most k − 3: **0 or 1 at k = 4, 2 at
k = 5.** That is the property a k = 4 proof of OC₁ can use. OC₁ is false for every k ≥ 5 (PW5 is k-limited for
every k ≥ 5), so any proof of it must use k ≤ 4 somewhere.

This count is **Lemma PL** (statement and proof at the top of this note). By (b) and (c), at k = 4 the repaired agent,
and every agent that shares two goods of its repair set, has no junk danger set left.

**Lemma candidate (K4-G4)** (`k4/ksens/g4_after.py`). Call a frozen agent (one whose base someone wants) *dangerous*
when it values the junk above its base.

> At k = 4, from every start whose picks have no one-absorber completion, some state reached by one improving chain
> has a one-absorber completion and leaves no dangerous frozen agent.

- *Evidence:* it holds on every hard start tested.
  - All 349 hard starts of the curated k = 4 set (`seeds_k4_hard.txt`: the DE4 screen set with the GM4 family, T3,
    Q2 and the logged climb results; `g4_after.log`).
  - All 1,392 hard starts of 1,730 PW-design k = 4 instances with n ≤ 6 (`seeds_pw4.txt`, `g4_after_pw4_n6.log`;
    the n ≤ 5 part alone, 1,175 starts, in `g4_after_pw4.log`).
- *At k = 5* PW5 has no repairing chain at all.
- *Why it helps.* (K4-G4) is the hypothesis (G4) of Lemma GDT, without the owner's good, after the chain. A proof of
  OC₁ through GDT needs it, and the leftover count above is its mechanism in the shared-pool case.

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
| PW(5, 4, 8) | 9 | 9 | 17 | 4 / 4 |
| PW(6, 4, 8) | 9 | 10 | 18 | 4 / 4 |

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
- Its upper side at k = 5, 6 ("two chains suffice"): climbs from PW starts (`climb.py oc2`, n = 5 at k = 5 and n = 6
  at k = 6, 50 rounds) found no start needing three chains.

A proof of OC₁ at k = 4 is the c = 1 rung. It must use **pool leftover ≤ 1**: after a repair consumes a danger pair,
the frozen agent's pool has at most k − 3 = 1 good left, and a single good is never a danger set.

**Which orders.** OC and OC₁ quantify over every order; TARGET needs only one good order. Where the failure first
appears depends on which orders are allowed:

| orders allowed | first failure of OC₁ (and OC) | instance | checks |
|---|---|---|---|
| every order | k = 5, n = 5, m = 9 | PW5 (§1) | SAT, full brute force, written proof |
| neediest first, need = y₁ − y₂ (plain) | k = 5 | PW5 with pool 24..21, pick 40 (`nf_orders.py`, `nf_orders.log`) | SAT |
| neediest first, need = y₁ − y₂ − y₃ (§9 of `k4/sdc.md`), plain | k = 6, n = 6, m = 11 | NF2-6 | SAT ×2, SAT-free |
| R1-priority (LB's Phase 1), some R1 order | k = 6, n = 6, m = 11 | PWR1-6 | SAT ×2, SAT-free |
| R1 neediest first, need = y₁ − y₂ | k = 6, n = 7, m = 12 | NF1R1-6 | SAT ×2, SAT-free |
| R1 neediest first, need = y₁ − y₂ − y₃ (LB₄ʳ's Phase 1); "needall" | none found | designs in `nf2r1.log` | |
| some order (SD-C: zero chains) | none found | | |

Notes on the table:
- *The checks* (`refute_oc1_r1.py`, `refute_oc1_r1.log`). "SAT ×2" means ocsat and ocseq: no one-chain repair, and
  a two-chain repair exists. "SAT-free" means brute.py enumerates every one-chain state (2,514 to 29,683 per case)
  and finds no completion of any, by backtracking against the raw definition. The backtracking was validated against
  the full enumeration on PW5 (38,286 comparisons).
- *Why R1 costs a pool good.* In PW5's failing order the three frozen agents are served before the wanters. R1
  serves a wanter as soon as it has lost a good. In the R1 runs:
  - the first wanter takes a second frozen pick (and is frozen itself);
  - the frozen agent that lost it takes a pool good;
  - the other frozen agents, having lost that pool good, are served before the remaining wanters.

  That costs one pool good, and the displaced agent's two-good bundle is a new slot.
  - PWR1-6 removes that slot: the wanters value the displaced pool good slightly above their own good, so its holder
    is frozen too.
  - The count of §4 then needs three wanters and a pool of five, so k = 6. With this design k = 5 cannot fail under
    R1, and every k = 5 R1 variant tested holds.
- *Neediest-first* is value-sensitive. With the default values the wanters are the needier agents, are served first,
  and the picks extend (`nf_orders.py`, `nf_orders.log`). Flattening the wanters' values (p's 200, 199, 198, q 190) or lowering the
  pool goods to just above half the pick puts the frozen agents first.
- *need2 with R1 resists the PW designs* (`nf_orders.py 4`, `nf2r1.log`).
  - Adding a first agent z whose pick is a pool good makes every frozen agent "lose a good", so R1 serves them early.
  - But once two of a wanter's picks are gone its need y₁ − y₂ − y₃ turns positive, and it is served before the last
    frozen agent.
  - Keeping wanters non-needy needs extra goods of theirs that would also satisfy them as junk.
  - So the order LB₄ʳ and K4.SDC.NF use is the one order class here with no counterexample at any k; a k = 4 proof
    along those lines is not refuted by this mechanism.
- Climbs against OC₁ on R1 orders at k = 5 (`climb.py oc1r1`, n = 5, 30 rounds from PW starts): no failure.

So for a k = 4 proof:
- "from every order, one chain" has a k = 5 counterexample;
- "from every R1 order" and "from the neediest-first order" have k = 6 counterexamples;
- "from some order" (SD-C) has none.

A proof that fixes the order cleverly is not refuted at any k by this mechanism; the k ≤ 4 property it would use is
still pool leftover ≤ 1 (§2).

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
- *The PW design space at k = 4* (`pw4_search.py`): f frozen agents, each with a 3-subset of a pool D, every pair of
  it dangerous; 1–3 wanters of random subsets of the picks; sometimes an extra random agent. Natural order plus random
  orders. No failure of OC₁:
  - `pw4_search.log`: f ≤ 4, |D| ≤ 5; 60,000 instances, 178,308 starts, 28,175 needing a chain;
  - `pw4_search_wide.log`: f ≤ 5, |D| ≤ 8 (so pools from disjoint to identical); 20,000 instances, 49,035 starts,
    10,426 needing a chain.

  Disjoint pools are harmless: a middle repair then threatens nobody, so one chain can repair every frozen agent.
  Identical pools are PW4, with leftover 1. Partial overlaps leave room to pick pairs that are not danger sets of the
  other agents.
- *Climbs against OC₁* from those starts, n = 5 (40 rounds) and n = 6 (30 rounds, all 720 orders per evaluation)
  (`climb_oc1_n5k4_pw.log`, `climb_oc1_n6k4_pw.log`). They bottom out at exactly one repairing state, as the k = 4
  climbs of `k4/sdc.md` §29 did.
- *Disjoint unions* (`attempts/k4-ksens-union.md`). Two copies of the dichotomy counterexample K4.SDC.DICH need two
  absorbers if each copy keeps its own junk. They do not: one copy's absorber takes the other copy's junk that holds
  no danger set, and OC₁ holds (n = 6).
- *Complete want* (`attempts/k4-ksens-complete-want.md`, `fam_cw.py`). Every frozen pick stays wanted after a chain,
  yet the chain can dump the last frozen pick on a wanter as that wanter's one junk good, which satisfies it. OC₁
  holds on all 240 instances, k = 5–8.

## 6. One round of disjoint chains: Conjecture RD

**Definitions** (encoded by `ocsat.OC.holds(..., multi=True)`).
- A *round* from bases B is a set of vertex-disjoint improving chains C₁, …, C_s (s ≥ 0), each a chain of
  `k4/sdc.md` §29 with t ≥ 0, applied at the same time.
- Their junk sets H are pairwise disjoint. Each chain's head takes only junk and goods of its own chain's end.
- Each chain's end releases what is left of its old base into the junk.
- Every agent on a chain gains strictly; every other agent keeps its base.

**Conjecture RD₁ (k4/ksens).** In every additive instance, for every serial-dictatorship order π, some round from
the picks SD(π) reaches bases with a one-absorber completion: a complete EFX₀ allocation containing every base, in
which at most one agent holds two or more goods outside its base. RD is the same with the free completion.

*What RD says.*
- RD₁ ⟹ RD.
- RD from an order π implies MD for π: every chain agent gains and every other agent keeps its pick, so the
  completion value-dominates the picks.
- RD from a single order already gives a complete EFX₀ allocation.
- So **RD for all k contains EFX₀ existence for every additive instance**, which is open for n ≥ 4. RD at a fixed k
  is a k-limited statement like OC₁, with s chains instead of one.

*Evidence* (all EVIDENCE):

| data | starts needing a chain | one chain fails | one round fails |
|---|---|---|---|
| every known OC₁ counterexample, all starts: kgen-n4 (n = 4, k = 5), PW5, PW436, PWR1-6, NF2-6, NF1R1-6 (`round_known.log`) | 5, 7, 85, … | 1, 1, 13, … | 0 |
| random PW draws, k = 5–9 (90) and POOL(4, 7), POOL(5, 9) (`round_pw.log`) | all | all | 0 |
| PWQ(f, W, r): released wanter goods valued by the frozen agents (`fam_pwq.py`, 160 instances, k = 5–7) | all | 0 | 0 |
| climbs against RD₁ (`climb.py round1`): n = 4, 5 at k = 5, 6 (79 rounds), n = 6 at k = 6 | | | none |

The climbs at k = 6, 8 seeded from the n = 4 instance and from PW (`climb_round1_n4k6_kgen.log`,
`climb_round1_n5k8_pwfam.log`, `climb_round_n5k6_pwseed.log`) are running. As noted in the status block, the climbs
are weak: they miss known counterexamples to OC₁-R1.

**Why rounds beat the PW obstruction.** In PW every repair is independent. It uses a fresh frozen agent x, a fresh
wanter w, and the chain x → w; x takes a pair of the pool, w takes x's pick, and w's old pick is released.
- One chain can repair only its head without threatening the rest (Lemma PL (d), §1). A round can perform s repairs
  at once for any s ≤ min(W, ⌊r/2⌋).
- After s repairs, r − 2s pool goods are left and the W − s unused wanters offer one slot each.
- Taking s as large as the wanters allow closes the §4 count: with s = W every wanter holds a pick it ranks above the
  unrepaired agents' picks, so those are unfrozen and absorb their own pool goods.
- This is the k-free part of the picture. A round turns a bounded number of repairs (the ladder's ⌊(k − 1)/2⌋ chains)
  into an unbounded one.

**What a round cannot do, and where a counterexample to RD would have to live.** Compare two chains C₁ then C₂ applied
one after another from the picks (single-good bases).
1. If they share no agent and C₂ takes nothing that C₁ released, they form a round with the same result.
2. If C₂'s head y takes the pick g that C₁'s end a released, and C₂ is not a ring (y takes nothing from C₂'s own end),
   the concatenation C₁·C₂ is one chain with the same result. a passes its whole base {g} to y, so y receives exactly
   g, and C₁'s head may still take its junk.
3. The gap.
   - C₂ is a ring whose head needs both g (released by C₁) and goods of C₂'s own end. Then neither concatenation keeps
     both. In C₁·C₂ the head y is a middle agent and cannot take from C₂'s end. In C₂·C₁ the head x₀ of C₁ is a middle
     agent and receives C₂'s end's base instead of y.
   - Or the two chains share an agent that must gain twice.

   So an RD counterexample needs a repair that is a ring around a good released by another repair, or an agent that
   must move twice.
   - In PW, PWQ and the n = 4 instance no such dependence occurs.
   - A designed gadget (a ring head valuing exactly {g, e}, with g released by another chain and e the ring end's pick)
     is the next thing to try.

None of this is a proof. A k-free reason for RD would prove EFX₀ existence. What this section does establish is the
mechanism by which every k-sensitive failure found here, and in `proof/kgen-n3`, is repaired: independent repairs done
in parallel.
