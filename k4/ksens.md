# k-sensitivity: where SD-C, MD, OC and OC₁ break as k grows

Angle `proof/k4-ksens` of the TARGET₄ campaign (`k4/attack_log.md`), branch `claude/k4-ksens`, PR #98. Code
`k4/ksens/`, logs `results/k4_ksens/`. Definitions as in `k4/sdc.md` §2 (SD-C), §28 (MD), §29 (OC, OC₁): a *start* is
the serial-dictatorship picks of an order, the *junk* is what nobody picked, an *improving chain* is §29's move (every
agent on it strictly gains), and a *completion* keeps every base. Random and climbed instances are evidence only
(PROMPT.md §5 rule 3).

## Status (bursts 1–3)

**Bottom line.** Burst 3 corrects bursts 1–2, which said OC₁ holds on all k = 4 data.
- **OC₁, OC and one round fail already at k = 4, from maximum-matching starts** (§5).
  - The certifier session's ordinal CEGAR (branch `compute/k4-oc1max-cert`) covered every strict profile of the
    1,002 n = 4 core hypergraphs. It found 11 strict cores, n = 4 and m = 7 or 8, whose failing start gives every
    agent a pick.
  - From that start, neither the picks nor any state one chain or one round reaches has a completion, free or with
    one absorber. Two chains repair each.
  - Both checkers here agree on all 11 (`refute_oc1max_k4.py`).
  - The failing start is also an R1-priority start. The neediest-first starts hold (`oc1max_k4_orders.py`).
  - My k = 4 searches (80,000 structured instances, and climbs) never reached this structure
    (`attempts/k4-ksens-k4-searches.md`).
- **The PW mechanism is still k-sensitive.** A shared junk pool needs k ≥ 5 to break one chain, and Lemma PL and
  Lemma PWk (a) stand, proved and refereed. The k = 4 failure is a different mechanism, and it uses exactly the two
  cases Lemma PL leaves open: the base the chain releases, and a danger set built on another agent's pick (§5).
- **At k = 3 one chain suffices** (§8), exhaustively over every strict profile of every connected hypergraph:
  - from every start, maximum-matching or not, for n ≤ 4, under both move rules;
  - from every maximum-matching start for n = 5: 178,767,520 profiles, 553,551,399 starts, 4,062,658 of them
    needing a chain, no failure.
- **The ladder is corrected** (§4, §8).
  - Conjecture L (⌊(k − 1)/2⌋ chains) is false at k = 4.
  - Every rung known fits ⌊k/2⌋ chains, i.e. c chains up to k = 2c + 1 (Conjecture L′, §4).
  - The open rung: does k = 6 need three chains?
- RD (one round) fails at k = 4 by the same 11 instances, so RD5 (k = 5) is no longer the first failure. Two rounds
  (RD²), SD-C and MD have no failure at any k tested, and the 11 instances satisfy SD-C and MD. MD at all k contains
  EFX₀ existence.
- **Maximum-matching starts do not help** (§7), at k = 4 as at k = 5. Lemma PWk (§7) gives the PW count at general k.
- **The every-order forms at k = 4 were refuted earlier**, from non-maximum starts, by the TTC session's B< and MC2
  (`k4/sdc.md` §31, read on `compute/k4-oc1max-cert`).
  - Those two fail only under the official move rule. When an agent with an empty base may pass it on, one chain
    repairs both (`refute_oc_every_k4.py`).
  - The 11 new instances are perfect starts, so for them the rule does not matter.

| statement | k = 4 | smallest k found to fail | instance | checks |
|---|---|---|---|---|
| OC₁ / OC: from every order, one improving chain, then a completion (one absorber / free); also from maximum-matching starts only (OC₁^max, OC^max) | **fails** | **4** | the certifier's 11 cores, n = 4, m = 7 or 8 (§5); at k = 5 by the PW mechanism: PW5 (n = 5, m = 9, written proof), RD5, the n = 4 instance of `proof/kgen-n3` | SAT, full brute force (here and by the certifier) |
| the same from R1-priority orders | **fails** | **4** | the same 11 (§5); PWR1-6 at k = 6 | SAT; the 11 starts also by brute force |
| the same from the neediest-first order (need = y₁ − y₂ − y₃) | holds (data; the 11 included) | **6** | NF2-6 (n = 6, m = 11) | 2 SAT encodings, SAT-free enumeration |
| c chains from every order | c = 1 fails; c = 2 holds (data) | c = 1: **4**; c = 2, 3: 2c + 3 found | the 11 (c = 1); PW(c + 2, c + 1, 2c + 2) | c = 1 as above; c = 2, 3 by ocseq.py only |
| one round of disjoint chains, then a completion (Conjecture RD / RD₁, §6) | **fails** | **4** | the 11 (§5); RD5 (n = 4, m = 7) at k = 5 | SAT, brute force over every round |
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

*What PL does not cover.* Lemma candidate K4-G4 (§2) claimed that at k = 4 a suitable chain always exists. It is
false (§5), and the counterexamples use the last two of these gaps.
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

- **OC and OC₁ fail at k = 5 by the shared-pool mechanism** (§1); they fail already at k = 4 by another one (§5).
  PW5 has n = 5, m = 9, three agents with five relevant goods and two with
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

  The bottom rungs:
  - k ≤ 2: 0 chains (serial dictatorship);
  - k = 3: 1 (LB⁺'s single rotation; exhaustive over strict profiles for small n, §8);
  - k = 4: **2, not 1**: the counterexamples of §5 need two.

  Burst 2 conjectured ⌊(k − 1)/2⌋ chains (Conjecture L), and k = 4 refutes it. Every rung known fits ⌊k/2⌋
  (Conjecture L′, §4). PW's ⌊(k − 1)/2⌋ is a lower bound at most ⌊k/2⌋, and the two agree at odd k. For all k, L′
  would contain EFX₀ existence.

  One *round* of vertex-disjoint chains, followed by a one-absorber completion, repairs every PW and POOL instance
  tested, k = 5–10. That variant survives this obstruction at every k.
- **The k ≤ 4 steps of the proved lemmas are sharp** (§3).
  - Theorem DT's conclusion fails at k = 5 (n = 2, m = 6, distinct tops: no one-absorber completion).
  - Theorem DT₁'s conclusion fails at k = 5 (n = 3, m = 8: hypothesis (G3) of Lemma GDT fails after the swap).
  - Both are checked by SAT and brute force; OC₁ still holds on both instances. At k = 4, DT₁ held on all 1,022 swaps
    tested.
- **k = 4 itself** (§5): OC₁ fails (the certifier's 11 cores). My own k = 4 searches, listed below, found no failure;
  they are kept as a record of what missed it.
  - Lemma candidate (K4-G4) (§2) is false: the 11 starts have no repairing chain at all. It held on all 349 curated
    and 1,392 PW-design hard starts.
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
k = 5.** That is why the shared-pool mechanism cannot break one chain at k = 4. It does not give OC₁ at k = 4, which
fails there by a mechanism outside this count (§5).

This count is **Lemma PL** (statement and proof at the top of this note). By (b) and (c), at k = 4 the repaired agent,
and every agent that shares two goods of its repair set, has no junk danger set left.

**Lemma candidate (K4-G4)** (`k4/ksens/g4_after.py`). Call a frozen agent (one whose base someone wants) *dangerous*
when it values the junk above its base.

> At k = 4, from every start whose picks have no one-absorber completion, some state reached by one improving chain
> has a one-absorber completion and leaves no dangerous frozen agent.

- **False at k = 4** (§5): the 11 counterexamples have no repairing chain at all.
- *Evidence of burst 1:* it held on every hard start tested here.
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

The bottom of the ladder:
- c = 0 (the picks of every order extend) holds for k ≤ 2 (serial dictatorship, K3.SD2) and fails at k = 3, where
  LB⁺ needs its rotation.
- c = 1 is OC. Within PW it holds at k = 4 (Lemma PWk (a)) and fails at k = 5 (§1). In general it fails already at
  k = 4 (§5): **PW is not the extremal family at k = 4.**

So in PW the least number of chains is ⌊(k − 1)/2⌋. This is proved for k = 5 (§1, c = 1) and computed for k = 5–9
(table). The general count is a heuristic: later chains can move pool pairs between frozen agents, and a full proof
for every c has not been written.

**Conjecture L (ladder; burst 2) is false.** It said: for every k, from every serial-dictatorship order, the picks
extend after ⌊(k − 1)/2⌋ improving chains. At k = 4 that is OC, refuted in §5.

**Conjecture L′ (corrected ladder).** For every k, from every maximum-matching start, the picks extend after ⌊k/2⌋
improving chains. Equivalently, c chains suffice up to k = 2c + 1.
- k ≤ 2: true (serial dictatorship needs none; L′ allows one).
- k = 3, one chain: exhaustive over strict profiles of connected hypergraphs for small n, from every start (§8).
- k = 4, two chains: tight (§5). **Two moves suffice for every strict profile of every core with n ≤ 4**: OC₂^max,
  certified by the certifier session (`k4/oc1cert.md` §1 on `compute/k4-oc1max-cert`, read here; its moves are the
  official ones, at most two in sequence, with a one-absorber completion). Beyond n = 4 it is evidence only.
- k = 5, two chains: tight (PW5, RD5). Climbs from PW starts (`climb.py oc2`, n = 5 at k = 5 and n = 6 at k = 6,
  50 rounds) found no start needing three chains.
- k = 6, 8: L′ allows 3 and 4; PW needs only 2 and 3. Whether k = 6 needs three chains is the open rung that decides
  between ⌊k/2⌋ and something smaller at even k.
- k = 7, 9: tight by PW (3 and 4 chains, ocseq.py).

Pool leftover ≤ 1 (Lemma PL) is what keeps PW from breaking one chain at k = 4. It does not give OC₁ at k = 4, which is
false. A proof of two chains at k = 4 and 5 (the rung c = 2 of L′) has to handle both the k = 5 pools of PW5 and the
mechanism of §5.

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

### OC₁ fails at k = 4 (burst 3)

*Source.*
- The certifier session (`compute/k4-oc1max-cert`, `k4/oc1cert/`) ran an ordinal CEGAR for OC₁^max over every strict
  profile of every n = 4 core hypergraph of the k = 4 core lists, 1,002 hypergraphs.
- On 11 of them it found a strict profile and a maximum-matching start with no repair (`results/k4_oc1max/cert_4.log`
  and `brute_verify_cex_n4.log` on that branch, read here).
- The coordinator relayed the first one.

*Replay here* (`refute_oc1max_k4.py`, `refute_oc1max_k4.log`), for all 11, with both checkers of this note.
- The checkers:
  - ocsat: SAT;
  - brute.py: every chain and every round enumerated from the definition, every completion checked against raw EFX₀
    over all n^m allocations.
- The start gives every agent a pick (ν = n = 4) and is reached by one to three orders (the certifier's count).
- From it there is no completion, free or one-absorber:
  - at the picks;
  - after any one chain, with or without empty passes (15 to 32 one-chain states);
  - after any one round.
- Two sequential chains repair it (ocseq.py). By brute force, 5 to 22 two-chain states have a one-absorber
  completion.
- The rest of the instance:
  - every other start satisfies OC₁;
  - MD holds for every order, and SD-C holds;
  - ocsat and brute force agree on every start of every order.
- Order classes (`oc1max_k4_orders.py`):
  - the failing start is reached by an R1-priority order;
  - every neediest-first start (need2, need1 and needall, plain or R1) satisfies OC₁.
- *Only the "every start" forms fail* (`oc1max_k4_exists.log`). In each instance the failing start is the only
  maximum-matching start (of 6 to 10) that one chain does not repair, and 4 or 5 of them complete at the picks with
  one absorber. So "some maximum-matching order works with one chain" and SD-C survive; TARGET₄ needs only those.

*The first instance, by hand.* Goods 0–6; order 0, 3, 2, 1; junk {0, 3, 4}.

| agent | values | pick |
|---|---|---|
| 0 | g1 10, g5 7, g2 4, g0 2 | g1 |
| 1 | g1 10, g6 8, g5 4, g2 3 | g2 |
| 2 | g6 7, g5 6, g4 5, g3 3 | g5 |
| 3 | g6 4, g3 3, g4 2 | g6 |

- *The wanter.* Agent 1 values every other pick above its own (10, 8, 4 > 3) and values no junk. While it holds g2,
  agents 0, 2 and 3 must hold their picks alone: {y, x} minus x is y, worth more to agent 1 than g2.
- *The pool.* Agents 2 and 3 are frozen and share the danger pair D = {3, 4}: 3 + 5 = 8 > 6 for agent 2, and
  3 + 2 = 5 > 4 for agent 3. So no bundle of three or more goods may contain D.
- *At the picks* only agent 1 can take junk, so it takes {0, 3, 4}. Agent 2 removes g0 from {2, 0, 3, 4} and sees
  8 > 6.
- *Repair agent 2* (agent 2 takes D, agent 1 takes g5, and g2 becomes junk).
  - Agent 1 now wants g1 and g6, so agents 0 and 3 stay singletons.
  - Agent 2's {3, 4} can take nothing more: for agent 3, {3, 4, x} minus x is worth 5 > 4.
  - So agent 1 takes the junk {0, 2}, and agent 0 sees {5, 0, 2} minus g0, worth 7 + 4 = 11 > 10.
- *Repair agent 3* (agent 3 takes D, agent 2 takes g6 from it, and g5 becomes junk; or agent 1 takes g6 and g2
  becomes junk).
  - In the first form agent 1 still holds g2 and wants g1 and g6, so agents 0 and 2 hold them alone. Agent 3's pair
    can take nothing more (agent 2, now worth 7, would see {3, 4, x} minus x, worth 8). So the junk {0, 5} goes to
    agent 1, and agent 0 sees {2, 0, 5} minus g0, worth 11 > 10.
  - In the second form agent 2 wants g6, so agent 1 holds it alone; agent 0 stays a singleton; agent 3's pair can
    take nothing (agent 2 would see 8 > 6). So agent 2 takes {0, 2}, and agent 0 sees {5, 0, 2} minus g0, 11 > 10.
- *The remaining one-chain states* (15 in all) fail too, by both checkers.
- **The mechanism.** A repair uses D up, but the chain releases a pick into the junk (g2 or g5). That pick, together
  with another pick, is a danger set of agent 0: g5 + g2 = 11 > 10. Whoever takes the junk then holds it.
  - This is exactly what Lemma PL does not cover: a released base, and a danger set made of another agent's pick plus
    junk.
  - No agent values more than four goods, so k ≤ 4 does not exclude it.
  - PW cannot produce it at k = 4: its wanters value only picks, and its released goods are wanters' own goods,
    which nobody else values.
- **Two chains repair it** (brute force), with no absorber at all.
  1. Agent 3 takes D (5 > 4) and agent 2 takes g6 (7 > 6), releasing g5.
  2. A ring: agent 1 takes g1 (10 > 3), and agent 0 takes g2, g0 and g5 (4 + 2 + 7 = 13 > 10).

  The result is 0: {0, 2, 5}, 1: {1}, 2: {6}, 3: {3, 4}, which is EFX₀. The second chain gives agent 0 the danger set
  itself.

### Earlier k = 4 searches (bursts 1–2; none found the failures above)

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

**RD is false at k = 5: the instance RD5** (`k4/ksens/refute_rd_k5.py`, `refute_rd_k5.log`).
- *Found* by `climb.py round1` started from the n = 4 instance of `proof/kgen-n3` (at k = 6,
  `climb_round1_n4k6_kgen.log`), then shrunk by dropping goods (`rd_shrink.log`).
- *Instance* (n = 4, m = 7, strict values):

  | agent | goods (value) |
  |---|---|
  | 0 | 1 (57), 3 (44), 5 (33), 0 (26), 4 (24) |
  | 1 | 1 (12), 2 (11), 3 (6) |
  | 2 | 1 (9), 2 (8), 3 (6), 4 (1) |
  | 3 | 2 (53), 5 (47), 0 (36), 6 (4) |

- *Order (0, 3, 1, 2):* picks 1, 2, 3, 4 for agents 0, 3, 1, 2; the junk is {0, 5, 6}.
- *Result.* None of the 50 states one round reaches (30 of them by one chain) has a completion, free or with one
  absorber.
- *Checks:* SAT (ocsat with multi) and brute force (every round enumerated from the definition, `brute.Inst.rounds`,
  every allocation against the raw definition).
  - The three round implementations (ocsat, ocseq with rounds, brute force) agree on 1,364 start × completion pairs,
    48 of them failing one round (`xcheck_rounds.py`, `xcheck_rounds.log`, 0 mismatches).
- *What still holds:* two sequential chains repair it (18 two-chain states complete). MD and SD-C hold; OC₁ fails only
  from this start.
- *The k = 4 version* (agent 0 without good 4) satisfies one round, OC₁ and everything else. Agent 0 cannot lose any
  of its five goods: every single drop restores RD.

*The mechanism (a second place where k ≤ 4 enters).*
- Agents 0 and 3 are both frozen: agents 1 and 2 want their picks. They share the junk pair {0, 5}, which is a danger
  set for both (26 + 33 > 57; 36 + 47 > 53).
- Agent 3 gains only by taking {0, 5}: it values nothing else but its pick and good 6.
- So agent 0 must repair itself without {0, 5}. Its only other improving sets need both 3 and 4, the picks of agents
  1 and 2, or 3 with a pool good that agent 3 needs.
- A chain's head takes goods from its own chain's end only, and a middle agent receives one base. So one chain gives
  agent 0 at most one other agent's pick, and a round does too: agent 0 lies on one chain.
- Two sequential chains do it: the first moves agent 2 off good 4 (releasing it), the second lets agent 0 take good 3
  from its chain's end plus the released good 4. This is exactly the "ring around a released good" gap described
  above.

It needs five goods for agent 0: its pick, the two shared pool goods that make it dangerous, and the two foreign picks
of its repair set. With four goods, an improving set that avoids two pool goods consists of at most one further good;
when that is another agent's pick, one chain reaches it from its end.

**Consequences.**
- RD and RD₁ are k ≤ 4 statements like OC₁: true on all k = 4 data (they are implied by OC₁) and false at k = 5. A
  proof of them at k = 4 must use k ≤ 4.
- The next candidate is **two rounds** (RD²). In RD5 the first round releases the foreign picks an agent needs, and
  the second collects them. For this mechanism two rounds suffice however many picks are needed, since all of them can
  be released in parallel in the first round.
  - RD² for all k would still contain EFX₀ existence.
  - Whether it fails at some k is open. The ladder of chains (§4) needs ⌊(k − 1)/2⌋ chains, but PW needs only one round.
  - `ocseq.py` with `multi=True` decides c rounds in one SAT call: RD5 needs exactly two, every PW instance one.
  - Climbs against RD² (`climb.py rd2a`, one absorber, seeded from RD5 and the n = 4 instance; `climb_rd2_*.log`):
    n = 4 at k = 5 (30 rounds) and k = 6 (30), n = 5 at k = 6 (20). No start needs three rounds. The n = 4 climbs
    keep finding starts that need exactly two.
  - *A design to try next:* RD5's mechanism one level deeper.
    - A must collect the picks of B₁ and B₂ (RD5's agent 0).
    - Each Bᵢ can move only by collecting two foreign picks itself: picks cᵢ and c′ᵢ, worth less than bᵢ alone and
      more together.
    - Then the c's are released in round 1, the B's move in round 2, and A collects in round 3, unless A has
      alternatives.
    - This needs n ≥ 6, beyond the climbs so far. Whether it still fits k = 5 is what would separate "two rounds"
      from "any number".

## 7. Maximum-matching starts, and the PW count at general k

**Maximum-matching starts** (`k4/ksens/maxmatch.py`, `maxmatch.log`). A start is a matching of the agent–good graph.
It is a *maximum-matching start* when the number of agents with a pick equals the maximum matching size ν. OC₁^max
is OC₁ restricted to such starts; maximum-matching orders always exist.
- **Every failing start found here is a maximum-matching start**, in every case: PW5, RD5, the n = 4 instance of
  `proof/kgen-n3`, PW436, PWR1-6, NF2-6 and NF1R1-6 (ν = n, and every agent picks).
- So OC₁^max is false at k = 5, by PW5, RD5 and the n = 4 instance, and already at k = 4, by the certifier's 11
  instances (§5).
- *One round from a maximum-matching start* is false at k = 4 (§5), and at k = 5 by RD5.
- Every PW start is a maximum-matching start, so maximum-matching starts need at least ⌊(k − 1)/2⌋ chains for
  k = 5–9 (PW) and two at k = 4 (§5).
- *Two rounds* from maximum-matching starts survive everything so far: RD5 and the 11 instances of §5 need exactly
  two, PW one. Climbs
  restricted to maximum-matching starts (one absorber):
  - `climb.py rd2amx`, n = 4 at k = 5 (30 rounds, from RD5 and the n = 4 instance; 12 end at a start needing exactly
    two rounds) and n = 5 at k = 6 (20 rounds, from PW): no start needs three rounds (`climb_rd2mx_*.log`);
  - `climb.py oc1mx`, n = 5 at k = 4 from PW-design starts (30 rounds): no OC₁^max failure; the least number of
    repairing states reached is 1 (`climb_oc1mx_n5k4.log`). This climb missed the n = 4 failures of §5.

### Lemma PWk (the PW count at general k)

*The family.* PW(f, W, r), clean values (`fam_ladder.clean`; it is the family of §1 with W wanters and a pool of r).
- *Frozen agents* x₁, …, x_f. Agent x_j values its good p_j at P = 20 and every good of a pool D, |D| = r, at less than
  P (19, 18, …). Every pair of D is worth more than P, so this needs r ≤ 10.
- *Wanters* w₁, …, w_W. Each values every p_j above its own good q_i and nothing else, with the same ranking p₁ > … > p_f.
- *Order* x₁, …, x_f, w₁, …, w_W.
  - Picks: p_j for x_j, q_i for w_i.
  - Junk: D.
  - The start is a maximum-matching start, and every x_j is frozen as soon as W ≥ 1.
- *Sizes:* k = max(r + 1, f + 1), n = f + W, m = f + W + r.

*Junk and danger sets.* For x_j holding p_j alone, the danger sets in the junk are exactly the pairs (and larger
subsets) of D. A single good of D is never one.

**Lemma PWk.**
- **(a) [proved; referee: correct with fixes, applied]** If r ≤ 3, at most one chain repairs the start, with a
  completion that has at most one absorber, for every f and W (W = 0 needs no chain). In particular PW never breaks
  OC₁ at k ≤ 4, where r ≤ 3 and f ≤ 3.
- **(b) [computed for f ≤ 5, W ≤ 4, r ≤ 8 (`pw_grid.py`, `pw_grid.log`); proved for (3, 2, 4) in §1]** One chain
  fails (no completion, free or one-absorber) exactly when
  > W ≥ 2 and W + 2 ≤ r ≤ min(W + f − 1, 2f − 1).

  On every failing cell one round of disjoint chains repairs (`pw_grid_round.log`).
- **(c) Consequence for k.** (b) needs r ≥ W + 2 ≥ 4, i.e. k ≥ 5. Since PW5 is k-limited for every k ≥ 5, one chain
  fails at every k ≥ 5 and never at k ≤ 4 within the family.

*Proof of (a)* (corrected after the referee, `k4/referee/ksens.md` §5 on branch `claude/k4-referee`; the earlier
W = 1 completion needed v_{w₁}(p₂) + v_{w₁}(q₁) ≤ v_{w₁}(p₁), which the family does not guarantee).
- *W = 0.* Nobody wants a pick, so no agent is frozen. With r ≤ 3 every agent has at most four goods, and Theorem DT⁺
  (`k4/sdc.md` §6) completes the picks with one owner and no chain.
- *W ≥ 1, r ≤ 1.* D holds at most one good, which is never a danger set; it goes to w₁, giving the two-good bundle
  {q₁, d}, and the picks extend.

Let W ≥ 1 and r ∈ {2, 3}.
1. *The chain:* x₁ → w₁. x₁ takes two goods d₁, d₂ of D (worth more than P, so it gains). w₁ takes p₁ (it values p₁
   above q₁, so it gains), and q₁ is released.
2. *The completion:*
   - x₁ gets {d₁, d₂}, w₁ gets {p₁};
   - x_j gets {p_j} for j ≥ 2, and w_i gets {q_i} for i ≥ 2;
   - the leftovers q₁ and (when r = 3) d₃ go as follows:

     | case | q₁ goes to | d₃ goes to | absorber |
     |---|---|---|---|
     | W ≥ 2 | w₂ | w₂ | w₂, bundle R = {q₂, q₁, d₃} |
     | W = 1, f ≥ 2 | x₂, bundle {p₂, q₁} | w₁, bundle {p₁, d₃} | none |
     | W = 1, f = 1 | x₁ | x₁ | x₁ (two agents only) |

3. *It is EFX₀.*
   - *An x_j (j ≥ 2), worth P* (x₂ with q₁ is worth the same P, since q₁ is worthless to it).
     - x₁'s bundle has two goods; removing either leaves one pool good, worth less than P.
     - R, and w₁'s bundle {p₁, d₃}, contain at most one good x_j values (d₃), worth less than P.
     - x₂'s bundle {p₂, q₁} contains no good x_j values.
     - Every other bundle is a singleton.
   - *x₁, worth more than P:* it values at most d₃ in R or in {p₁, d₃}, since p₁ is now worth less to it than its
     pair. It values nothing in the other bundles.
   - *w₁, holding p₁ (its top among the picks):*
     - It values only q₁ in R, and v_{w₁}(q₁) < v_{w₁}(p₁).
     - In x₂'s two-good bundle {p₂, q₁}, removing a good leaves p₂ or q₁, each worth less than p₁.
     - It values nothing in x₁'s bundle.
   - *The other wanters w_i* exist only when W ≥ 2, and then every p is held as a singleton: {p₁} by w₁, {p_j} by
     x_j. R contains no p and no q_i of theirs other than w₂'s own q₂. Since they value nothing but the p's and their
     own q_i, no bundle threatens them. (The two-good bundles {p₁, d₃} and {p₂, q₁} occur only when W = 1, where
     there is no other wanter.)
4. *Checks* (`pwk_check.py`, `pwk_check.log`), against the raw EFX₀ definition:
   - the allocation is EFX₀ for every f ≤ 6, W ≤ 5, r ∈ {2, 3} with clean values (60 configurations), and on 8,000
     random value assignments of the whole family;
   - on the referee's instance (wanter values 12, 8, 5) the earlier completion fails and this one is EFX₀;
   - W = 0 completes at the picks on all 305 starts tested. ∎

*Scope.* At k ≤ 4 the family has r ≤ 3 (each x values its pick and the pool) and f ≤ 3 (each wanter values the f
picks and q), so (a) covers every PW instance with at most four goods per agent. (a) itself holds for every f.

This is Lemma PL (b), (c) at work: after the repair at most r − 2 ≤ 1 pool good is left, and it threatens nobody.

*What one chain removes and what is left (the count behind (b)).* One chain has three ways to deal with the pool:
1. **Repair only its head.** Two goods of D go to x₀. The W − 1 unused wanters keep every other x frozen, so those
   hold their picks alone, and every bundle of three or more goods may hold at most one good of D (Lemma PL (d)). The
   r − 2 remaining goods need r − 2 slots; only the W − 1 unused wanters give one each. This fails iff
   **r − 2 > W − 1**, i.e. r ≥ W + 2.
2. **Repair through every wanter in one chain.** The chain alternates x, w, x, w, …. Each wanter takes a pick it ranks
   above the rest, so afterwards nobody wants the f − W unrepaired picks.
   - The middle x's hold {received base} plus a pair, which threatens an unrepaired x unless that x holds a pool good
     of its own. With the pool goods suitably assigned, that is enough on the computed cells; this is a heuristic, not
     a proof.
   - The r − 2W remaining goods must cover the f − W unrepaired agents. This fails iff **r − 2W < f − W**, i.e.
     r ≤ W + f − 1.
3. **Repair everybody.** That takes two goods each. It fails iff **r < 2f**.

(b) says one chain fails exactly when all three fail.
- At k ≤ 4 strategy 1 always works (r − 2 ≤ 1).
- In general the bound r − 2 ≤ W − 1 is the k − 3 count of Lemma PL (r ≤ k − 1).

*More chains and rounds.*
- With c chains the head-only count becomes r − 2c > W − c, giving the ladder ⌊(k − 1)/2⌋ of §4.
- One round can use strategy 1 with up to W heads at once, each with its own wanter. The count then becomes
  r − 2s > W − s for s repairs, and s = W (or all of the frozen agents) closes it. Observed: one round repairs every
  PW instance tested (no proof).
- What one round cannot do is RD5's two-foreign-picks repair (§6).

## 8. The general-k picture (summary)

*Setting.* Additive instances in which every agent values at most k goods. A *start* is the serial-dictatorship picks
of an order.
- A *chain* is the improving chain of `k4/sdc.md` §29; a *round* is a set of vertex-disjoint chains applied at once
  (§6).
- A *completion* is a complete EFX₀ allocation keeping every base, free or with one absorber.
- "Holds" at k = 4 means: on all data, never proved.

| statement (from every start of the given kind, unless "some") | k ≤ 2 | k = 3 | k = 4 | first failure | smallest counterexample | checks |
|---|---|---|---|---|---|---|
| the picks extend (no chain) | proved (K3.SD2) | **fails** | fails | k = 3 | n = 2, m = 4 (`k3_zero.log`) | SAT, brute force |
| one chain: OC₁ / OC; also restricted to maximum-matching starts | | holds: every strict profile of every connected hypergraph, every start for n ≤ 4, maximum-matching starts for n = 5 (below) | **fails** | **k = 4** | the certifier's 11 cores, n = 4, m = 7 or 8 (§5); at k = 5 also PW5 (written proof, refereed) and RD5 | SAT, brute force |
| one chain from R1-priority starts | | | **fails** | **k = 4** | the 11 (§5); PWR1-6 at k = 6 | SAT; brute force for the 11 starts |
| one chain from the need2 neediest-first start | | | holds (data; the 11 included) | **k = 6** | NF2-6: n = 6, m = 11 (§4) | 2 SAT encodings, SAT-free |
| one chain from the need2 R1 neediest-first start (LB₄ʳ's Phase 1) | | | holds | none found | | |
| c chains (the least c that always suffices) | c = 0 | c = 1 (exhaustive, small n) | c = 2: certified for every strict profile of every core with n ≤ 4 (certifier); c = 1 fails | c = 1 at k = 4; c = 2, 3 at k = 2c + 3 found | the 11 (c = 1); PW(c + 2, c + 1, 2c + 2) (§4) | ocseq, brute force |
| one round of disjoint chains (RD, RD₁) | | | **fails** | **k = 4** | the 11 (§5); RD5 at k = 5 | SAT, brute force over every round |
| two rounds (RD²), also from maximum-matching starts | | | holds | none found (climbs k = 5, 6, 8; n ≤ 6) | | |
| SD-C: some order whose picks extend | | holds (data; K4.SDC.K3 open) | holds | none found (k ≤ 8) | | |
| MD: every start value-dominated | | | holds | none found (k ≤ 8) | | |
| conclusions of Theorems DT, DT⁺, Lemma GDT, Theorem DT₁ | | | proved | **k = 5** | DT5: n = 2, m = 6; DT1-5: n = 3, m = 8 (§3) | SAT, brute force |

**The k-dependence in one count** (Lemma PL, top of this note).
- A frozen agent's junk danger sets live inside its at most k − 1 lower goods.
- A repair spends two of them, so at most k − 3 are left.
- Each rung of the ladder:
  - *k ≤ 2:* the pool has at most one good, so no danger set and no chain (serial dictatorship).
  - *k = 3:* a pool of two, a danger pair, one chain; nothing is left after it (`k3_zero.log`; LB⁺'s rotation).
  - *k = 4:* a pool of three; after one repair one good is left, never a danger set, so PW needs one chain. One chain
    is still not enough in general: a released pick plus another agent's pick can be a danger set (§5). Two chains
    are needed.
  - *k = 5:* a pool of four; two goods are left and still a danger set for the agents sharing the pool (PW5); or the
    repair needs two foreign picks (RD5). One chain is not enough.
  - *Larger k:* the head-only count r − 2c > W − c (Lemma PWk) gives ⌊(k − 1)/2⌋ chains in PW.
- The k ≤ 4 inputs found here. They rule out the PW and RD5 mechanisms at k = 4, not every failure of one chain:
  - Lemma PL (b), (c);
  - Lemma PWk (a);
  - the one-agent counts in Theorem DT's (F4) and DT₁'s step 3;
  - RD5's five-good requirement: pick, shared pair, and two foreign picks. One round fails at k = 4 anyway (§5).

**What might hold for every k.**
- MD, SD-C and two rounds (RD²) have no counterexample. Each of them, for every k, contains EFX₀ existence for all
  additive instances, which is open for n ≥ 4.
- Conjecture L (⌊(k − 1)/2⌋ chains) is false at k = 4 (§5). Conjecture L′ (⌊k/2⌋ chains from maximum-matching starts,
  §4) is consistent with every rung computed (k = 2 to 9).
- *Why depth is hard to build* (`fam_depth.py`, `attempts/k4-ksens-depth-composition.md`). Forcing three rounds needs
  RD5's mechanism one level deeper, which means more agents. Every unfrozen agent added is a free slot for one junk
  good, and a single slot already dissolves RD5's obstruction.
- *Data* (`rd5_plus.py`, `rd5_plus.log`). Adding two random agents to RD5 dissolves its obstruction:
  - in 33 of 40 instances no start needs any chain;
  - in the other 7, one chain or one round suffices from every start.
- *Two-round climbs* from these instances (n = 6, k = 5, 6; 40 climb rounds) and from PW starts at k = 8 found no
  start needing even two rounds (`climb_rd2mx_n6k*.log`; `climb_rd2mx_n5k8.log` was stopped after 5 of its 20 runs).
- So among the obstructions found, slots limit depth: they need few agents, and extra agents repair them. That is a
  heuristic, not a proof.

**Evidence base** (all evidence only). Each refutation is checked by two independent programs: SAT (sdclib's EFX₀
clauses with this note's chain or round encodings) and a brute force or SAT-free enumeration from the definitions.
PW5 also has a written proof, refereed by the coordinator (`k4/referee/ksens.md` on the coordinator's branch, not
read here). Random surveys: 12,000 instances at k = 5–8. Climbs: 786 climb rounds over the targets above (`climb_*.log`, the n = 6 runs still in progress). Structured
k = 4 searches: 80,000 instances, none of which found the k = 4 failures of §5.

**k = 3, exhaustively over strict profiles** (`k3max.py`, `k3max_n*.log`; SAT cross-check `k3max_xcheck.py`,
`k3max_xcheck_*.log`).
- *Scope.* Every connected agent–good hypergraph with n agents, each valuing at most three goods (nauty-genbg: 52 at
  n = 3, 396 at n = 4, 3,988 at n = 5).
- *Every strict profile, through its order type.* At k = 3 every comparison the question makes is between disjoint
  sets of one agent's goods: SD picks, a chain agent's new against its old base, and EFX₀. For three goods
  a > b > c the only such comparison the ranking leaves open is a against b + c. So 12, 2 or 1 types per agent cover
  every strict profile exactly (ties are excluded).
- *Result: no failure.* One chain followed by a one-absorber completion repairs
  - every start, maximum-matching or not, for n ≤ 4, under the official move rule and with empty passes:
    - n = 3: 25,816 profiles, 44,972 starts, 1,538 of them need a chain;
    - n = 4: 1,885,816 profiles, 4,982,948 starts, 126,994 need a chain;
  - every maximum-matching start for n = 5 (official rule): 178,767,520 profiles, 553,551,399 starts, 4,062,658
    need a chain (`k3max_n5.log`, 43 min on 4 CPUs).
- *Checks.*
  - Every repair is a witness, re-checked under its profile from the raw definitions: strict gains, EFX₀, at most
    one absorber.
  - A start with no cached witness is decided by exact backtracking.
  - ocsat (SAT) agrees on every maximum-matching start at n = 3 (43,751) and on 8,693 sampled at n = 4 (5,770 of them
    with m ≥ 6), with 0 mismatches.
- *So at k = 3 one chain suffices,* and the ladder's jump to two chains happens at k = 4.
  - At k = 4: one chain fails at n = 4 (§5), and two sequential moves are certified for every strict profile of
    every core with n ≤ 4 (`k4/oc1cert.md` on `compute/k4-oc1max-cert`).
  - The scope is connected instances. In a disjoint union each component may need its own chain; a round handles
    that.
  - The k3-oc1 session reports an every-order failure at k = 3 under the official rule, at n = 5 outside the cores
    [unverified here: read only in a commit message on `claude/k4-k3-oc1`]. This is consistent with the above, which
    covers every start only for n ≤ 4.

**Unrestricted k: every agent values every good** (`general_rounds.py`, `general_rounds_*.log`, `rd5_full.log`,
`kgen_n3_rounds.log`).
- *Setting.* Strict positive values, so EFX₀ and EFX coincide here; every start is a maximum-matching start.
- *n = 3 is the decisive case.* An EFX allocation is known to exist for three additive agents: Chaudhury–Garg–Mehlhorn,
  arXiv 2002.05119, as recorded in `proofs/citations.md` item 5, not read in this workstream. So a start needing three
  rounds there would refute "two rounds" without contradicting EFX₀ existence.
- *PW5 lifted to full valuations* (every value ×100, the goods an agent did not value worth 1, 2, …; k = m = 9).
  - One chain still fails, and one round repairs.
  - So OC₁ fails at unrestricted k with all values positive. PW's mechanism does not need zero values.
- *RD5 lifted the same way* (k = m = 7) needs only one round. Its mechanism needs the zeros: with every good valued,
  an agent can gain by adding any tiny junk good, which makes chains much more flexible.
- *The two configurations of `kgen/n3.md` §10* (branch `claude/kgen-n3`, read here): their stated starts extend
  without a chain, and no start of either needs more than one round.
- *Climbs maximizing the rounds needed* (values only; one-absorber completion; `general_rounds_climb_*.log`):
  n = 3, m = 7 (18 runs, stopped) and m = 8 (9 runs, stopped); n = 4, m = 7 (10 runs). No start needs two rounds:
  the climbs top out at starts needing one round.
- *Random profiles* (`general_rounds_rand.log`): no start needs more than one round, one-absorber or free.
  - n = 3, m = 5–9: 400 profiles, 629 starts; 104 need one round with one absorber, 12 with the free completion.
  - n = 4, m = 6–8: 80 profiles, 194 starts; 11 need one round.
- *Climb at n = 5, m = 9 from PW5 lifted* (3 runs, 60 steps each; `general_rounds_climb_n5m9_pw5.log`): every run
  ends at starts needing one round, 7 to 10 of them. None needs two.
- *Conclusion at unrestricted k:* within n ≤ 5, m ≤ 9 no start needs even two rounds. So the decisive n = 3 test does
  not refute RD². It only shows that with every good valued, one round has sufficed everywhere tested, at n = 3
  every start.
  - Compare k = 5 with zeros (RD5), where two rounds are needed.
  - Zero values make the problem harder for rounds, not easier.
