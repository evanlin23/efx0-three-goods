# k-sensitivity: where SD-C, MD, OC and OC₁ break as k grows

Angle `proof/k4-ksens` of the TARGET₄ campaign (`k4/attack_log.md`), branch `claude/k4-ksens`, PR #98. Code
`k4/ksens/`, logs `results/k4_ksens/`. Definitions as in `k4/sdc.md` §2 (SD-C), §28 (MD), §29 (OC, OC₁): a *start* is
the serial-dictatorship picks of an order, the *junk* is what nobody picked, an *improving chain* is §29's move (every
agent on it strictly gains), and a *completion* keeps every base. Random and climbed instances are evidence only
(PROMPT.md §5 rule 3).

## Status (bursts 1–5)

**Burst 5: how the number of moves grows, k = 6 exactly, and Conjecture RF at k = 5** (§4, §8). *Stopped at
the campaign wind-down, 2026-11-27 06:53 UTC.* Every sweep below marked running is partial; its log ends with a
PARTIAL line giving the count done:
- k = 6, two chains, exact mode: n = 3, 19 of 950; n = 4 core-like, 93 of 891; designed instances, 4 of 18. All
  certified.
- RF at k = 5, n = 4: 784 of 1,138, with 4 FAIL (§8).
- RF∃ at k = 5, n = 4: 471 of 1,138, all certified.
- k = 5, two chains, n = 4 core-like with m ≥ 8: 875 of 8,870, all certified.
- **Sequential chains: the number needed grows with k, from maximum-matching starts.** [R]
  - PW(4, 3, 6) (k = 7, n = 7, m = 13): no state reachable by two chains has a completion, not even a free one. Three
    chains repair it.
  - The two checks are independent:
    - ocseq: c chains in one SAT encoding;
    - kchains: breadth-first search that lists all 158,100 one-chain states (uncapped) and tests each with an ocsat
      call for one more chain, empty passes allowed (`ladder_pw436_bfs2_free.log`).
  - PW(5, 4, 8) at k = 9 needs four chains (ocseq only).
  - So "two sequential moves" fails from k = 7 on. Within PW the least number is ⌊(k − 1)/2⌋ (computed for
    k = 5 to 9).
- **Rounds of disjoint chains behave differently.** One round repairs every PW instance, and two rounds (RD²) have
  no failure anywhere. If any notion of "two moves" holds at every k, it is two rounds.
- **k = 6 can now be certified exactly** (§8). Two changes made the CEGAR at six goods fast and exact:
  - *Bitsets.* Every comparison of six ranked goods is precomputed as a bitset over the grid points, so a
    realizability check is a chain of word ANDs. This is 20–60 times faster than before, with the same iterations
    and cuts (`kcegar_grid_check_fast.log`, 12 of 12).
  - *Exact mode.* The grid only proposes cores. A core becomes a cut only after a rational LP proves it unrealizable
    over the reals; an LP point joins the grid otherwise. Verdicts then cover every strict profile.
  - *Validation* (`kcegar_exact_check.log`, 16 of 16):
    - with an incomplete five-good grid (145 of 516 types per ranking), the verdicts equal those of the full type
      lists, FAIL cases included;
    - at six goods, two grids and the slow LP route give the same verdicts.
- **CGM's Table 3 hypergraph (k = 6, n = 3): one chain suffices** from every maximum-matching start, for every strict
  profile [Cert] (`kcegar_cgm_exact.log`). The LP added 5,956 strict points that the B = 48 grid lacks.
- **Does k = 6 need a third chain? Nothing needs one so far** (exact mode, D = 2, running):
  - three agents: the n = 3 hypergraphs that extend a k = 5 one-chain failure by one good go first (36 of the 950);
  - four agents: the core-like hypergraphs with m = 6, 7 (891; paused for the RF run);
  - the 18 designed instances;
  - every hypergraph finished so far is certified (counts in §8).
  - A three-chain climb from the k = 5 failures (n = 3, k = 6, 40 rounds) found nothing [E].
- **Conjecture RKMAX (rank-maximal start, coordinator's `k4/sdc.md` §31) fails at k = 5 with three agents** [R]:
  - N3K5 refutes it, and so do all 13 n = 3 hypergraphs where OC₁^max fails (`refute_rkmax_k5.py`, `rkcegar.py`).
  - The agents share their top two goods, so every SD order hands out ranks 1, 2, 3, and every maximum-matching SD
    vector has the same signature σ = (1, 1, 1, 0, 0). RKMAX then says OC₁ at every maximum-matching start, which
    fails. The same goes for leximin and rank sum.
  - "Some σ-maximal vector satisfies OC₁" holds on all 28 profiles tested. RF holds (next item).
  - At k = 4 the tool certifies RKMAX on the 11 cores, as the coordinator did. Its tops-only control fails there, as
    the coordinator found.
- **Conjecture RF, in its "every receiver-first order" form, fails at k = 5 with four agents** [R] (RF5,
  `refute_rf_k5.py`).
  - Agents 2 and 3 are twins. At the failing start, the receiver 2 put first gives back the same start with the twins
    swapped.
  - **The weak form RF∃ survives everywhere tested** [Cert]: some receiver-first order gives maximum-matching picks
    that satisfy OC₁. RF∃ still implies OC₁^∃max.
  - Tested exhaustively: n = 3 at k = 5, RF5's hypergraph, and the 11 k = 4 cores; n = 4 at k = 5 is running.
- **Conjecture RF (receiver first, `k4/sdc.md` §31 on main) holds at k = 5 for three agents** [Cert]:
  - `rfcegar.py` certifies every strict profile of all 411 n = 3 hypergraphs with a five-good agent. On the other 206,
    kcegar finds no failing start, so RF has nothing to check there.
  - The tool also certifies RF on the 11 k = 4 cores where OC₁^max fails. That agrees with the coordinator's n = 4
    certificate, which comes from different code.
  - As a control, the run without the receiver condition fails, and brute force confirms each failure.
  - A replay from the definitions (`rf_replay.py`): RF holds on all 15 failing starts of N3K5's family, RD5 and
    PW5.
  - Running: RF on the 1,138 core-like n = 4, k = 5 hypergraphs with m ≤ 7.

**Burst 4: k = 5 by exhaustive search over order types** (`kcegar.py`, §8).
- *The tool.* An ordinal CEGAR of my own, run over every strict profile of a hypergraph. It agrees with the
  certifier at k = 4, and with the k = 3 enumeration.
- *Two chains suffice* from every maximum-matching start, for every strict profile, of:
  - all 617 connected n = 3 hypergraphs with at most five goods per agent;
  - the hypergraphs of RD5 and of the n = 4 instance of `proof/kgen-n3`;
  - the 11 k = 4 counterexamples with one agent extended to five goods (22 hypergraphs).

  - PW5's hypergraph (three agents with five goods each): 179,619 iterations, 17 min.

  So two rounds suffice there too.
- *One chain fails already at n = 3 when k = 5:* N3K5, n = 3, m = 6, with agents valuing 5, 5 and 3 goods. Both
  checkers confirm it (`refute_oc1_k5_n3.py`).
  - One round fails on N3K5 too, free or one-absorber.
  - It still fails with every good valued (N3K5⁺). So one round is not enough even for three agents with
    positive values, where EFX allocations are known to exist.
  - Two rounds repair it.
  - In all, one chain fails on 13 of the 617 n = 3 hypergraphs (m = 6, 7, 8). One of them has a single five-good
    agent (degrees 4, 4, 5).
- *Correction:* one round fails at strictly positive values (RD5⁺ of the kgen-rounds session, verified here). My
  earlier "zeros make rounds necessary" came from a tie in RD5 (§8).

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
PW(4, 3, 5), `ladder_pw436.log` shows PW(4, 3, 6) needs more than one, and `ladder_pw436_bfs2_free.log` that it needs
more than two.)

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
- k = 5, two chains: tight (PW5, RD5, and N3K5 at n = 3).
  - **Certified** for every strict profile of all 617 connected n = 3 hypergraphs with at most five goods per agent,
    of the hypergraphs of RD5 and kgen-n4, and of the 22 extended k = 4 counterexamples (`kcegar.py`, §8).
  - Climbs from PW starts (`climb.py oc2`, n = 5 at k = 5 and n = 6 at k = 6, 50 rounds) found no start needing three
    chains, and neither did the three-chain climbs from the k = 4 counterexamples at k = 4–6 (`climb_oc3amx_*.log`).
- k = 6, 8: L′ allows 3 and 4; PW needs only 2 and 3. Whether k = 6 needs three chains is the open rung that decides
  between ⌊k/2⌋ and something smaller at even k. Exact certificates of two chains at k = 6 (CGM's hypergraph, and the
  n = 3 and n = 4 sweeps running) are in §8.
- k = 7, 9: tight by PW (3 and 4 chains, ocseq.py).
  - At k = 7 a second check agrees: `kchains.py` lists all 158,100 one-chain states of PW(4, 3, 6) and finds none
    that one more chain repairs (`ladder_pw436_bfs2_free.log`, 1,059 s; free completion, empty passes allowed).
  - So two sequential chains fail at k = 7 from a maximum-matching start [R]. The number of sequential moves needed
    grows with k. Rounds do not grow this way within PW (one round repairs every PW instance).

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
- *Instance* (n = 4, m = 7; distinct values per agent, but not a strict profile: agent 0 has the tie
  v₀(4) + v₀(5) = 24 + 33 = 57 = v₀(1), which matters at full valuations, §8):

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
- "Holds" without a label means: on all data, never proved.

Labels: **[P]** proved (written proof); **[Cert]** certified for every strict profile of the stated class (exhaustive
order-type search or ordinal CEGAR, cross-checked by a second program); **[R]** refuted by an explicit instance that
two independent checkers confirm; **[E]** evidence only (data, random sampling, climbs). "max" = from maximum-matching
starts; n is the number of agents.

| statement (from every start of the given kind, unless "some") | k ≤ 2 | k = 3 | k = 4 | k = 5 | k = 6 | first failure; smallest counterexample |
|---|---|---|---|---|---|---|
| the picks extend (no chain) | holds [P] (K3.SD2) | fails [R] | fails | fails | fails | k = 3; n = 2, m = 4 (`k3_zero.log`) |
| one chain (OC₁, OC), max | | holds [Cert]: every connected hypergraph, n ≤ 5 (k3max, kcegar) | **fails [R]**: n = 4 (the certifier's 11, §5) | **fails [R] at n = 3** (N3K5); PW5, RD5 | fails | **k = 4**; n = 4, m = 7 |
| one chain, every start | | holds [Cert] for n ≤ 4, both move rules; **fails [R]** at n = 5 under the official rule only (MC2 shape) | fails [R]: the 11 under both rules; B<, MC2 under the official rule only | fails | fails | k = 3 under the official rule (n = 5, m = 9); k = 4 with empty passes |
| one chain from R1-priority starts | | | fails [R] (the 11) | fails | fails [R] (PWR1-6) | k = 4 |
| one chain from the need2 neediest-first start | | | holds [E] (the 11 included) | | fails [R] (NF2-6, n = 6) | k = 6 |
| one chain from the need2 R1 neediest-first start (LB₄ʳ's Phase 1) | | | holds [E] | | | none found |
| least number of chains that always suffices, max (Conjecture L′: ⌊k/2⌋) | 0 [P] | **1** [Cert], n ≤ 5 | **2**: 2 [Cert] on all cores with n ≤ 4 (certifier) and on the 11 (kcegar); 1 fails | **2**: 2 [Cert] on all 617 connected n = 3 hypergraphs, 25 named ones and the 1,138 n = 4 core-like hypergraphs with m ≤ 7 (m = 8: 875 so far, paused); 1 fails | ≥ 2; no start needs 3 so far: 2 [Cert] (exact mode) on CGM's hypergraph (where 1 suffices) and on every hypergraph the n = 3 and n = 4 sweeps have finished (below; running) | c = 1 at k = 4; **c = 2 at k = 7 [R]** (PW(4, 3, 6): ocseq and breadth-first search) |
| one round of disjoint chains (RD, RD₁), max | | holds [Cert] (one chain suffices) | **fails [R]** (the 11) | fails [R]: N3K5 (n = 3), RD5 | fails | k = 4 |
| one round with every good valued (unrestricted k, values > 0) | | | | | | fails [R]: N3K5⁺ (n = 3, m = 6), RD5⁺ (n = 4) |
| two rounds (RD²), max | | holds [Cert] | holds [Cert] where two chains are certified (n ≤ 4 cores) | holds [Cert] on the classes of the row above; [E] elsewhere | holds [Cert] where two chains are certified (row above) | none found |
| Conjecture RF (receiver first, `k4/sdc.md` §31), max | | | holds [Cert], n ≤ 4 (coordinator; here `rfcegar.py` on the 11) | holds [Cert] at n = 3 (`rfcegar.py`, all 617); n = 4 running | | none found |
| RF, every receiver-first order (the K4.SDC.RF form), max | | | holds [Cert], n ≤ 4 | holds [Cert] at n = 3; **fails [R] at n = 4** (RF5, twins) | | **k = 5**; n = 4, m = 7 |
| RF∃: some receiver-first order works, max | | | holds [Cert] on the 11 (`rfcegar.RFE`) | holds [Cert] at n = 3 and on RF5's hypergraph; n = 4 running | | none found |
| Conjecture RKMAX (every rank-maximal maximum-matching start), max | | | holds [Cert], n ≤ 4 (coordinator; here `rkcegar.py` on the 11) | **fails [R]** at n = 3: N3K5 (all maximum-matching vectors have σ = (1, 1, 1, 0, 0)) | | **k = 5**; n = 3, m = 6 |
| SD-C: some order whose picks extend | | holds [E] (K4.SDC.K3 open) | holds [E] | holds [E] | holds [E] | none found (k ≤ 8) |
| MD: every start value-dominated | | | holds [E] | holds [E] | holds [E] | none found (k ≤ 8) |
| conclusions of Theorems DT, DT⁺, Lemma GDT, Theorem DT₁ | | | proved [P] | fails [R] | fails | k = 5; DT5: n = 2, m = 6; DT1-5: n = 3, m = 8 (§3) |

Checks behind each [R]: SAT (ocsat or ocseq) and a brute force from the definitions (brute.py), with the certifier's
programs as a third check on the 11. Each [Cert] at k = 5 comes from kcegar alone; kcegar itself is cross-checked
against the certifier at k = 4 and against k3max at k = 3.

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
  - A second, independent method, the ordinal CEGAR `kcegar.py`, certifies one chain for every strict profile and
    every maximum-matching start of all 52, 396 and 3,988 hypergraphs at n = 3, 4, 5 (`kcegar_k3_n*_D1.log`).
    At D = 0 (no chain) it fails on exactly the 15 n = 3 hypergraphs where k3max found a start needing a chain.
    Over every start (`--any-start`, official rule) it certifies all 52 and 396 hypergraphs at n = 3, 4, as k3max
    found (`kcegar_k3_n*_D1_any.log`).
- *So at k = 3 one chain suffices,* and the ladder's jump to two chains happens at k = 4.
  - At k = 4: one chain fails at n = 4 (§5), and two sequential moves are certified for every strict profile of
    every core with n ≤ 4 (`k4/oc1cert.md` on `compute/k4-oc1max-cert`).
  - The scope is connected instances. In a disjoint union each component may need its own chain; a round handles
    that.
  - *Every start at n = 5 (`kcegar_k3_n5_D1_any.log`).* One chain, official rule, fails on exactly one of the 3,988
    hypergraphs, and only from a start that is not maximum-matching.
    - The hypergraph: sets [[0,2,6], [1,4,7], [3,5,8], [6,7,8], [6,7,8]], all values (2, 3, 4).
    - The start: picks 6, 7, 8 for agents 0–2, and agents 3, 4 get nothing (3 picks, ν = 5).
    - No one-chain state has a one-absorber completion (51 states). 6 have a free one, and with empty passes 34
      states have a one-absorber completion (brute force and ocsat).
    - This is the k = 3 failure reported by the k3-oc1 session (`claude/k4-k3-oc1`, there read only in a commit
      message), now checked here. It has the MC2 shape of `k4/sdc.md` §31: the pickless agents value only picks.

**k = 5 by ordinal CEGAR** (`kcegar.py`, `kcegar_batch.py`, `kcegar_*.log`; types `types5.py`).
- *Types of five goods.* The strict order types are the chambers of the arrangement v(S) = v(T) for disjoint S, T in
  the open orthant.
  - Each chamber has an integer point with coordinates at most 80. An extreme ray's coordinates are 4 × 4 minors of
    {−1, 0, 1} rows, at most 16 by Hadamard, and five rays sum to an interior point.
  - With the ranking fixed, scanning the C(80, 5) decreasing tuples finds 516 types, the same as the grid up to 40.
    So there are 61,920 types with the rankings (`types5.log`).
  - The same scan gives 12 types for three goods and 336 for four, the strict counts of `k4/order_types.json`.
- *The CEGAR.*
  - The outer SAT chooses comparison bits and the picks of a maximum-matching SD start.
  - Realizability is lazy: an agent's assigned bits are checked against its type list, and a minimal conflicting set
    is blocked. A one-hot encoding of the types is kept as `--onehot` and gives the same verdicts.
  - A witness is the exact picks plus the comparisons its chains and its completion need. The inner search is brute
    force over at most D chains (official rule), with backtracking completions on the raw definition.
  - Every FAIL is re-checked by brute force with empty passes allowed and by ocseq.
- *Validation.*
  - On the certifier's 11 k = 4 hypergraphs: D = 1 fails and D = 2 certifies (`kcegar_k4_cex.log`,
    `kcegar_lazy_check.log`), as in `k4/oc1cert.md`. Each failing profile is confirmed by ocsat and brute force.
  - At k = 3 it certifies D = 1 on every hypergraph with n ≤ 5, and its D = 0 failures are exactly k3max's.
- *Results at k = 5* (maximum-matching starts, one-absorber completion, every strict profile):
  - D = 2 is certified for all 617 connected n = 3 hypergraphs (`kcegar_k5_n3_D2.log`, 880 s on 2 CPUs). It is also
    certified for RD5's, kgen-n4's, PW5's (179,619 iterations, 17 min) and the 22 extended k = 4 hypergraphs
    (`kcegar_k5_D2.log`, 25 of 25). No start needs three chains, so none needs three rounds.
  - D = 2 is certified for all 1,138 n = 4 core-like hypergraphs with m ≤ 7 (`kcegar_k5_core5_n4_D2_m5-7.log`, 6,382 s on
    2 CPUs). The class: connected, agent degrees 3–5 with at least one 5, at most d − 2 private goods per agent; it
    is an analogue of the k = 4 cores, with no reduction lemma behind it at k = 5. The 8,870 with m ≥ 8 are running
    (checkpoint `kcegar_k5_core5_n4_D2_m8plus.ckpt.jsonl`).
  - D = 1 fails on 13 of the 617 n = 3 hypergraphs (`kcegar_k5_n3_D1.log`, 883 s).
    - By m: 7 at m = 6, 5 at m = 7, 1 at m = 8.
    - Degree profiles: (5, 5, 5) six times, (4, 5, 5) five times, (3, 5, 5) and (4, 4, 5) once each.
    - Every failing profile is re-checked: no repair within one chain by brute force with empty passes, nor by ocseq.

    The first failure is N3K5 (`refute_oc1_k5_n3.py`):
    - agent 0 values goods 0, 2, 3, 4, 5 at 3, 22, 23, 38, 43;
    - agent 1 values goods 1, 2, 3, 4, 5 at 15, 17, 27, 40, 43;
    - agent 2 values goods 1, 4, 5 at 1, 2, 4;
    - order (1, 0, 2) gives the picks 4, 5, 1, a maximum-matching start.

    Both checkers agree: no completion, free or one-absorber, at the picks, after one chain, or after one round. Two
    chains repair it. MD and SD-C hold.
  - So one chain first fails at k = 5 already for three agents, and at k = 4 for four (§5). At k = 3 it never fails
    from a maximum-matching start for n ≤ 5.

**k = 6: is a third chain ever needed?** (`kcegar.py` exact grid mode, `ratlp.py`, `typesk.py`; running)
- *Why six goods are hard.*
  - The strict types are too many to list. As I recall the count, it is 124,187 per ranking [unverified].
  - The completeness bound of the grid argument is 6 × 48 = 288, too large for a full scan.
  - The pure LP route (rational simplex for every realizability question) is exact but slow. On RD5 with agent 0
    extended to six goods it timed out after 3,000 s: 306 iterations, 282,989 LP calls
    (`kcegar_k6_named_D2_exactLP.log`).
- *Grid mode, made fast.* `typesk.py` lists the strict types with a decreasing integer representative in [1, B]⁶.
  There are 46,314 at B = 48 (`types6.log`).
  - The agent's ranking comes from its singleton bits. Each other bit is a comparison of two disjoint sets of the six
    ranked goods, precomputed as a bitset over the grid.
  - The first realizing point and a minimal core (progressive deletion) are word ANDs.
  - Answers are identical to the first version: same iterations and cuts, 12 of 12 (`kcegar_grid_check_fast.log`).
  - It is 20–60 times faster: n3_m6_105 at D = 2 takes 31.6 s instead of 1,703 s.
  - Alone, grid mode sees only the grid's types. A FAIL there is genuine, but "certified" is [E].
- *Exact mode* (`--exact6`; validated by `kcegar_exact_check.py`, `kcegar_exact_check.log`):
  - the grid, plus every real point found so far, only proposes a core;
  - the core becomes a cut only after `ratlp.realize` proves it unrealizable over the reals; the cut is the LP's
    sub-core plus the ranking;
  - if the LP realizes the core, its strict integer point joins the points, and the core is recomputed;
  - points and core verdicts are facts about R⁶, so they are cached and shared across hypergraphs. 95% of the core
    checks hit the cache.
  - So "certified" covers every strict profile.
  - *Validation, 16 of 16 agree.*
    - Five goods with an incomplete grid (B = 18: 145 of 516 types per ranking): exact mode gives the verdicts of the
      complete type lists on RD5, N3K5, n3_m7_15 and a holding case, at D = 1 (FAIL) and D = 2.
    - Six goods: exact mode on the B = 32 and B = 48 grids and the pure LP route give the same verdicts.
  - The first exact version (every core and full bit set sent to the LP) gave the same verdicts
    (`kcegar_exact_check_v1.log`). It was about 10 times slower.
- *CGM's Table 3 hypergraph* (sets {0,1,2,3,5,6}, {0,2,3,4,6}, {4,5,6}; `kcegar_cgm.py --exact6`,
  `kcegar_cgm_exact.log`).
  - **One chain suffices from every maximum-matching start, for every strict profile [Cert]**: 2,646 iterations,
    280 s, so two chains as well.
  - The LP added 5,956 strict points the B = 48 grid lacks, so grid-only certificates really were partial.
  - With CGM's own values (`kgen/charity/cgm_check.py` on `claude/kgen-charity`, read there), one chain suffices
    (ocsat and brute force).
- *Sweeps at D = 2, exact mode* (checkpoints `kcegar_k6_*_exact.ckpt.jsonl`; "certified" = for every strict profile and
  every maximum-matching start, two chains and a one-absorber completion):
  - n = 3: all 950 connected hypergraphs with a six-good agent (`kcegar_k6_n3_D2_exact.*`). The one-good extensions
    of the 13 k = 5 one-chain failures run first (36 of them; `--prio`). 16 certified so far, none failed; the
    slowest took 1,101 s.
  - n = 4, the core-like class (agent degrees 3–6 with a 6, at most d − 2 private goods; `kcegar_k6_core6_n4_D2_exact.*`):
    107 hypergraphs at m = 6 and 784 at m = 7. 93 certified so far (m = 6), none failed; paused for the RF run.
  - The 18 designed hypergraphs (`named6`: k = 5 and k = 4 instances extended to six goods): 2 certified so far.
  - Earlier grid-only runs, superseded: 31 n = 3 hypergraphs and the RD5 extensions certified on the B = 48 grid
    (`kcegar_k6_*_grid48.*`) [E].
- *Climb* (`climb.py oc3amx`, n = 3, K = 6, 40 rounds from the 13 k = 5 failure witnesses,
  `climb_oc3amx_n3k6_k5fail.log`): no start needing three chains. The best has 3 two-chain completions [E].

**Conjecture RF at k = 5** (`rfcegar.py`, `rfcegar_*.log`, `rf_replay.py`, `rf_replay.log`).
- *The statement* (`k4/sdc.md` §31 end, on main, amended version). Let Y be a maximum-matching SD start where OC₁
  fails, and u a receiver of Y: an agent with a pick that no other agent values above its own pick (an agent without a
  pick prefers every good it values). Then every order with u first whose picks Z are a maximum matching satisfies
  OC₁.
- *The tool.* An extension of kcegar.
  - The outer SAT carries a second pick system for Z, with its own SD order, |Z| = ν, and u first, plus a one-hot
    receiver u with the receiver clauses on Y.
  - The inner search tries to repair Y with one chain, then Z.
  - A repair witness is a cut on both pick systems, since a repair of given bases under given comparisons does not
    depend on which order produced them.
  - A FAIL is re-checked by brute force from the definitions.
- *Checks of the tool.*
  - At k = 4 it certifies RF on all 11 OC₁^max-failing cores (`rfcegar_k4_cex.log`, 1–4 s each). That agrees with
    the coordinator's certificate of RF at n = 4 from the certifier's export, by other code.
  - Without the receiver condition (`--any-receiver`, not RF) it fails on cex1–4, and brute force confirms each
    failure. So the FAIL path works.
- **Result: RF holds for every strict profile of every connected n = 3 hypergraph with at most five goods per agent**
  [Cert]:
  - all 411 with a five-good agent are certified (`rfcegar_k5_n3.log`, 1,444 s);
  - on the other 206, kcegar finds no maximum-matching start that fails OC₁ (`kcegar_k5_n3_D1.log`), so RF has
    nothing to check.
  - So RF survives the step from k = 4 to k = 5 at n = 3, where OC₁^max itself fails (N3K5).
- *Replay from the definitions* (`rf_replay.py`): the 13 kcegar witnesses, RD5 and PW5 give 15 failing
  maximum-matching starts. Each has a receiver (PW5 has two, {3, 4}), and every receiver-first maximum-matching pick
  vector completes at the picks or after one chain.
- **RF fails at k = 5 with four agents** [R]: RF5 (`refute_rf_k5.py`, `refute_rf_k5.log`).
  - It was found by the sweep over the 1,138 core-like n = 4 hypergraphs with m ≤ 7 (`rfcegar_k5_core5_n4.*`), on
    core5_n4_m7_688.
  - The instance:
    - agent 0: goods 0, 1, 2, 5, 6 worth 3, 35, 33, 43, 39;
    - agent 1: goods 1, 2, 4, 5, 6 worth 20, 26, 16, 43, 32;
    - agents 2 and 3 (twins): goods 3, 4, 5, 6 worth 8, 2, 7, 4.
    - The profile is strict (all subset sums of each agent distinct).
  - The start Y = (6, 5, 4, 3) comes from orders (1, 0, 3, 2), (1, 3, 0, 2) and (3, 1, 0, 2), and is a maximum
    matching (ν = 4). OC₁ fails there, even with the free completion.
  - Its only receiver is agent 2. The other three each have a pick another agent prefers: 0's good 6 (agent 2), 1's
    good 5 (agent 0) and 3's good 3 (agent 2).
  - The six orders with 2 first give six distinct maximum-matching vectors:
    - (2, 1, 0, 3) gives **Z = (6, 5, 3, 4), where OC₁ fails, even with the free completion**;
    - the other five satisfy OC₁: (1, 5, 3, 6) and (5, 6, 3, 4) after one chain, (1, 6, 3, 5), (5, 2, 3, 6) and
      (6, 2, 3, 5) at the picks.
  - Both checkers agree on every vector: brute force from the definitions, and ocsat.
  - *Mechanism.* Z is Y with the twins' picks exchanged.
    - In Y the twin 3 is served before 2 and takes their common top good 3, so 2 gets good 4.
    - With 2 first, 2 takes good 3, and in the order (2, 1, 0, 3) its twin gets good 4.
    - Up to relabelling the twins, Z is Y, and now the twin 3 is the receiver.
    - So "every receiver-first order" cannot hold once a receiver has a twin that the rest of the order serves in the
      old position.
  - At k = 4, RF is certified at n ≤ 4 (K4.SDC.RF), and rfcegar certifies it on the 11 cores. So RF in this form is
    k-sensitive. The step to k = 5 lets agents 0 and 1 hold five goods each, which is what makes this start fail OC₁.
- **Twins are not the whole story: RF5b** (`refute_rf_k5.py`, second instance).
  - Same hypergraph and start, with vals [[3,22,23,43,38],[20,26,16,43,32],[10,2,7,4],[8,1,6,4]].
  - Agents 2 and 3 rank their goods the same way (3 > 5 > 6 > 4) but differ in type: v₂(3) + v₂(4) = 12 > 11 =
    v₂(5) + v₂(6), while v₃(3) + v₃(4) = 9 < 10 = v₃(5) + v₃(6).
  - The same Y and Z fail OC₁, by both checkers.
  - It was found by `rfcegar.RFT`. That form excuses a failing receiver-first vector that is the start with
    identical-type agents' picks permuted; "identical type" is exact, via XOR literals over every comparison bit of
    the pair.
  - So "every receiver-first order, up to relabelling exact twins" fails too.
- **Up to ordinal twins it holds on this hypergraph** [Cert] (`rfcegar.py --ordinal-twins`). Ordinal twins have the
  same relevant set and the same ranking of single goods.
  - Every strict profile is covered: 7,549 iterations, 4 twin images excused.
  - SD sees only rankings, so permuting ordinal twins maps SD starts to SD starts. That is a natural excuse.
  - The candidate refined statement: every receiver-first maximum-matching vector satisfies OC₁, unless it is the
    start with ordinal twins' picks permuted.
- **Partial sweep result, stopped at the campaign wind-down (2026-11-27 06:53 UTC)** [E]
  (`rfcegar_k5_core5_n4.log`, `.ckpt.jsonl`).
  - The every-form sweep finished 784 of the 1,138 n = 4 hypergraphs: 780 certified, 4 FAIL (core5_n4_m7_688, 807,
    816, 826).
  - Each FAIL was re-checked by brute force only: start, receiver and receiver-first vector, OC₁ failing at both.
    ocsat was not run on 807, 816 or 826.
  - In all four, the failing receiver-first vector Z is the start Y with two agents' picks swapped.
  - In 688 and 816 the swapped agents have the same relevant set.
  - In 807 and 826 they do not: they are agents 0 and 1 with R₁ = {1,4,5,6} ⊂ R₀ = {0,1,4,5,6} in 807, and
    R₁ = {1,3,4,5,6} in 826.
  - So the ordinal-twin form, which is certified only on 688's hypergraph, probably needs more than equal sets. It
    was not run on 807, 816 or 826. Open.
- **RF∃ ("some receiver-first order works") survives** (`rfcegar.RFE`; `rfecegar_*.log`).
  - *The tool.* One SD pick system per fixed order (24 at n = 4), each with an indicator of being a maximum matching.
    A violation needs every u-first order to give non-maximum picks or picks that fail OC₁. A repair witness of any
    vector is a cut on every pick system whose order starts with u.
  - *Controls.*
    - At k = 4 it certifies the 11 cores.
    - With no chain allowed (D = 0) it fails, as it must, and brute force confirms that no receiver-first vector
      completes at the picks.
  - *Certified* [Cert]:
    - the 13 n = 3, k = 5 hypergraphs where OC₁^max fails (elsewhere at n = 3 no start fails, so RF∃ holds);
    - RF5's hypergraph.
  - *Partial* (stopped at the wind-down): 471 of the 1,138 n = 4, k = 5 core-like hypergraphs certified, no violation
    (`rfecegar_k5_core5_n4.*`) [E for the class].
  - RF∃ gives OC₁^∃max as RF does, since a receiver-first maximum-matching order where OC₁ holds is all that
    argument uses. So RF5 does not touch the route to TARGET.

**Conjecture RKMAX at k = 5: false** (`rkcegar.py`, `rkcegar_*.log`, `refute_rkmax_k5.py`, `refute_rkmax_k5.log`).
- *The statement* (coordinator's `k4/sdc.md` §31 end, ledger K4.SDC.RKMAX on branch `claude/kind-lamport-y8fdme`,
  read there).
  - rank_i = 1 + the number of agent i's relevant goods valued above its pick. σ(Y) = (#rank 1, …, #rank k).
  - RKMAX: every maximum-matching SD vector whose σ is lexicographically maximal among the maximum-matching SD
    vectors satisfies OC₁.
- *The tool.* kcegar's outer SAT, with a lazy σ-maximality check over all n! orders under the model's ranking.
  - If an order gives a maximum-matching vector Z with σ(Z) > σ(Y), the cut is: not Y, or not the singleton
    comparisons that fix SD = Z and the ranks of Y's and Z's picks.
  - Otherwise the one-chain repair search runs at Y.
  - At k = 4 it certifies RKMAX on all 11 OC₁^max-failing cores (`rkcegar_k4_cex.log`), as the coordinator's
    certificate says.
  - The tops-only control (σ = #rank 1 alone, which the coordinator found fails) fails on 5 of the 11, and brute
    force confirms each failure.
- **Result: RKMAX fails on all 13 n = 3, k = 5 hypergraphs where OC₁^max fails** [R] (`rkcegar_k5_n3.log`).
  - `refute_rkmax_k5.py` re-checks every witness by brute force and by ocsat: the rkcegar witnesses, the kcegar
    witnesses and the 15 starts of `rf_replay.py`, 28 profiles in all. RKMAX fails on 26; the checkers never
    disagree.
  - N3K5 itself is one of the 26:
    - agent 0 ranks 5 > 4 > 3 > 2 > 0, agent 1 ranks 5 > 4 > 3 > 2 > 1, agent 2 ranks 5 > 4 > 1;
    - in every order the first agent takes 5 (rank 1), the second takes 4 (rank 2) and the third takes its third
      good;
    - so all 6 maximum-matching SD vectors have σ = (1, 1, 1, 0, 0), and the failing start (4, 5, 1) is σ-maximal.
  - The same holds for any selection that depends only on the multiset of ranks, such as leximin or rank sum.
  - RD5 and PW5 do satisfy RKMAX: their σ-maximal vectors need one chain.
- *What survives.* "Some σ-maximal vector satisfies OC₁" holds on all 28 profiles, but at N3K5 that is just
  OC₁^∃max. RF holds (above): the receiver distinguishes vectors that σ does not.
- *Why k matters.* At k = 4, three agents never fail OC₁^max. So the first place where all σ tie and OC₁^max fails is
  k = 5, n = 3.

**Unrestricted k: every agent values every good** (`general_rounds.py`, `general_rounds_*.log`, `rd5_full.log`,
`kgen_n3_rounds.log`).
- *Setting.* Strict positive values, so EFX₀ and EFX coincide here; every start is a maximum-matching start.
- *n = 3 is the decisive case.* An EFX allocation is known to exist for three additive agents: Chaudhury–Garg–Mehlhorn,
  arXiv 2002.05119, as recorded in `proofs/citations.md` item 5, not read in this workstream. So a start needing three
  rounds there would refute "two rounds" without contradicting EFX₀ existence.
- *PW5 lifted to full valuations* (every value ×100, the goods an agent did not value worth 1, 2, …; k = m = 9).
  - One chain still fails, and one round repairs.
  - So OC₁ fails at unrestricted k with all values positive. PW's mechanism does not need zero values.
- *RD5 lifted the same way* (k = m = 7) needs only one round, **but only because of a tie**.
  - In RD5, v₀(4) + v₀(5) = 57 = v₀(1). With every good valued, a ring repairs at that equality plus a small value.
  - With v₀(4) = 23 instead (RD5⁺, found by the kgen-rounds session, `proof/kgen-rounds`, `kgen/rounds.md`; reported
    to me by message, not read here), **one round fails with every good valued**.
  - Checked here with ocsat and with brute force over all 225 round states, for three choices of the small values;
    two rounds repair (ocseq). With the tie restored, one round suffices (`rd5plus_check.log`).
  - So my earlier remark that "RD5's mechanism needs the zeros" was wrong.
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
- *N3K5⁺: one round fails for three agents with every good valued.* N3K5 ×100 with its zeros replaced by 1, 2, …
  (k = m = 6).
  - From the same start, no round has a completion, free or one-absorber: ocsat, and brute force over 120 round
    states. Two rounds repair it (`refute_oc1_k5_n3.log`).
  - With random small values in place of the zeros it fails for some draws and not others (`n3k5_full.log`).
- *Conclusion at unrestricted k.*
  - One round fails with every good valued: RD5⁺ (n = 4, m = 7) and N3K5⁺ (n = 3, m = 6).
  - My random profiles and climbs never found a start needing two rounds, so they missed it. That is another case
    where sampling and climbing failed and a hand-made or exhaustive search did not (compare §5).
  - Two rounds repair every start tested, RD5⁺ and N3K5⁺ included. So the decisive n = 3 test does not refute RD²
    (it would need a start needing three rounds), but my earlier "one round sufficed on every n = 3 start tested" only
    reflected what random sampling reached.
  - Zero values are not what makes rounds necessary. The earlier conclusion was an artifact of RD5's tie.
