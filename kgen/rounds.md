# Rounds of disjoint chains at positive values (workstream `proof/kgen-rounds`)

Branch `proof/kgen-rounds`, draft PR #111. Code `kgen/rounds/`, logs `results/kgen_rounds/`. Coordinator's record:
`k4/attack_log.md` on `claude/kind-lamport-y8fdme`. Builds on `k4/ksens.md` §6–§8 (branch `claude/k4-ksens`, read
there at 63089336), `k4/sdc.md` §29–§31, `kgen/n3.md` (branch `claude/kgen-n3`) and
`reports/EFX literature from the agent side.md`. Random and climbed instances are evidence only (PROMPT.md §5 rule 3);
every refutation below is confirmed by three independent programs.

## Status (2026-11-26)

**Bottom line.**
- **ROUND⁺ is false.** In the conjecture's own setting (strictly positive additive values, every agent values every
  good), some serial-dictatorship start needs two rounds of vertex-disjoint improving chains. The smallest examples
  have n = 4 and m = 7, and it also fails at n = 4 with m = 8, 9 and at n = 5 with m = 8, 9 (§3).
  - The clean instance **RD5⁺** is ksens's RD5 with one value changed (agent 0's value of good 4 from 24 to 23),
    multiplied by 100, with every zero replaced by any ε in 1..99. So RD5's two-foreign-picks mechanism survives the
    lift to positive values. ksens's lift (`k4/ksens.md` §8) kept the value 24, which sits exactly at a tie
    (v₀(4) + v₀(5) = v₀(1)), and so missed it.
  - ROUND⁺ also fails with **two valuation types**: n = 4, agents 0 = 1 and 2 = 3 (§3.3). In that class EFX
    existence is known (Mahara, two monotone types, as cited by the literature report; not read here
    [unverified]). So ROUND⁺ fails where EFX itself is not in doubt.
- **The mechanism is one obstruction, with a two-line certificate (§3.1).**
  - A round reaches only allocations that value-dominate the picks (MD).
  - After one round, a base contains at most one other agent's pick.
  - In every failure found, every value-dominating EFX allocation has a *starved agent*. That agent has lost its
    pick, holds two foreign picks, and with only one of them plus its junk it does not beat its pick.
  - `refute_roundplus.py` checks this certificate by raw enumeration.
- **Two rounds repair every start found** (RD²⁺, §4). Each repair releases one foreign pick into the junk in round 1
  and collects it together with a second pick in round 2. Checked by ksens's ocseq (SAT) and by bruter.py's forward
  two-round simulation on every failure. Climbs toward a start needing three rounds have found none so far.
- **The one-step repairs of the mechanism.**
  - *ROUND-X* (chain starts may also take the released pick of any chain's end) fixes most failures, but fails itself
    at n = 4, m = 7 (§4.2): the starved agent is then a middle agent.
  - *ROUND-P* (every chain agent may take released end picks) survives everything. On the data it is nearly
    indistinguishable from MD (§4.2).
- **n = 3: one round survives everything** (§5). The data: random profiles, 170 climbs with m = 6–10, and kgen-n3's
  OC₁(t ≥ 0) evidence, which implies one round at n = 3.
  - Classification of what a start needs:
    - most starts keep their picks;
    - every other start but one is repaired by some two-agent move (a hand-off or a swap). The repairing pair varies:
      some starts need only a hand-off, some only a swap;
    - one random start (ROT3) needs the three-agent rotation (§5.2, verified by forward simulation).
  - The last picker almost never starts the repairing chain.
  - At n = 3, starvation never blocks every MD allocation on the data (§5.3). The only possible round structure
    around a starved agent is forced, but no proof.
  - **Lemma ID** (proved, any n): with identical valuations, the picks of every order extend.
- **k = 4 with zeros (for the campaign; §4.3).**
  - ε-lift climbs (at most four values per agent above ε) also break one round. Their zero versions are genuine k = 4
    instances at perfect starts where **OC₁ and one round fail**. Three programs agree, including k4/sdc's own OC₁
    pipeline.
  - In most of them a good is valued by nobody, and deleting it repairs them.
  - **K4W** has no worthless good. A top-heavy agent freezes a starved agent that uses exactly four goods.
  - So OC₁ at perfect starts is false for non-core k = 4 instances: this is the target of Lemma RED's route and the
    LOOSE form of OC₁^max. OC₁^max on cores is untouched: K4W's top-heavy agent is peeled by R1.
  - **OC₁^max (K4.SDC.OC1MAX, the campaign's central conjecture) is REFUTED** by **C4K**, a strict connected k = 4 core
    with n = 4, m = 7 (§4.4). From two perfect starts, no addition, chain or ring has a one-absorber completion.
    - Four programs agree, among them the campaign's own `k4/sdc/oc1_max_orders.py`.
    - The mechanism is a starved agent with exactly four goods.
    - Two rounds repair both starts, and MD holds.
- **Tools.** Lemma RC (one round) and Lemma RC2 (two rounds) turn reachability into a condition on where the picks lie
  in the final allocation. `rnd.c` enumerates every EFX allocation and decides both, in milliseconds at n = 4. Both
  are cross-checked against forward simulations, by exact counts for two rounds.

| statement (strictly positive values, every SD start) | n = 3 | n = 4 | n = 5 | instance | checks |
|---|---|---|---|---|---|
| picks extend (free) | fails | fails | fails | | |
| one chain (OC₁, t ≥ 0) then one absorber | holds (data; kgen-n3) | **fails** (kgen n = 4 lifted, m = 8) | **fails** (PW5 lifted) | `named.log` | rnd.c, ocsat |
| **ROUND⁺: one round of disjoint chains** (free = one absorber at n ≤ 5, Lemma RC (c)) | holds (data) | **FAILS** (RD5⁺, m = 7; two types, m = 7) | **FAILS** (m = 8, 9) | §3 | rnd.c, bruter.py, ocsat/ocseq; certificate script |
| ROUND-X: one round, starts draw from a common pool of released picks | holds | **FAILS** (X4, m = 7) | holds (data) | §4.2 | rnd.c, bruter.py (pooled) |
| ROUND-P: one round, every chain agent draws from the pool | holds | holds (data) | holds (data) | §4.2 | rnd.c, bruter.py (pooled) |
| **RD²⁺: two rounds** | holds | holds (data, every failure; climbs bottom out at one two-round witness) | holds (data) | §4.1 | ocseq, bruter.py two rounds, rnd.c Lemma RC2 |
| MD (some EFX allocation value-dominates the picks) | holds | holds | holds | | rnd.c |
| *k = 4 with zeros, perfect starts:* OC₁ and one round, non-core instances | | **FAIL** (W4: a worthless good; K4W: none, a top-heavy agent) | | §4.3 | k4/sdc pipeline, ocsat, brute force |
| *k = 4 with zeros:* **OC₁^max on strict connected cores (K4.SDC.OC1MAX)** | | **FAILS** (C4K, m = 7) | | §4.4 | `k4/sdc/oc1_max_orders.py`, k4/sdc pipeline, ocsat, brute force |
| *k = 4 with zeros:* two rounds on C4K, W4, K4W | | holds | | §4.3, §4.4 | brute force |

## 1. Definitions and the round characterization

*Setting.*
- n agents, m ≥ n goods, values v_i(g) > 0 for every agent and good (so EFX₀ = EFX), additive.
- An order π gives serial-dictatorship picks y (each agent in turn takes its favourite remaining good, ties to the
  smaller index). Every agent gets a pick. J = M ∖ {y_a} is the junk. Every junk good is worth at most v_a(y_a) to
  every agent a (it was available at a's turn).
- **Chain** (`k4/sdc.md` §29). Distinct agents x₀, …, x_t (t ≥ 0) with disjoint sets H_i.
  - x₀ takes H₀ ⊆ J ∪ B_{x_t} (for t = 0: H₀ ⊆ J, added to its base).
  - x_i takes B_{x_{i−1}} ∪ H_i with H_i ⊆ J.
  - Every chain agent strictly gains; the rest of B_{x_t} becomes junk.
- **Round** (`k4/ksens.md` §6). Vertex-disjoint chains applied at once, their H sets pairwise disjoint. Each start
  takes goods of its own chain's end only.
- **Completion.** A complete EFX allocation containing every base: free, or with one absorber (at most one agent
  holds two or more goods outside its base).
- **ROUND⁺** (the coordinator's conjecture). For every positive instance and every order, the picks have a completion
  after at most one round. *RD^c⁺* is the same with c sequential rounds.

**Lemma RC (the round characterization at positive values; written proof, used by `rnd.c`).** Fix the start y and a
complete allocation X. Let loc(a) be the agent whose bundle contains y_a, and Mv = {a : loc(a) ≠ a} the movers.
- (a) X is a free completion of the bases after some round iff some set P ⊆ Mv (the passers, with successor
  s(a) = loc(a)) satisfies all of:
  1. s is injective on P and has no cycle;
  2. every a ∈ Mv ∖ P has a predecessor (some p ∈ P with s(p) = a);
  3. every agent b with a predecessor p has v_b(y_p) + v_b(X_b ∩ J) > v_b(y_b);
  4. every start x (in P, with no predecessor), whose path ends at e, has
     v_x(X_x ∩ J) + [loc(e) = x]·v_x(y_e) > v_x(y_x).
- (b) X is a one-absorber completion after some round iff, in addition, at most one agent holds two or more
  *released picks*: the y_e of path ends e with loc(e) ≠ the start of e's path.
- (c) At n ≤ 5 there are at most two paths, hence at most two released picks, so the free and one-absorber forms of
  one round coincide.

*Proof.*
- (⇒) Take a round and its completion X.
  - Off-chain agents and t = 0 starts keep their pick, so they are not movers.
  - A passer x_i (i < t) hands y_{x_i} to x_{i+1}, whose base lies in X_{x_{i+1}}. So x_i ∈ Mv and
    loc(x_i) = x_{i+1}. Let P be the set of passers.
  - A mover that does not pass lies on a chain, hence is an end x_t with predecessor x_{t−1}. This gives 1 and 2.
  - The receiver x_i's base is {y_{x_{i−1}}} ∪ H_i with H_i ⊆ J ∩ X_{x_i}. Values are positive, so the left side of 3
    is at least the base value, which exceeds v(y_{x_i}).
  - x₀'s set H₀ lies in (J ∪ {y_{x_t}}) ∩ X_{x₀}, which gives 4.
  - For (b): a released pick y_e lies in no base. Receivers' sets H lie in J; another chain's start takes only its own
    end's base; an off-chain agent's base is its pick plus junk. So every released pick is outside its holder's base.
- (⇐) The paths of s are chains x₀ → … → x_t with t ≥ 1. Put H_i = X_{x_i} ∩ J and H₀ = X_{x₀} ∩ (J ∪ {y_{x_t}}).
  - The sets are disjoint, since they lie in different bundles.
  - Every new base lies inside its holder's bundle (y_{x_{i−1}} has loc = x_i).
  - The gains are 3 and 4.
  - An agent on no path is not a mover, by 2, so it keeps {y_a} ⊆ X_a.
  - For (b), every off-chain agent holding junk also makes a t = 0 move with H₀ = X_a ∩ J, which gains by positivity.
    Then the goods outside bases are exactly the released picks.
- (c) Each path has at least two agents. ∎

`rnd.c` enumerates every complete EFX allocation (pruned DFS on the raw definition) and decides (a) and (b) by
enumerating the ends among the movers (at most 2^n choices).

**Lemma R1 (MD and one foreign pick).** Every allocation X reached by one round from the picks satisfies:
- v_i(X_i) ≥ v_i(y_i) for every i, strictly when y_i ∉ X_i;
- every base contains at most one pick of another agent: receivers get one passed pick, a start one end pick, an
  off-chain or t = 0 agent its own.

**Corollary (starved-agent certificate).** Call an agent a *starved* in X if y_a ∉ X_a and
max over f ∈ (X_a ∩ foreign picks) ∪ {none} of v_a({f} ∪ (X_a ∩ J)) ≤ v_a(y_a). If every EFX allocation that
value-dominates the picks has a starved agent, no round from the picks has a completion.
- *Proof.* By Lemma R1 a reachable X is MD. The starved agent a lost its pick, so it lay on a chain with t ≥ 1, and
  its base (at most one foreign pick plus junk, inside X_a) beats y_a. That contradicts starvation. ∎

## 2. Tools and cross-checks

| tool | what |
|---|---|
| `kgen/rounds/rnd.c` + `rndlib.py` | every EFX allocation by pruned DFS (raw definition); per start: picks extend (free / one absorber), OC₁ (one chain t ≥ 0), one round (free / one absorber, Lemma RC), ROUND-X, ROUND-P, MD; witness counts and witness margins |
| `kgen/rounds/bruter.py` | independent forward simulation from the definitions: every round (every chain set, every choice of H sets), then every completion; two rounds; pooled rounds (ROUND-X/P) |
| ksens `ocsat.py`, `ocseq.py` (SAT) | one round (`multi=True`), c rounds |
| `kgen/rounds/n3shapes.py` | third implementation of the n = 3 shapes (keep / hand-off / swap / 3-chain / rotation), cross-checked against rnd.c's count on every start |
| `kgen/rounds/refute_roundplus.py` | self-contained pure-Python check of the refutations: raw enumeration of all n^m allocations, MD, the starved-agent certificate, an explicit two-round repair |
| `kgen/rounds/stress.py` | random families and adversarial climbs |
| `kgen/rounds/climb2.py` | climbs toward starts needing three rounds (rnd.c, then ocseq counts of two-round completions; slow, superseded) |
| `rnd.c` `rnd2_count`, `rnd2_count_margin` | two rounds, Lemma RC2: exact count and margins of the allocations reachable by ≤ 2 rounds |
| `kgen/rounds/climb3.py` | climbs toward three rounds with the exact two-round count (MARGIN2, PHASED) |
| `kgen/rounds/xcheck.py`, `xcheck_x.py`, `xcheck2.py` | cross-checks: rnd.c against bruter.py and ocsat; ROUND-X/P; two-round counts |
| `kgen/rounds/mechanism.py` | starved-agent certificate on every failure |
| `kgen/rounds/shrink.py` | good deletion on the failures |
| `kgen/rounds/n3shapes.py`, `n3roles.py` | n = 3 shapes and repair positions |
| `kgen/rounds/verify_k4zero.py`, `k4zero_scan.py`, `k4w_check.py`, `zero_version.py` | k-limited instances with zeros: k4/sdc's pipeline, ocsat and a brute force |

Cross-checks, 0 mismatches:
- rnd.c against bruter.py: 1,048 starts, n = 3, 4, m ≤ 7 (`xcheck_brute_150_1.log`);
- rnd.c against ocsat (EXTF, EXT1, OC1, RNDF, RND1, MD) on the 101 starts of the named instances, including the starts
  where one chain fails (`xcheck_known.log`);
- ROUND-X and ROUND-P against bruter's pooled forward simulation (`xcheck_x_60_3.log`, `xcheck_xp_40_4.log`);
- n3shapes against rnd.c on every n = 3 start classified.

## 3. ROUND⁺ is false

### 3.1 RD5⁺ (n = 4, m = 7)
Values ×100 of RD5 (`k4/ksens.md` §6), with agent 0's value of good 4 lowered from 24 to 23 and every zero replaced by
ε (any ε from 1 to 99 works):

| agent | g0 | g1 | g2 | g3 | g4 | g5 | g6 |
|---|---|---|---|---|---|---|---|
| 0 | 2600 | 5700 | ε | 4400 | **2300** | 3300 | ε |
| 1 | ε | 1200 | 1100 | 600 | ε | ε | ε |
| 2 | ε | 900 | 800 | 600 | 100 | ε | ε |
| 3 | 3600 | ε | 5300 | ε | ε | 4700 | 400 |

- *Order (0, 3, 1, 2).* Picks: agent 0 takes 1, agent 3 takes 2, agent 1 takes 3, agent 2 takes 4. The junk is
  {0, 5, 6}.
- *Claim.* No round of vertex-disjoint chains from these picks has a completion, free or with one absorber. The other
  9 distinct starts of the instance need at most one round.
- *Proof* (ε = 1; the finite part is checked by `refute_roundplus.py`, `refute_roundplus.log`).
  - The instance has 26 EFX allocations. Six of them value-dominate the picks, and in all six agent 0 holds {3, 4}
    (plus possibly good 6), agent 3 holds {0, 5}, and agents 1 and 2 hold picks 1 and 2.
  - So agent 0 lost its pick and holds the picks of agents 1 and 2. With one of them plus its junk (good 6 at most),
    its base is worth at most 4400 + ε < 5700 = v₀(y₀). Agent 0 is starved in all six, and the Corollary of §1
    applies. ∎
- *Why the value 24 hides it.* With v₀(4) = 24 we get v₀({4, 5}) = v₀(1), a tie. A ring through agent 2 then repairs
  agent 0 with {4, 5} at equality plus ε, and the lifted RD5 of `k4/ksens.md` §8 needs one round. Any lower value
  breaks this (`v0(4)= 2399 fails`, scan in §3.4).
- *Two rounds repair it.* In round 1, agent 3 passes its pick 2 to agent 1 and takes the junk pair {0, 5}, releasing
  agent 1's pick 3; agent 0 adds junk 6 (a t = 0 move). In round 2, a ring: agent 2 takes 1 from agent 0's base
  {1, 6}, and agent 0 takes agent 2's pick 4 plus the released 3. The completion gives 6 back to agent 0:
  ({3, 4, 6}, {2}, {1}, {0, 5}), which is EFX.
- *Checks* (`verify_fail_first.log`, `refute_roundplus.log`): rnd.c, bruter.py (forward, every round) and ocsat
  (SAT, `multi=True`) agree that one round fails; ocseq and bruter.py agree that two rounds suffice.

### 3.2 The other failures (all confirmed by the three programs; all repaired by two rounds)
- **C4G** (n = 4, m = 7; climb from GM4-G lifted):
  - values [[304,35,1,2864,610,2535,950], [432,643,29,1067,71,2469,764], [90,582,165,1265,981,2483,1970],
    [434,642,29,1068,69,2467,764]];
  - order (2, 1, 3, 0), picks (4, 3, 5, 6). Agent 2 is starved in all 8 MD allocations: it needs agent 0's and agent
    3's picks.
- **n = 5:** C5a (m = 8, climb from the PW-like family; agent 0 starved in all 20 MD allocations), and seven n = 5,
  m = 9 starts from climbs seeded at PW5 lifted (`verify_fail_first.log`, `fails.jsonl`).
- **n = 4, m = 8 and 9:** found by campaign 3 (`c3_rnd1_*.log`, `fails.jsonl`).
- Every failure found has a starved agent in every MD allocation: the certificate is checked on C4G and C5a by
  `refute_roundplus.py` (raw enumeration), and on all 61 distinct failing starts of `fails.jsonl` and
  `fails_twins.jsonl` by `mechanism.py` (`mechanism.log`): every MD allocation of every failure has a starved agent.

### 3.3 Two valuation types (n = 4, m = 7)
- *Instance:* agents 0 and 1 have values (144, 1429, 2963, 2918, 1039, 1633, 2640); agents 2 and 3 have values
  (173, 23, 8993, 6979, 1816, 929, 2941).
- *Order (0, 1, 2, 3):* picks (2, 3, 6, 4), junk {0, 1, 5}.
- *Mechanism:* in all 8 MD allocations a type-A agent holds {4, 6}, the picks of both type-B agents, and the type-B
  agents hold the type-A agents' picks 2 and 3. One foreign pick plus junk is worth at most 2640 < 2963 (or < 2918).
- *Checks:* three programs; two rounds suffice (`verify_fail_twotypes.log`).
- Twin climbs (`twins*.log`) found 12 such starts with one or two identical pairs, m = 7–9.
- *Consequence.* EFX is known for two types (Mahara [unverified]; the literature report) and, with one identical pair,
  three types (Prakash HV–Ghosal–Nimbhorkar–Varma, EC 2025 [unverified]). So ROUND⁺ is not a reformulation of EFX
  existence; it is a genuinely stronger structural claim, false already where existence is easy.

### 3.4 How the failures were found
- *Random sampling found none.* n = 4: 16,800 profiles, 110,102 starts, m = 6–12 (`rand_n4_*.log`). n = 5: 2,400
  profiles, 66,936 starts, m = 6–10 (`rand_n5_*.log`). Across twelve families: generic, small integers with ties,
  identical, near-identical, two and three types, distinct tops, PW-like, big/small, lexicographic, correlated, pairs.
- *Climbs found them* (`stress.py climb`), minimizing at the hardest start:
  1. the number of EFX allocations that witness one round;
  2. then the sum of their margins: the smaller of the EFX slack and the best structure's gain slack, normalized by the
     agent's total value.

  The margin term matters. Counts alone plateau at one witness, the "keep every pick, one agent absorbs" allocation.
- *Seeds.* Failures come fastest from seeds near known obstructions: GM4 lifted, RD5 lifted, PW5 lifted, the PW-like
  family. ksens's climbs (`general_rounds_climb_*`) used counts of rounds only and found none.

## 4. What survives

### 4.1 Two rounds (RD²⁺)
- Every one-round failure found is repaired by two rounds with one absorber (ocseq `multi=True`; `climb2.py` evaluates
  every failing start). The failures are those of `fails.jsonl`, `fails_twins.jsonl` and `fails_keps.jsonl`. On every
  failure checked by `rndlib.two_rounds`, *every* MD allocation is reachable in two rounds.
- **Lemma RC2 (two rounds, free completion, positive values; used by `rnd.c`'s `rnd2_count`).** X is reachable by at
  most two rounds iff some round-1 data and some round-2 roles satisfy the conditions below.
  - *Round-1 data:* a structure (each agent OFF, a t = 0 agent, or on a path, with a ring flag per path) and an
    assignment of the junk to round-1 chain agents. Every round-1 chain agent strictly gains.
  - *Round-2 roles:* each agent's round-1 base B¹_a either
    - stays inside X_a, or
    - passes whole to the agent whose bundle contains it, or
    - is split (the agent is then a round-2 end with a predecessor; its start takes X_{x₀} ∩ B¹_a and the rest is
      released).
  - *Conditions:* the passers form disjoint acyclic paths, and the gains of Lemma RC hold with sets and with the
    round-1 junk J¹ = (J − H¹) + released picks:
    - receiver b with predecessor p: v_b(B¹_p) + v_b(X_b ∩ J¹) > v_b(B¹_b);
    - start x with end e: v_x(X_x ∩ J¹) + v_x(X_x ∩ B¹_e) > v_x(B¹_x).
  - *Proof.* The round-2 sets H can be taken maximal, as in Lemma RC, because nothing moves after round 2. A round-1
    junk good taken by an agent that does not split must end in the bundle its base moves to. ∎
- *Cross-check.* `xcheck2.py` compares the exact number of complete EFX allocations reachable by at most two rounds
  (and by one) with a forward simulation (bruter.py's rounds applied twice, every completion enumerated).
  - 0 mismatches on 157 + 502 starts, n ≤ 4, m ≤ 7 (`xcheck2_80_2_4_7.log`).
  - Those starts include 106 where some MD allocation is not reachable in two rounds, and 157 where two rounds reach
    more than one.
- *Climbs toward three rounds.*
  - `climb3.py` uses the exact two-round count, which is fast: milliseconds at n = 4, about 1 s at n = 5, m = 9. It is
    seeded from every failure and from random families (`c4_3r_*.log`).
  - The earlier SAT climbs (`climb2.py`, ocseq counts) were too slow and were stopped.
  - Every climb bottoms out at exactly **one** two-round-reachable EFX allocation at the hardest start, never zero.
  - It is the same "last witness never dies" plateau as the one-round climbs had before the margin term exposed
    failures.
  - `climb3.py` with MARGIN2=1 and PHASED=1 therefore minimizes two-round witnesses and their margins over the
    one-round failures only (`rnd2_count_margin`: the best structure's smallest gain slack, and the EFX slack). It
    is in `c5_3r_*.log`, with no start needing three rounds.
- *Why depth is hard to build.* A three-round need requires a starved agent one of whose needed picks belongs to
  another starved agent. A sketch at n = 5 shows that one round-2 chain can still collect both: the start takes the
  inner starved agent's pick as its end's pick, plus a pick released in round 1. That agrees with ksens's estimate
  (n ≥ 6) for the zero-value case.
- RD²⁺ for all n would contain additive EFX existence.

### 4.2 One-step repairs of the mechanism
- **ROUND-X.** As a round, but every chain start may take, besides junk, the released pick of *any* chain end (a
  common pool).
  - It repairs every ROUND⁺ failure but one: X4, n = 4, m = 7, values [[1,642,31,987,363,2866,764],
    [136,705,266,1148,475,2515,985], [146,133,242,1670,1,2701,633], [245,119,75,2148,140,2806,653]], order
    (3, 1, 0, 2).
  - In X4's three MD allocations, agent 1 holds the picks of agents 0 and 2 and is the *middle* agent of the only
    possible chain 0 → 1 → 2, so it cannot draw from the pool.
  - Checked by rnd.c and bruter.py's pooled forward simulation. Two rounds repair it.
- **ROUND-P.** Every chain agent may draw from the pool. No failure found.
  - On the failures its witness count equals the MD count in most cases.
  - It excludes only one MD configuration: two agents that hold no pick and whose picks lie in the same bundle (both
    would have to be passers into one agent).
  - So ROUND-P is close to MD and says little beyond it.

### 4.3 k-limited instances: ε-lifts and zeros (bears on the k = 4 campaign)
- *ε-lifts of k-limited instances.* `stress.py` with KEPS=k: every agent keeps at most k values above 5, and the rest
  are clamped to 1..5.
  - One round fails at KEPS = 4 (n = 4, m = 7–9; n = 5, m = 8; `keps4_*.log`, `fails_keps.jsonl`), always by
    starvation (`mechanism_keps.log`).
- **The zero versions** (every value ≤ 5 set to 0) are genuine k = 4 instances with zeros: exactly four relevant goods
  per agent, and every agent picks (perfect starts).
  - Of the 11 distinct ε-failures, the zero versions of **10** fail OC₁ (one chain or ring, one absorber) and one
    round of disjoint chains (free and one absorber), and two rounds repair them. The 11th (n = 5) satisfies OC₁.
  - Three programs agree (`zero_version_keps.log`, `k4zero_scan_keps.log`, `verify_k4zero_W4.log`): ksens ocsat,
    k4/sdc's own OC₁ pipeline (Enc, de_free.moves with rings, oc_absorb.extends_A), and the brute force of
    `verify_k4zero.py`.
  - **Each of the 10 contains a good valued by nobody.** Deleting the worthless goods restores OC₁ and one round, in
    both programs.
- *Instance W4* (n = 4, m = 7, k = 4; good 3 is valued by nobody):
  - values [[7114,0,7069,0,0,6267,3000], [9160,0,8502,0,0,3000,2986], [0,1391,6792,0,5427,6130,0],
    [0,5425,6790,0,1390,6129,0]];
  - order (0, 2, 3, 1), picks (0, 6, 2, 5) for agents 0–3.
- *Consequences for the campaign* (sent to the coordinator).
  - OC₁ and RD (ksens) at perfect starts are false at k = 4 when worthless goods are allowed.
  - Lemma RED's target, "OC₁ at perfect starts for every instance with ≤ 4 relevant goods", needs the hypothesis
    "every good is valued by someone". It holds for RED's reduced instance I′ whenever I is a core, and L3 provides it
    in general.
  - OC₁^max on strict cores is untouched: cores have no worthless goods.
- **K4W: a worthless-free k = 4 failure.** Found with KEPS = 4 and KCOVER = 1, where every good is a real good of some
  agent (`kcover4_*.log`, `fails_kcover.jsonl`).

  | agent | relevant goods (value) |
  |---|---|
  | 0 | g1 2613, g4 1453, g5 1599, g6 1597 |
  | 1 | g1 2615, g4 1474, g5 1599, g6 1596 |
  | 2 | g0 1929, g1 984, g2 22, g5 543 (top-heavy: 1929 ≥ 1549) |
  | 3 | g0 2334, g2 2265, g3 49, g5 897 |

  - n = 4, m = 7, k = 4. Every agent has four relevant goods, subset sums are strict, the instance is connected, and
    every good is valued.
  - *Starts.* Orders (0, 1, 3, 2) and (1, 0, 3, 2) give the perfect starts (1, 5, 2, 0) and (5, 1, 2, 0).
  - *Result.* From both, OC₁ (one chain or ring, one absorber) and one round (free or one absorber) fail. Two rounds
    repair both, and MD holds. The other 6 distinct starts satisfy OC₁.
  - *Checks.* Three programs agree on every order (`k4w_check.py`, `k4w_check.log`).
  - *Mechanism.*
    - There are 26 EFX₀ allocations, and 6 of them value-dominate the picks. In all six, agent 3 gives its pick g0 to
      the top-heavy agent 2, whose own pick g2 is worth 22 to it, and holds both foreign picks {2, 5}.
    - Agent 3's best one-round base is g2 + g3 = 2314 < 2334: it is starved.
    - If agent 3 kept g0 together with any other good, agent 2 would envy that bundle (EFX₀ requires v₂(X₂) ≥ 1929).
    - The starved agent uses exactly four goods: its pick, two foreign picks and one junk good. So ksens's five-good
      count for RD5, which comes from a frozen agent's danger pool, does not bound this mechanism: here the freezing
      comes from a top-heavy agent.
  - *Scope.*
    - K4W is not a core: agent 2 is top-heavy, and R1 would peel it with g0. Lemma P (`kgen/n3.md` §2) does not apply,
      because agent 2's pick is not its top.
    - So K4W refutes OC₁ and RD at perfect starts for non-core k ≤ 4 instances, even with every good valued. That
      includes the LOOSE form of OC₁^max and the target of Lemma RED's route, whose reduced instance I′ need not be a
      core.
    - It does not refute OC₁^max on cores.
- *Core-constrained ε-lift climbs* (KEPS = 4, KCORE = 1: the zero version satisfies K4.CORE of `k4/SCOUT.md`, without
  connectivity; `kcore4_*.log`). No one-round failure. The climbs bottom out at exactly one witness, consistent with
  the campaign's OC₁^max evidence.
  - One ε-failure was found among them (n = 5, m = 8, `fails_kcore.jsonl`). Its zero version satisfies OC₁ and one
    round from the same order, in both programs (`k4zero_scan_kcore.log`). So the ε values themselves caused the
    failure there.
- *Caveat.* rnd.c tests the ε-lift, not the zero version. In every ε-failure the zero version failed too, but a
  zero-version failure with a repairable ε-lift would be missed.

### 4.4 OC₁^max is false: the core C4K (n = 4, m = 7)
Found by the core-constrained ε-lift climbs: KEPS = 4, KCORE = 1, `fails_kcore.jsonl`, `k4zero_scan_kcore.log`. Of
their four ε-failures, two zero versions satisfy OC₁. The other two are the two failing starts of the core below.

| agent | relevant goods (value) |
|---|---|
| 0 | g1 2030, g4 1714, g5 1395, g6 1806 |
| 1 | g1 2461, g4 1674, g5 1357, g6 1802 |
| 2 | g0 1025, g2 35, g3 818, g6 934 |
| 3 | g0 1090, g1 901, g3 154, g6 517 |

- *A strict connected k = 4 core* (`c4k_core.py`, `c4k_core.log`; the logic is the core claim of
  `k4/gm4_counterexample.py`):
  - every agent has four relevant goods and is strictly balanced;
  - all subset sums are distinct;
  - the one private good is g2;
  - every good is valued, and the instance is connected;
  - ν = 4.
- *Failing starts.* Orders (0, 1, 2, 3) and (1, 0, 2, 3), with picks (1, 6, 0, 3) and (6, 1, 0, 3); 6 of the 24
  orders give one of them. These are perfect starts, so maximum-matching starts.
- *Result.* From both starts there is no one-absorber EFX₀ completion at the picks or after any addition, chain or
  ring. One round of disjoint chains fails too. Two rounds repair both, and MD holds.
- *Checks.* Four programs agree:
  - `k4/sdc/oc1_max_orders.py` on `c4k.json` (`c4k_oc1_max_orders.log`: 6 maximum-matching orders fail);
  - k4/sdc's pipeline, ksens's ocsat and the brute force (`c4k_check.log`).
- *Mechanism* (`c4k_mechanism.log`).
  - There are 10 EFX₀ allocations, 6 of them MD.
  - In each, agent 3 takes agent 2's pick g0 (1090 against its own pick's 154), and agent 2 holds both foreign picks
    g3 and g6 (1752 > 1025).
  - One move gives agent 2's base at most one of them, worth at most 934 + 35 = 969 < 1025: agent 2 is starved
    (§1, Corollary).
  - The starved agent uses exactly k = 4 goods: its pick, two foreign picks and one junk good.
- *Write-up:* `attempts/kgen-rounds-oc1max-c4k.md`.
- *What it leaves.* Two rounds (RD² at k = 4), MD and SD-C. On C4K, 18 of the 24 orders satisfy OC₁. The natural
  repair of OC₁ is a move that lets one agent collect two picks: two sequential chains, or a pooled round where
  middle agents draw from the pool (ROUND-P).

## 5. n = 3

### 5.1 One round survives
- At n = 3 a round has at most one chain with t ≥ 1 (Lemma RC), and the free and one-absorber forms coincide.
- OC₁(t ≥ 0) implies one round. So every n = 3 datum of `kgen/n3.md` §3 supports ROUND⁺₃. That includes the
  exhaustive grids with values in {0, …, 3}, m = 5, which contain all positive profiles with values in {1, 2, 3}.
- Here: random families (`n3shapes_rand_150_7_5_10.log`, 4,729 starts) and 170 climbs with m = 6–10
  (`climb_n3m*.log`). No failure. Climbs bottom out at exactly one witness.
- By Proposition H of `kgen/n3.md` §10, a proof of ROUND⁺₃ would be a new proof of three-agent EFX (CGM), since one
  round from any order produces an EFX allocation.

### 5.2 Which shape a start needs (`n3shapes.py`)
Shapes:
- K: keep;
- H: hand-off x₀ → x₁, x₁'s pick released;
- S: swap, a 2-ring;
- P3: chain x₀ → x₁ → x₂, released;
- R3: rotation, a 3-ring.

| data | starts | K | H and S | S only | H only | 3-agent only |
|---|---|---|---|---|---|---|
| random, twelve families, m = 5–10 | 4,729 | 4,500 | 180 | 26 | 22 | 1 (R3 only) |
| climbed (170 climbs, m = 6–10) | 854 | 638 | 137 | 79 | 0 | 0 |

- No two-agent shape suffices alone: "S only" and "H only" both occur.
- **A rotation is sometimes necessary** (instance ROT3, verified by bruter.py's forward simulation restricted to chains
  of at most two agents: 0 of 117 states complete, against 159 of 300 with three-agent chains):
  - values [[2,42,584,29,58,1,44], [22,37,9,46,527,19,511], [15,21,593,58,860,45,9]], order (1, 2, 0);
  - picks: agent 0 takes 6, agent 1 takes 4, agent 2 takes 2;
  - a witness: ({2}, {0, 1, 6}, {4, 5}). The picks rotate 0 → 1 → 2 → 0, and agents 1 and 2 also take junk.
- The chain-with-release P3 was never needed alone.

**Who repairs, by order position** (`n3roles.py`; position 0 = first picker, 2 = last). Hard starts are those whose
picks do not extend: 330 in 3,000 random profiles with m = 6–10 (`n3roles_rand_3000_11_6_10.log`), and 216 in the
climbs (`n3roles_climbed.log`).

| cover | random: misses | climbed: misses |
|---|---|---|
| a two-agent move into the last picker: H(0→2), H(1→2), S{0,2}, S{1,2} | 10 of 330 | 0 of 216 |
| any two-agent move with the last picker, also H(2→·) | 7 | 0 |
| **any two-agent move** (hand-off or swap) | **0** | **0** |
| a move into the last picker, or a rotation | 1 | 0 |

- The last picker almost never starts the chain: H(2→0) repairs 6 of 330 starts and H(2→1) 2 of 330.
- The most frequent repairs are the swap of the first and last pickers S{0,2} (293 of 330), H(1→2) (291) and
  H(0→2) (285).
- The repair is not determined by positions. Every single pattern fails somewhere, and examples needing only S{1,2}
  or only S{0,2} are in the logs.
- The rotation is needed only on ROT3-like starts (one in 4,729 random starts in the run of the table above, none in
  the 330 here).

**Lemma ID (identical valuations; written proof, any n).** If all agents have the same additive valuation (zeros
allowed), the picks of every order extend to a complete EFX₀ allocation. No chain is needed.
- *Proof.*
  - The k-th agent of the order picks the k-th good g_k of the decreasing order (ties by index).
  - Run LPT along that order: each good goes to a bundle of currently smallest value. With positive values the first
    n goods go to distinct bundles; give each bundle to the agent whose pick it holds. With zeros, ties are broken
    toward empty bundles, which does the same.
  - For a bundle Z with at least two goods, let h be its last good. Then h is the smallest good of Z, and when h was
    added, Z ∖ h was a smallest bundle. Bundles only grow, so v(Z) − min(Z) = v(Z ∖ h) ≤ v(W) for every bundle W.
    The valuations are identical, so this is EFX₀ for every agent. ∎
- Checked on 15,684 starts, n = 3–5, generic and small-integer values with ties: the picks extend on all of them.
- So the two-type failure of §3.3 is as close to identical as a failure can be: two types, two agents each.

### 5.3 Starvation at n = 3 (partial)
- At n = 3 a starved agent a must hold y_b and y_c. Then b and c both lost their picks, and one of them, say b, holds
  no pick at all (X_b ⊆ J), because y_a is in only one bundle.
- The only round structure placing y_b and y_c with a is the path b → a → c with y_c released into X_a, which needs
  y_a ∈ X_c. Its gain at a is v_a(y_b) + v_a(X_a ∩ J) > v_a(y_a).
  - *Why this is the only structure.* b holds no pick, so it has no predecessor and must pass, to a. Then c cannot
    also pass to a, so c is an end, whose predecessor must be a.
- If that gain fails, X is unreachable. On all data at n = 3 another MD allocation is then reachable: no start was
  found at which every MD allocation is starved.
- A proof would have to construct that allocation, which is the three-agent existence problem again. Not proved.

## 6. Proposed ledger rows (for the coordinator; LEDGER.md is not edited on this branch)

| ID | Claim | Status | Artifact |
|---|---|---|---|
| KGEN.ROUND+ | ROUND⁺: with strictly positive additive values, from every SD order one round of vertex-disjoint improving chains reaches bases with a complete EFX completion | REFUTED | `kgen/rounds/refute_roundplus.py`, `results/kgen_rounds/refute_roundplus.log`, `results/kgen_rounds/verify_fail_first.log`, `attempts/kgen-rounds-one-round.md` |
| KGEN.ROUNDX | ROUND-X: the same with chain starts drawing from a common pool of released end picks | REFUTED | `results/kgen_rounds/xcheck_xp_40_4.log` (X4, rnd.c and bruter.py), `kgen/rounds.md` §4.2 |
| KGEN.RC | Lemmas RC, RC2 and R1 (round characterizations at positive values; at most one foreign pick per base after one round) | PROVED | `kgen/rounds.md` §1, §4.1 (written proofs, not refereed; RC/RC2 cross-checked against forward simulations, `xcheck_*.log`) |
| KGEN.RD2+ | RD²⁺: two rounds suffice at positive values | CONJECTURE | EVIDENCE only: every one-round failure (138 starts found), climbs (`c4_3r_*.log`, `c5_3r_*.log`) |
| KGEN.ROUND3 | ROUND⁺ at n = 3 | CONJECTURE | EVIDENCE only (§5.1); a proof would reprove CGM |
| KGEN.ID | Identical valuations: the picks of every order extend (any n, zeros allowed) | PROVED | `kgen/rounds.md` §5.2 (written proof; checked on 15,684 starts) |
| K4.SDC.OC1MAX | (existing row) OC₁^max on strict connected k = 4 cores | CONJECTURE → **REFUTED** | `attempts/kgen-rounds-oc1max-c4k.md`, `kgen/rounds/c4k_core.py`, `results/kgen_rounds/c4k.json`, `results/kgen_rounds/c4k_oc1_max_orders.log`, `results/kgen_rounds/c4k_check.log`, `results/kgen_rounds/c4k_mechanism.log` |
| K4.SDC.OC1PERF | OC₁ (and one round) at perfect starts for every instance with ≤ 4 relevant goods per agent (the target of Lemma RED's route; the LOOSE form of OC₁^max) | REFUTED | `kgen/rounds/k4w_check.py`, `results/kgen_rounds/k4w_check.log` (K4W, no worthless good), `results/kgen_rounds/verify_k4zero_W4.log` (W4) |

## 7. Next
- RD²⁺:
  - at n = 6 the two-round checker needs a larger round-1 structure table (MAXS1);
  - the depth-two design of §4.1 at n = 6.
- Whether K4W's configuration can appear in Lemma RED's I′ of a core. Climbs on the I′ shape: agents with three goods
  may be top-heavy, four-good agents are balanced (`iprime_*.log`).
- Turn the starved-agent certificate into the obstruction statement it suggests: "some MD allocation has no starved
  agent" is ROUND-P-like and contains EFX existence; what does k ≤ 4 add?
