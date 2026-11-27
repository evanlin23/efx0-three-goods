# Rounds of disjoint chains at positive values (workstream `proof/kgen-rounds`)

Branch `proof/kgen-rounds`, draft PR #111. Code `kgen/rounds/`, logs `results/kgen_rounds/`. Coordinator's record:
`k4/attack_log.md` on `claude/kind-lamport-y8fdme`. Builds on `k4/ksens.md` §6–§8 (branch `claude/k4-ksens`, read
there at 63089336), `k4/sdc.md` §29–§31, `kgen/n3.md` (branch `claude/kgen-n3`) and
`reports/EFX literature from the agent side.md`. Random and climbed instances are evidence only (PROMPT.md §5 rule 3);
every refutation below is confirmed by three independent programs.

## Status (2026-11-27)

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
    LOOSE form of OC₁^max.
  - **OC₁^max (K4.SDC.OC1MAX) is false.** The certifier refuted it first, by exhaustive ordinal CEGAR over the
    n = 4 core hypergraphs: 11 of 1,002 fail (`results/k4_oc1max/oc1max_cex_n4.json` on `compute/k4-oc1max-cert`;
    ledger REFUTED since 23:14).
  - This workstream found it independently with **C4K**, a strict connected core with n = 4, m = 7 (§4.4), and 25
    more strict cores. All of them lie on the certifier's hypergraphs 2, 3 and 5 (`vs_certifier.log`), so they agree
    with the certifier's count. From the failing perfect starts, no addition, chain or ring has a one-absorber
    completion.
    - Four programs agree, among them the campaign's own `k4/sdc/oc1_max_orders.py`.
    - The mechanism is a starved agent with exactly four goods.
    - Two rounds repair both starts, and MD holds.
    - Direct climbs on cores with zeros found 30 failing instances (§4.5), 26 of them strict cores on three
      non-isomorphic n = 4, m = 7 hypergraphs.
  - **OC₁′** survives everything (§4.6): middle agents of the chain may also take the end's released goods.
    - It repairs every OC₁ failure found, including all 11 of the certifier's, and implies MD.
    - **At n = 4 it holds at all 112,880 OC₁^max-failing starts of the certifier's exhaustive search.** The certifier
      has since CERTIFIED OC₁′^max at n ≤ 4.
    - **It FAILS at n = 5** (the certifier, 24 starts; §4.8) by a second mechanism: two disjoint pick cycles, which
      one round of chains repairs.
    - So the one-step form that survives every k = 4 failure is **ROUND-P** (a pooled round, §4.8). OC₂^max and two
      rounds survive as well.
    - **§4.9 checks it directly**, with zeros, in the narrow form of the ledger row. Two implementations agree.
      - At all 112,880 of the certifier's OC₁^max-failing n = 4 starts, ROUND-P holds and one plain round fails.
      - At the certifier's n = 5 failures the plain round already holds.
      - It holds at every positive-value failure too.
      - Climbs on strict cores at n = 5, 6 have found no failure.
      - The only MD allocations it misses have an agent that keeps its own pick and also holds a pickless agent's
        pick.
    - It is a one-move alternative to the campaign's current target OC₂^max (two sequential moves).
    - On all 11 of the certifier's instances, every MD allocation has a starved agent, so the obstruction is the same
      k-independent one.
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
| *k = 4 with zeros:* **OC₁^max on strict connected cores (K4.SDC.OC1MAX)** | | **FAILS** (certifier: 11 hypergraphs; here C4K and 25 more, m = 7) | | §4.4 | `k4/sdc/oc1_max_orders.py`, k4/sdc pipeline, ocsat, brute force |
| *k = 4 with zeros:* two rounds on C4K, W4, K4W | | holds | | §4.3, §4.4 | brute force |
| *k = 4 with zeros:* **OC₁′^max** (middle chain agents may take the end's released goods) | | holds (certified by the certifier) | **fails** (the certifier's 24: two cycles) | §4.6, §4.8 | rnd.c, forward brute force |
| *k = 4 with zeros:* one plain round | | **fails** at all 112,880 OC₁^max-failing starts | holds at the certifier's 24 | §4.9 | rnd.c, forward `round_pool` |
| *k = 4 with zeros:* **ROUND-P^max** (narrow: non-end agents of chains with t ≥ 1 take any end's goods) | | holds (at all 112,880; follows from OC₁′^max) | holds (data: the 24, climbs) | §4.9 | rnd.c, forward `round_pool` |
| OC₁′ at k = 5 / at positive values | | **fails at positive values** (two disjoint swaps, m = 7, 8) | **fails** (PW5, zeros and lifted; m = 9 positive) | §4.6 | rnd.c, forward brute force |

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

**Evidence volume** (`summary.py`, `summary.log`; climb rounds of 1,500–5,000 steps each; all of it is evidence
only):

| climb family | climb rounds | distinct failing starts |
|---|---|---|
| ROUND⁺ at positive values (campaigns 1–3), n = 4, m = 7–12; n = 5, m = 8–10 | 880 | 59 |
| ROUND⁺ with one or two identical pairs | 296 | 22 |
| ROUND⁺ at n = 4, m = 5, 6 | 150 | 0 |
| ROUND-X | 203 | 2 |
| ε-lifts with KEPS = 4, 5 / every good covered / cores / I′ shape | 220 / 272 / 1,696 / 348 | 71 / 2 / 16 / 3 (ε) |
| k = 4 cores with zeros, OC₁ (zclimb) | 444 | 46 |
| k = 4 cores with zeros, OC₁′ (zclimb) | 286 | **0** |
| positive values, OC₁′ | 85 | 10 (two disjoint swaps) |
| three rounds (climb3, two variants) | 54 | **0** |

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
- *Two rounds repair it* (the form given by the referee, `k4/referee/rounds_r1.md` on `claude/k4-referee`).
  - Round 1: agent 3 passes its pick 2 to agent 1 and takes the junk pair {0, 5}, which releases agent 1's pick 3.
  - Round 2: the ring 0 → 2 → 0. Agent 2 receives agent 0's base {1} (900 > 100), and agent 0 takes agent 2's pick 4
    plus the released 3 (6700 > 5700).
  - The completion gives 6 to agent 0: ({3, 4, 6}, {2}, {1}, {0, 5}), which is EFX.
  - An earlier version of this note also added 6 to agent 0's base in round 1. It then let agent 2, as the *start* of
    a chain 2 → 0, take only {1} out of its end's base {1, 6}. §29 allows that (H₀ ⊆ J ∪ B_{x_t}), but the referee
    read agent 2 as a receiver, which must take the whole base. The plain ring above needs no such reading.
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
- *A literature instance.* Section 7 of Chaudhury–Garg–Mehlhorn–Mehta–Misra (arXiv 2103.01628) gives an n = 4, m = 9
  instance on which the three-agent approach stops (`cgmmm_instance.log`). Its values are [unverified]: they come from
  a web-fetch agent's summaries of the page, not from the paper text. On those values OC₁ holds at every start, with
  zeros and lifted, and one round suffices.
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
  - W4 itself says nothing about OC₁^max on strict cores (cores have no worthless goods), but OC₁^max is false
    there anyway (§4.4).
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
    - On its own it does not refute OC₁^max on cores (§4.4 does).
- *Core-constrained ε-lift climbs* (KEPS = 4, KCORE = 1: the zero version satisfies K4.CORE of `k4/SCOUT.md`, without
  connectivity; `kcore4_*.log`, `kcoreB_*.log`). Their ε-failures led to C4K (§4.4).
  - One ε-failure was found among them (n = 5, m = 8, `fails_kcore.jsonl`). Its zero version satisfies OC₁ and one
    round from the same order, in both programs (`k4zero_scan_kcore.log`). So the ε values themselves caused the
    failure there.
- *Caveat.* rnd.c tests the ε-lift, not the zero version. In every ε-failure the zero version failed too, but a
  zero-version failure with a repairable ε-lift would be missed.

### 4.4 OC₁^max is false: the core C4K (n = 4, m = 7)
*Priority.* The certifier found OC₁^max failures first, by exhaustive ordinal CEGAR on 11 of the 1,002 n = 4 core
hypergraphs (`compute/k4-oc1max-cert`). C4K's hypergraph is the certifier's instance 2, a different failing profile on
a known failing hypergraph. This section is an independent confirmation by a different method (climbs).

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

### 4.5 Direct climbs on k = 4 cores with zeros: more OC₁^max counterexamples
- *A zero-aware checker.* `rnd.c` `rnd_oc1z` tests OC₁ at perfect starts with zero values allowed, using the official
  move of `k4/sdc.md` §29/§31:
  - an addition, a chain or a ring;
  - junk sets inside the receiver's relevant goods, the start taking only end goods it values;
  - one absorber.

  Witnesses come from the EFX₀ enumeration and the analogue of Lemma RC.
  - *Cross-check* against k4/sdc's pipeline: 0 mismatches on 1,553 perfect starts, 102 of them failing OC₁
    (`xcheck_z.py`, `xcheck_z_300_5.log`).
- *Climbs.* `zclimb.py` climbs directly on strict connected k = 4 cores (K4.CORE plus connectivity), minimizing at the
  perfect starts the OC₁ witness count and margin (`zcore_*.log`). They found **30 distinct failing instances**
  (`fails_zcore.jsonl`, `zcore_fails.json`).
  - k4/sdc's own `oc1_max_orders.py` confirms a failing maximum-matching order on every one: 121 failing
    maximum-matching orders in all (`verify_zfails.log`).
  - **26 are strict connected cores with n = 4, m = 7, on three non-isomorphic hypergraphs** (`zcore_classes.log`):
    - C4K's, with 16 instances;
    - relevant sets {0,3,5,6}, {0,1,3,4}, {1,2,5,6}, {0,1,3,4}, with 9 instances;
    - relevant sets {0,2,3,5}, {0,2,4,5}, {1,3,4,6}, {0,1,3,4}, with 1 instance.
  - The other 4 are not strict (ties); two of them have n = 5, m = 9, 10.
- So C4K is not an isolated accident. OC₁^max fails on a positive fraction of the ε-climbable n = 4, m = 7 core space.
  Random sampling of profiles missed it because the failing profiles are rare.

### 4.6 OC₁′: a one-move repair that survives
- **OC₁′.** The move is OC₁'s single chain (or addition, or ring), except that every *non-end* agent of the chain may
  also take goods of the end's base that it values. The start already may (a ring); now a middle agent may too, on top
  of the base it receives. That base is released anyway.
  - Every chain agent strictly gains and the others keep their picks, so OC₁′ still implies MD.
  - With Lemma MAXSD and the core reduction, OC₁′^max (maximum-matching starts of strict connected k = 4 cores) would
    still imply TARGET₄.
  - OC₁′ is the single-chain case of ROUND-P (§4.2).
- *In C4K:* the chain 1 → 2 → 3. Agent 1 takes the junk {4, 5}; agent 2 receives agent 1's pick g6 and takes the
  released g3 plus the junk g2, 1787 > 1025; agent 3 receives g0.
- *Evidence.*
  - OC₁′ holds at every perfect start where OC₁ fails: 77 zero-version starts from the ε-lifts, and the 30 instances
    of §4.5, so C4K, K4W and W4 included (rnd.c and the forward brute force, `verify_zfails.log`).
  - Two implementations agree with 0 mismatches: rnd.c (`OC1P`) and a forward brute force written from the
    definition (`verify_k4zero.one_chain_prime`). They were compared on 984 perfect starts, 79 of them OC₁-false
    (`xcheck_oc1p.py`, `xcheck_oc1p_150_6.log`).
  - **The certifier's 11** (`vs_certifier.py`, `vs_certifier.log`): at every failing start, every MD allocation has a
    starved agent. OC₁′ holds, by rnd.c and by the forward brute force, and two rounds hold (brute force).
  - **Every OC₁^max-failing start at n = 4.** The certifier exports all 112,880 (type profile, picks) pairs on its 11
    hypergraphs where OC₁^max fails (`certifier_two_move_starts_n4.json.gz`, from `compute/k4-oc1max-cert`).
    - rnd.c reproduces every pick vector and agrees that OC₁ fails at all 112,880. **OC₁′ holds at all 112,880**
      (`oc1p_vs_oc2.py`, `oc1p_vs_oc2.log`).
    - **Second implementation:** the forward brute force (`verify_k4zero.oc1_prime`, no rnd.c) also finds OC₁′ at all
      112,880 (`oc1p_vs_oc2_forward.py`, `oc1p_vs_oc2_forward_0.log`, `oc1p_vs_oc2_forward_1.log`). It also checks
      that the certifier's picks are the SD picks of the listed order.
    - With the certifier's certification of OC₁^max on every other n = 4 start, this gives **OC₁′^max for every
      strict connected k = 4 core with n = 4**. It rests on the certifier's ordinal type reduction (OC₁′'s gains
      compare subset sums, so OC₁′ depends only on the types) and on this workstream's implementations.
  - Direct OC₁′ climbs on cores bottom out at one witness, with no failure: n = 4, m = 6–8; n = 5, m = 7–10; n = 6,
    m = 9–12; n = 7; seeded from all OC₁ failures (`oc1p_*.log`, `oc1pB_*.log`, `oc1pC_*.log`; ZCLASS = OC1P).
- *At positive values (unbounded k)* OC₁′ repairs all 66 ROUND⁺ failures (`fails.jsonl`, `fails_twins.jsonl`), where
  even a round of several chains fails.
- **OC₁′ is a k ≤ 4 statement.** It fails on ksens's PW5 (k = 5, zeros, the natural order), whose obstruction is a
  shared danger pool rather than two picks. It also fails on PW5 lifted and on PW(4,2,5) and PW(4,3,5) lifted.
  - The same PW5 start fails in rnd.c, in the forward brute force, and in k4/sdc's pipeline for OC₁
    (`oc1p_pw5.log`). This also tests the "false" branch of the two OC₁′ implementations.
  - It repairs RD5 (k = 5) and kgen's n = 4 instance.
  - So, like OC₁, OC₁′ must use k ≤ 4. At unbounded k the surviving form is still two rounds (RD²⁺).
- **At positive values a second mechanism defeats OC₁′: two disjoint swaps.**
  - Positive climbs (`oc1p_pos_*.log`, `fails_oc1p_pos.jsonl`) found starts at n = 4, m = 7, 8 and n = 5, m = 9 where
    OC₁′ fails. rnd.c and the forward brute force agree (`oc1p_pos_check.log`).
  - Example: n = 4, m = 7, values [[1115,5553,1291,553,3004,3000,46], [21,2905,920,1305,2402,3000,1938],
    [232,2943,178,368,2117,2957,72], [21,2905,920,1305,683,3000,1938]], order (3, 1, 0, 2).
  - In every MD allocation all four agents lose their picks in two disjoint swaps, 0 ↔ 1 and 2 ↔ 3.
  - One chain performs one swap; one round of two chains performs both. One round (and ROUND-P) holds on every such
    start.
  - This is the "two hand-offs on disjoint pairs" of `kgen/n3.md` §7. That note's count says it needs agents with
    five goods, which fits its absence at k = 4.
- **The picture at positive values.**
  - *Starvation* defeats one round (§3). *Two disjoint swaps* defeat one chain, even OC₁′.
  - **ROUND-P** (vertex-disjoint chains whose agents may also take released end picks) handles both. It holds on every
    start tested, but on the data it is close to MD (§4.2).
  - **Two rounds (RD²⁺)** hold on every start tested.
- **The picture at k = 4 with zeros.** Only starvation has appeared, and **OC₁′^max survives**: every OC₁ failure is
  repaired, and the direct climbs found no failure.

### 4.7 Exhaustive small grids (positive values)
`grid.py` and `rnd.c`'s `rnd_grid` test every profile with values in {1..V}. Agents' rows are taken as a multiset;
every order is tested, so permuting agents changes nothing. At every start they check one round (Lemma RC) and, where
it fails, two rounds (Lemma RC2). The coordinator's lesson applies: OC₁^max survived 11M random tests and fell to
exhaustive ordinal search.

| n | m | values | profiles | starts | need two rounds | need three |
|---|---|---|---|---|---|---|
| 3 | 4 | 1..3 | 91,881 | 223,952 | 0 | 0 |
| 3 | 5 | 1..3 | 2,421,090 | 5,155,168 | 0 | 0 |
| 3 | 6 | 1..2 | 45,760 | 111,932 | 0 | 0 |
| 3 | 7 | 1..2 | 357,760 | 846,088 | 0 | 0 |
| 3 | 8 | 1..2 | 2,829,056 | 6,577,716 | 0 | 0 |
| 4 | 5 | 1..2 | 52,360 | 357,835 | 0 | 0 |
| 3 | 6 | 1..3 | 64,836,045 | 127,496,212 | 0 | 0 |
| 4 | 6 | 1..2 | 766,480 | 4,445,602 | 0 | 0 |
| 4 | 7 | 1..2 | 11,716,640 | 62,363,869 | 0 | 0 |

(`grid_n3.log`, `grid_n4.log`.)
- Not one start on these grids needs even a second round.
- The ROUND⁺ failures of §3 need finely tuned values: RD5⁺ fails only when v₀(4) + v₀(5) < v₀(1) by any margin,
  with values two orders of magnitude apart. Small grids do not contain them.
- So the grids are evidence for ROUND⁺₃ on small values and say little about RD²⁺. An ordinal search, as the
  certifier did for OC₁^max, would be the right exhaustive test.

### 4.8 OC₁′^max: certified at n ≤ 4, refuted at n = 5 (the certifier); the two-cycle mechanism
- **The certifier's result** (`compute/k4-oc1max-cert`; it agreed its move generator with
  `verify_k4zero.one_chain_prime`: identical state sets on 400 random n = 4, 5 core starts, `xcheck_prime.log`).
  - OC₁′^max holds for every strict profile on all 1,002 n = 4 core hypergraphs (`cert_4_prime.json.gz`, with an
    independent check), so it is CERTIFIED at n ≤ 4. This agrees with §4.6: two implementations here found OC₁′ at
    all 112,880 OC₁^max-failing n = 4 starts.
  - At n = 5 it FAILS: 24 of the first 137 OC₁^max-failing starts of its n = 5 run have no OC₁′ repair
    (`oc1prime_cex_n5_partial.jsonl` there, copied to `certifier_oc1prime_cex_n5.jsonl`). Each is a perfect
    maximum-matching start on a strict core.
- **Checked here** (`check_oc1p_n5.py`, `check_oc1p_n5_first6.log`; `flow_oc1p_n5.py`, `flow_oc1p_n5.log`):
  - on the first 6, rnd.c and the forward brute force both report that OC₁ and OC₁′ fail;
  - all 24 are strict cores;
  - **one round of vertex-disjoint chains repairs all 24**, with one absorber and free (brute force).
- **The mechanism: two disjoint cycles, not starvation.**
  - No MD allocation of these starts has a starved agent.
  - In essentially every MD allocation the moved picks form *two disjoint cycles* (swaps or rotations). For example,
    in idx 9 the picks rotate 0 → 1 → 2 → 0 and swap 3 ↔ 4.
  - One chain performs one cycle, even under OC₁′. A round performs both.
  - It is the positive-value "two disjoint swaps" of §4.6, at k = 4 on cores. `kgen/n3.md` §7's five-good heuristic
    for it does not hold at n = 5.
- **The picture at k = 4.**

  | one-step form | starvation (n = 4, C4K, the certifier's 11) | two cycles (n = 5, the certifier's 24) |
  |---|---|---|
  | OC₁ (one chain) | fails | fails |
  | OC₁′ (one chain, middle agents take the end's goods) | holds | fails |
  | one round of disjoint chains | fails | holds |
  | ROUND-P (a round whose chain agents take any end's goods) | holds (it contains OC₁′) | holds (it contains the round) |
  | two sequential moves (OC₂^max) | holds | holds |

  So **ROUND-P^max**, one simultaneous step, is the one-step form that survives every known k = 4 failure, and every
  positive-value failure (§4.2). At n = 4 it follows from the certified OC₁′^max. Two sequential moves (the
  campaign's OC₂^max) and two rounds also survive.

### 4.9 One round and ROUND-P with zeros, at every known k = 4 failure
*Definitions* (zeros allowed, perfect starts, raw EFX₀, one-absorber completion). A round is a set of vertex-disjoint
chains x₀ → … → x_t (t ≥ 0).
- *One plain round (RND1Z).*
  - Each start x₀ takes relevant junk and, in a ring, goods of its own end's base.
  - Every later chain agent x_i takes B_{x_{i−1}} plus relevant junk.
  - A t = 0 agent adds relevant junk.
  - Every chain agent strictly gains, and the untaken goods of the ends' bases are released.
- *ROUND-P (RNDPZ).* The same, and in addition every non-end agent x_i (i < t) of a chain with t ≥ 1 may take goods of
  *any* chain end's base that it values. This is the ledger row K4.SDC.ROUNDP.
  - It contains OC₁′ (one chain) and the plain round.
  - The positive-value ROUND-P of §4.2 (`bruter.rounds_pool(receivers=True)`) is wider: there ends and t = 0 agents
    may also take end goods.
  - A variant that also lets t = 0 agents take them is `verify_k4zero.round_pool(adders=True)`. It was never needed,
    because RNDPZ itself never failed.

*Two implementations.*
- `rnd.c` (`oc1z_start`, bits 16 and 32) tests each complete EFX₀ allocation with Lemma RC: passers s(a) = loc(a), any
  number of paths, maximal H.
- `verify_k4zero.round_pool` simulates forward from the definition.
- `xcheck_roundz.py` compares them at every perfect start of the certifier's 11 (n = 4) and 24 (n = 5) and of 400
  random k-limited instances: 1,256 starts, 0 mismatches (`xcheck_roundz.log`).

*The coordinator's start* is the certifier's n = 5 instance idx 164: order (1, 4, 2, 0, 3), picks (7, 2, 3, 5, 4).
OC₁ and OC₁′ fail there. One plain round holds, and all 9 MD allocations are plain-round witnesses, hence ROUND-P
witnesses too.

**Every known failure** (`rndp_known.py`, `rndp_known.log`; forward re-check of 458 starts, every failure family
included, 0 mismatches):

| starts | mechanism | OC₁ | OC₁′ | one plain round | ROUND-P |
|---|---|---|---|---|---|
| the certifier's 112,880 OC₁^max-failing n = 4 starts (all 11 hypergraphs, every strict type) | starvation | fails | holds | **fails at all 112,880** | **holds at all 112,880** |
| the certifier's 11 n = 4 instances (OC₁-failing perfect starts) | starvation | fails | holds | fails (11 of 11) | holds |
| C4K (2 starts) | starvation | fails | holds | fails | holds |
| zero-core climb failures (§4.5, 47 OC₁-failing starts: 44 at n = 4, 2 at n = 5, 1 at n = 6) | starvation (n = 4) | fails | holds | fails at all 44 with n = 4 and at 1 with n = 5; holds at 1 with n = 5 and at the n = 6 start | holds |
| the certifier's 24 n = 5 instances (26 OC₁-failing perfect starts) | two cycles | fails | fails (24 instances) | **holds at all 26** | holds |

- The two mechanisms separate cleanly.
  - At n = 4 (starvation) the plain round never repairs an OC₁^max failure of the certifier's search. The starved
    agent's second foreign pick is held by a *middle* agent, and only the pooled take reaches it.
  - At n = 5 (two cycles) the plain round always suffices.
- ROUND-P holds at every one of them, at the narrow definition above.

**Positive-value failures** (`rndp_positive.py`, `rndp_positive.log`; 112 re-checked forward, 0 mismatches):
- *Starvation.* At all 158 ROUND⁺ failure starts of `fails*.jsonl` (raw, twins, ε-lifts, KCORE, KCOVER, KIPRIME), the
  plain round fails, as it must, and the narrow ROUND-P holds.
- *ROUND-X's failure.* The narrow ROUND-P holds at X4.
- *Two disjoint swaps.* At the 10 positive-value OC₁′ failures (`fails_oc1p_pos.jsonl`) the plain round already
  holds.

**Which MD allocations ROUND-P misses** (`rndp_gap.py`, written from Lemma RC's structure independently of rnd.c;
its witness counts equal rnd.c's at every start):

| data | perfect starts | MD allocations | ROUND-P witnesses | gaps: no path structure / no gain / absorber |
|---|---|---|---|---|
| 60 random strict cores, n = 5, m = 8 (`rndp_gap_n5m8.log`) | 232 | 8,462 | 7,489 | 0 / 973 / 0 |
| 25 random strict cores, n = 6, m = 9 (`rndp_gap_n6m9.log`) | 190 | 7,901 | 7,397 | 0 / 504 / 0 |

- Every gap has one shape.
  - Some agent b keeps its own pick y_b and also holds the pick of an agent c that holds no pick.
  - c must hand its base to b, and then b's own base is released. b needs y_b back, so the allocation is two rounds
    away: a hand-off, then re-adding the released pick.
- The wide positive-value ROUND-P of §4.2 lets an end take back its own base, so it covers this shape. The narrow form
  does not.
- So a narrow ROUND-P failure needs a start at which *every* MD allocation has such a keep-and-add agent (or one of
  the two shapes never seen: no path structure, or two absorbers).

**Climbs toward a ROUND-P failure** (`zclimb.py`, ZCLASS = RNDPZ; strict connected cores with distinct subset sums;
the objective is failing starts, then the witness count and margin at the hardest perfect start):
- Seeds:
  - the certifier's 24, ×100 (n = 5);
  - 286 six-agent extensions of them (`seeds_rndp_n6.jsonl`). Each adds a sixth agent, random or a near-twin of an
    existing agent, with or without one new good. Following the coordinator, no instance is two copies glued at a
    junk good.
  - unseeded random strict cores at n = 5, m = 9.
- CLIMB_RESULT
- `is_core` alone does not enforce distinct subset sums. Without that constraint the climbs drift to exact ties, such
  as v₀(6) + v₀(7) = v₀(8), so the strict form is enforced (ZSTRICT = 1).

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
| KGEN.R1 | Lemma R1 and the starved-agent certificate (§1): after one round each base holds at most one foreign pick, and a start whose every MD EFX allocation has a starved agent needs more than one round (any values) | PROVED | `kgen/rounds.md` §1; refereed CORRECT (`k4/referee/rounds_r1.md` on `claude/k4-referee`, 4c53b1f) |
| KGEN.RC | Lemmas RC and RC2 (exact one- and two-round characterizations at positive values) | PROVED | `kgen/rounds.md` §1, §4.1 (written proofs, not refereed; cross-checked against forward simulations, `xcheck_*.log`) |
| KGEN.RD2+ | RD²⁺: two rounds suffice at positive values | CONJECTURE | EVIDENCE only: every one-round failure (138 starts found), climbs (`c4_3r_*.log`, `c5_3r_*.log`) |
| KGEN.ROUND3 | ROUND⁺ at n = 3 | CONJECTURE | EVIDENCE only (§5.1); a proof would reprove CGM |
| KGEN.ID | Identical valuations: the picks of every order extend (any n, zeros allowed) | PROVED | `kgen/rounds.md` §5.2 (written proof; checked on 15,684 starts) |
| K4.SDC.OC1MAX | (existing row, REFUTED by the certifier) OC₁^max on strict connected k = 4 cores | REFUTED | additional artifacts: `attempts/kgen-rounds-oc1max-c4k.md`, `results/kgen_rounds/c4k_oc1_max_orders.log`, `results/kgen_rounds/zcore_fails.json`, `results/kgen_rounds/verify_zfails.log`, `results/kgen_rounds/vs_certifier.log` |
| K4.SDC.OC1PRIME | OC₁′^max: as K4.SDC.OC1MAX, with non-end chain agents allowed to take goods of the end's base (one move; implies MD) | CERTIFIED at n ≤ 4 (the certifier, `cert_4_prime.json.gz` on `compute/k4-oc1max-cert`; agrees with the 112,880-start check here); REFUTED at n = 5 (the certifier's 24, two disjoint cycles; checked here) | `oc1p_vs_oc2.log`, `oc1p_vs_oc2_forward_0.log`, `oc1p_vs_oc2_forward_1.log` (n = 4, with the certifier's export), `vs_certifier.log`, `xcheck_oc1p_150_6.log`, `verify_zfails.log`, `oc1p*_*.log`. False at k = 5 (PW5) and at positive values (two disjoint swaps) |
| K4.SDC.ROUNDP | Conjecture ROUND-P^max at k = 4: one round of vertex-disjoint chains in which every non-end agent x_i (i < t) of a chain with t ≥ 1 may also take goods of any chain end's base, one-absorber completion | CONJECTURE (at n ≤ 4 it follows from the CERTIFIED OC₁′^max) | EVIDENCE only: holds at all 112,880 OC₁^max-failing n = 4 starts and at the certifier's 24 n = 5 failures, two implementations (`rndp_known.log`, `xcheck_roundz.log`); strict-core climbs at n = 5, 6 (`zclimb_rndpz_*.log`); `kgen/rounds.md` §4.8, §4.9 |
| K4.SDC.OC1PERF | OC₁ (and one round) at perfect starts for every instance with ≤ 4 relevant goods per agent (the target of Lemma RED's route; the LOOSE form of OC₁^max) | REFUTED | `kgen/rounds/k4w_check.py`, `results/kgen_rounds/k4w_check.log` (K4W, no worthless good), `results/kgen_rounds/verify_k4zero_W4.log` (W4) |

## 7. Next
- **ROUND-P^max at n = 5, exhaustively.** The certifier's ordinal CEGAR with the narrow ROUND-P move (§4.9) on the
  n = 5 core hypergraphs. `rnd.c`'s `oc1z_start` (bit 32) and `verify_k4zero.round_pool` are two reference
  implementations. The only MD shape it misses (keep-and-add, §4.9) says where a counterexample would have to live.
- **OC₁′^max at k = 4, exhaustively.** The certifier's ordinal CEGAR (`compute/k4-oc1max-cert`), run with OC₁′'s
  move, would certify it or refute it on all 1,002 n = 4 core hypergraphs. The move change is local: a non-end chain
  agent may also take goods of the end's base. `rnd.c`'s `oc1z_start` and `verify_k4zero.one_chain_prime` are two
  reference implementations.
- **A designed OC₁′ breaker.** An agent whose pick is wanted and which needs *three* foreign picks fits in four goods.
  OC₁′ gives a base at most two foreign picks, while two rounds could still give three. Not yet constructed: a wanted
  agent can always keep its pick as a singleton, so the frozen configuration has to be forced elsewhere.
- **RD²⁺** at positive values. Ordinal enumeration is infeasible at unbounded k. Bigger climbs with the two-round
  margin at n = 5, 6 (the two-round checker needs a larger MAXS1 at n = 6).
- **n = 3.** Any proof of ROUND⁺₃ reproves three-agent EFX (Proposition H of `kgen/n3.md`). The classification of
  §5.2 (keep / two-agent move / rare rotation) is the structure such a proof would have to produce.
