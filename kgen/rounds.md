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
  - Classification of what a start needs: most starts keep their picks; otherwise a hand-off or a swap of two agents
    usually works. Some starts need only a hand-off, some only a swap, and one random start needs the three-agent
    rotation (§5.2, verified by forward simulation).
  - The starved-agent obstruction needs four agents (§5.3, partial argument).

| statement (strictly positive values, every SD start) | n = 3 | n = 4 | n = 5 | instance | checks |
|---|---|---|---|---|---|
| picks extend (free) | fails | fails | fails | | |
| one chain (OC₁, t ≥ 0) then one absorber | holds (data; kgen-n3) | **fails** (kgen n = 4 lifted, m = 8) | **fails** (PW5 lifted) | `named.log` | rnd.c, ocsat |
| **ROUND⁺: one round of disjoint chains** (free = one absorber at n ≤ 5, Lemma RC (c)) | holds (data) | **FAILS** (RD5⁺, m = 7; two types, m = 7) | **FAILS** (m = 8, 9) | §3 | rnd.c, bruter.py, ocsat/ocseq; certificate script |
| ROUND-X: one round, starts draw from a common pool of released picks | holds | **FAILS** (X4, m = 7) | holds (data) | §4.2 | rnd.c, bruter.py (pooled) |
| ROUND-P: one round, every chain agent draws from the pool | holds | holds (data) | holds (data) | §4.2 | rnd.c, bruter.py (pooled) |
| **RD²⁺: two rounds** | holds | holds (data, every failure) | holds (data) | §4.1 | ocseq, bruter.py two rounds |
| MD (some EFX allocation value-dominates the picks) | holds | holds | holds | | rnd.c |

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
| `kgen/rounds/climb2.py` | climbs toward starts needing three rounds (rnd.c, then ocseq counts of two-round completions) |

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
- Every one-round failure found (`fails.jsonl`, `fails_twins.jsonl`) is repaired by two rounds, with one absorber
  (ocseq `multi=True`; `climb2.py` evaluates every failing start).
- `climb2.py` climbs from the failures toward starts needing three rounds. It minimizes the number of complete EFX
  allocations reachable in two rounds (ocseq, capped), at n = 4, m = 7 and n = 5. No start needing three rounds so
  far (`climb2_*.log`).
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

### 5.3 Why the starved-agent obstruction needs four agents (partial)
- At n = 3 a starved agent a must hold y_b and y_c. Then b and c both lost their picks, and one of them, say b, holds
  no pick at all (X_b ⊆ J), because y_a is in only one bundle.
- The only round structure placing y_b and y_c with a is the path b → a → c with y_c released into X_a, which needs
  y_a ∈ X_c. Its gain at a is v_a(y_b) + v_a(X_a ∩ J) > v_a(y_a).
- If that fails, X is unreachable. But at n = 3 such an X seems never to be the only MD allocation: on all data
  another MD allocation is reachable.
- A proof would have to construct that allocation, which is the three-agent existence problem again. Not proved.

## 6. Next
- RD²⁺: faster two-round checker (C, backward with round-1 enumeration) and bigger climbs, n = 5, 6; the depth-two
  design of §4.1 at n = 6.
- Turn the starved-agent certificate into the obstruction statement it suggests: "some MD allocation has no starved
  agent" is ROUND-P-like and contains EFX existence; what does k ≤ 4 add?
