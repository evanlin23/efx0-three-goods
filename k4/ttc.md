# Housing-market and TTC view of the improving chains (k = 4)

Workstream `proof/k4-ttc` (branch `claude/k4-ttc`, draft PR #101). Code: `k4/ttc/` (`run_all.sh` reproduces every
log); logs: `results/k4_ttc/`. Notation as in `k4/sdc.md` (§2, §28–§30). Everything called evidence below is evidence
only (PROMPT.md §5 rule 3). This note changes no ledger row; the coordinator integrates.

## Status (end of burst 1)

**Proved (short written proofs, §2):**
- *Lemma T1:* with unit demand, no trade of TTC or YRMH-IGYT changes the serial-dictatorship picks. So every repair
  needs a set demand.
- *Lemma T2:* the improving chains and rings of `k4/sdc.md` §29 (with every passed base inside its receiver's relevant
  goods) are exactly the executed request paths and loops of YRMH-IGYT with set requests.
- Lemma 1 of `k4/sdc.md` §2 is Abraham et al.'s characterization of Pareto-optimal matchings, applied to the
  favourite-good matching F(X). Draft and Exchange's Improvement Lemma is Gale's pointer argument with set demands.

**Conjecture OC₁-H (new, survives everything tested, §8).** The pool belongs to the chain's head: from every order,
the picks have a one-absorber completion, or some improving chain x₀, …, x_t with t ≥ 1 has a one-absorber completion
whose absorber is its head x_t (the agent whose pick is vacated). In Abdulkadiroğlu–Sönmez's TTC every vacant house
points to the agent heading the chain, and that is exactly this statement. It sharpens OC₁ toward the refuted strict
dichotomy, and holds on both instances that refute the dichotomy (there the head is the only role that works on both).
- *Data:* 2,310 distinct hard starts (n ≤ 5): special, screen, suite, logs, random cores.
- *Climbs:* adversarial climbs at n = 3 and n = 4 never go below one head-absorbed repairing chain.

**Conjecture MDP∃ (new, survives, §7).** Among the complete EFX₀ allocations that value-dominate the picks, some
allocation with the fewest displaced picks is reached from the picks by one chain. Together with MD this gives OC.
The every-form fails at r617 (n = 4, m = 8, two independent pool swaps; `attempts/k4-ttc-min-displacement.md`).

**Refuted / failed (attempts, smallest failing configurations replayed by brute force):**
- *No fixed TTC priority rule picks the repairing chain* (§3–§4; `attempts/k4-ttc-priority-rules.md`). The best rule
  repairs about 85% of the hard starts, against about a third for a random chain. Smallest failure: r428, n = 3, m = 5.
- *The two-rule mechanism TTC₂ fails too* (§5). It tries every head and two request rules, and repairs every curated
  hard start (special, dich, screen, suite: 1,534 starts) but only 97% of the logged and random ones. Smallest failure:
  n = 3, m = 5. A pool-first rule (Draft and Exchange's chain lemma) repairs the case no other rule did, but a
  49-rule union still misses an n = 4 start.
- *Local validity is neither necessary nor sufficient for a repair* (§6; `attempts/k4-ttc-local-validity.md`). T3,
  n = 3, m = 6.

**What the theory gives as an invariant (§9).**
- Individual rationality relative to the picks is MD.
- The failures of monotone rules come in two kinds: overshooting the region that a complete EFX₀ allocation still
  dominates (the P1 phenomenon), or stalling inside it.
- Pareto efficiency and the core add nothing beyond MD in the pick market. Every dominating allocation is in its core
  (Lemma T3).
- Konishi–Quint–Wako's empty core with additive multi-unit demand is an analogue of P1, not an implication.

**Literature (§1):** recorded with read levels. Full text for Abdulkadiroğlu–Sönmez 1998 and 1999, Abraham et al.
2004, Roth–Postlewaite 1977, Sönmez–Ünver 2010, Konishi–Quint–Wako (working paper), Biró–Klijn–Pápai 2022 and
Todo–Sun–Yokoo 2014. Abstract only for Shapley–Scarf 1974, Ma 1994 and Svensson 1999. Secondary only for Sönmez 1999.

## 1. Literature

Read by this session's literature readers (two agents; their notes, with quotations and URLs, were checked for
internal consistency, not re-read by me against the PDFs). "Full text" means the whole paper was read; numbering is
the source's own. Anything not read is marked.

| source | read level | what is used here |
|---|---|---|
| Abdulkadiroğlu, Sönmez, *House allocation with existing tenants*, JET 88 (1999) 233–260 | full text (author-hosted published PDF) | the TTC algorithm with an ordering f and the YRMH-IGYT algorithm; Prop. 1 (Pareto efficient), Prop. 2 (individually rational), Thm 1 (strategy-proof), Thm 3 (YRMH-IGYT = TTC) |
| Abdulkadiroğlu, Sönmez, *Random serial dictatorship and the core from random endowments*, Econometrica 66 (1998) 689–701 | full text (author-hosted scan; appendix proofs at statement level) | Lemma 1: a matching is Pareto efficient iff some serial dictatorship selects it, iff it is the core of some housing market (model: \|A\| = \|H\|, strict preferences) |
| Abraham, Cechlárová, Manlove, Mehlhorn, *Pareto optimality in house allocation problems*, ISAAC 2004, LNCS 3341, 3–15 | full text (Glasgow ePrints author version) | Prop. 2: PO ⟺ maximal, trade-in-free and coalition-free (strict preferences, incomplete lists, unmatched agents and houses allowed); §6 Lemma 1: serial dictatorship generates every PO matching; Thm 1: maximum PO matching in O(√n m) |
| Roth, Postlewaite, JME 4 (1977) 131–137 | full text (OCR) | Thm 2: with strict preferences the weak-domination core of a housing market is a single allocation, the competitive one (the TTC outcome, by the surrounding text) |
| Sönmez, Ünver, *House allocation with existing tenants: a characterization*, GEB 69 (2010) 425–445 | full main text; proof of Prop. 2 skimmed | Thm 1: PE + IR + strategy-proof + weakly neutral + consistent ⟺ YRMH-IGYT |
| Pápai, *Strategyproof assignment by hierarchical exchange*, Econometrica 68 (2000) | §1–8 (third-party copy of the published PDF), appendix not read | hierarchical exchange with inheritance; AS99's rules are fixed-endowment hierarchical exchange rules |
| Shapley, Scarf, JME 1 (1974); Ma, IJGT 23 (1994); Svensson, SCW 16 (1999) | **abstract only** | core nonemptiness and Gale's TTC [unverified beyond the abstract]; TTC is the unique IR + PE + SP rule [Ma's abstract]; serial dictatorship characterization [Svensson's abstract] |
| Konishi, Quint, Wako, *On the Shapley–Scarf economy: the case of multiple types of indivisible goods*, JME 35 (2001) | full text of Boston College WP 484 (July 2000); journal numbering [unverified] | Prop. 2.4 (core may be empty with Q = 2 types, n ≥ 4, or Q ≥ 3, n ≥ 3); Prop. 4.1 (no PE + IR + SP rule); **§5, Example 5.1: one type of good, additive utilities, allocations any partition, 4 agents, 5 goods, one agent owning two goods: the core is empty**; the authors conclude that "each agent consumes one unit" is crucial. The reader re-checked the examples by enumeration (evidence) |
| Biró, Klijn, Pápai, *Serial rules in a multi-unit Shapley–Scarf market*, GEB (2022) | full text | multi-unit circulation model with responsive preferences; IR + PE rules exist (Cor. 18); no core results |
| Biró, Klijn, Pápai, balanced exchange, BSE WP 1342 (2022) | main results | IR + PE + SP compatible exactly for "irreducible" capacity configurations, and then only the circulation TTC rule (Thm 2) |
| Todo, Sun, Yokoo, AAAI 2014 | full text | Prop. 1: with lexicographic preferences and multiple endowments no rule is SP and PE |
| Sönmez, *Strategy-proofness and essentially single-valued cores*, Econometrica 67 (1999) | **secondary only** (Ehlers 2014, Takamiya 2003) | IR + PE + SP rule exists iff the core is essentially single-valued [unverified] |
| Sikdar, Adalı, Xia, AAAI 2017 | main results (arXiv v1) | multi-type housing markets: no IR + PO + SP rule (Thm 2); strict-core checking coNP-complete |
| TTC and EF1/EFX | search | no paper connecting TTC with EFX was found; TTC-style steps give EF1 for chores (Bhaskar–Sricharan–Vaish 2021) and EF1 mechanisms (Echenique–Goel–Lee 2025) [both at main-results level] |

**How the literature handles a chain ending at a vacant house** (AS99 §5, proof of Thm 3, Case 1): every available
house points to the top-priority remaining agent i₁, so a request chain i₁ → h_{i₂} → i₂ → … → i_k → h (h vacant)
closes into a cycle exactly when its head i₁ has top priority; then i_k gets h, each i_j gets h_{i_{j+1}}, and the
head's own house becomes available. The pool is, in effect, the head's endowment (Pápai's view: vacant houses are the
endowment of the top-priority agent).

## 2. The induced market

**The market of a start.** Fix an order π and its picks Y = SD(π), with junk J (the unpicked goods).
- *Agents:* every agent is an existing tenant holding its pick Y_i as its "house", or a newcomer if Y_i is none.
- *Pool:* the junk is the set of vacant houses.
- *Demand:* additive over subsets of the agent's at most 4 relevant goods. A *request* of agent a is an option
  strictly better than its base:
  - *take:* the base of another agent plus junk, inside R_a;
  - *pool:* junk only, giving up its base.

**Lemma T1 (unit demand trades nothing).** In the unit-demand market (each agent requests single goods of R_i ranked
by value, its own pick acceptable), no request path of YRMH-IGYT or TTC that improves its agents can execute from Y.

*Proof.* An executed unit-demand trade is either a request path ending at a vacant house or a loop.
- *Path to a vacant house.* Its last agent i_k requests a junk good h with v_{i_k}(h) > v_{i_k}(Y_{i_k}). By property
  (I2) of serial dictatorship, every unpicked good is worth less to each of its valuers than its pick (an agent
  without a pick values no unpicked good). Contradiction.
- *Loop.* Each agent requests a pick it prefers to its own. By (I1), every good an agent prefers to its pick was
  picked earlier, so every request points to an agent earlier in π, and no loop exists. ∎

These are the trade-in-free and coalition-free conditions of Abraham et al. (Prop. 2). With strict preferences, the
same follows from Y being Pareto-optimal (AS98 Lemma 1; Abraham et al. §6 Lemma 1, which allows incomplete lists) and
TTC being individually rational and Pareto efficient (AS99 Props. 1–2). The direct proof avoids model mismatches
(AS98 assumes |A| = |H| and complete lists).

*Consequence.* Every repair of a start moves some agent to a *set*. This is where k ≥ 4 differs from the
single-unit theory. KQW's §5 example shows that additive multi-unit consumption can empty the core, and P1
(K4.SDC.P1) shows that it can trap value-monotone processes.

**Lemma T2 (chains are request paths).** Run YRMH-IGYT with set requests (`k4/ttc/ttclib.py`, `yrmh`):
- the highest-priority agent is the head and makes a take request;
- the owner of the requested base gets the turn ("I get your turn") and requests in its turn;
- a pool request closes a chain, and a request for a base already on the path closes a loop.

The executed chains are exactly the improving chains x₀, …, x_t of `k4/sdc.md` §29 in which each passed base
B_{x_{i−1}} lies inside R_{x_i}: x_t is the head, x₀ the pool requester, and H_i the junk part of x_i's request. The
executed loops are the rings, together with the chains whose x₀ takes the head's base.

*Proof.* By definition. Agent x_i requests B_{x_{i−1}} ∪ H_i, worth more than its own base. The requests reserve
disjoint junk. When the path closes, every agent on it receives its request, and the head's old base, requested by
nobody on the path, becomes vacant. Conversely, an improving chain becomes a request path once its head is given top
priority and each agent requests exactly its part of the chain. ∎

So OC and OC₁ say that some request path repairs. §29's "no simple rule picks the chain" asks for a rule; the
housing-market answer is a priority (who heads) plus a request preference (what each agent asks for). §3–§5 test
that answer.

**Lemma 1 of `k4/sdc.md` §2 is Abraham et al.'s Prop. 2.** For an allocation X, F(X) (each agent's favourite held good)
is a matching. In the house-allocation instance with preference lists R_i ranked by value:
- (U) says F(X) is maximal and trade-in-free (a non-favourite good is an unmatched house);
- (A) says it is coalition-free (its envy graph is acyclic).

So X completes an SD outcome iff F(X) is a Pareto-optimal matching (Abraham et al., Prop. 2 and §6 Lemma 1). SD-C reads
"some EFX₀ allocation has a Pareto-optimal favourite matching".

**Draft and Exchange (`paper/k3-simple`) as TTC.**
- *The Improvement Lemma is Gale's pointer argument:* every agent outside U points (σ), and following the pointers
  closes a ring.
- *A pair arrow is a set demand:* a blocker x of the free agent o requests o's good together with a leftover good
  h_x (its pair).
- *The chain lemma is a pool request:* x requests its pair {b_x, c_x} from the junk, and its top passes along the
  wanters to an unwanted agent, the head.

At k = 3 every set demand is a pair. At k = 4 the dangerous agent's request can be any junk danger set, and middle
agents can make set requests.

## 3. Mechanisms run from the picks

**Configurations** (`k4/ttc/ttclib.py`, `k4/ttc/ttc_test.py`).
- *Request preference* (for the head / for the other agents):
  - `val`: the most valuable option;
  - `minval`: the least valuable improving option ("just enough");
  - `lean`: the fewest junk goods;
  - `minimal`: an inclusion-minimal junk part, the most valuable such;
  - `small`: the fewest goods;
  - `poolval`, `poolmin`: a pool request if there is one, else `minval`.
- *Priority:* the order π, its reverse, index order, dangerous agents first, or unwanted agents first.
- *Mode:*
  - `one`: the first trade;
  - `head`: the first trade through the head;
  - `full`: the whole mechanism;
  - `rep`: repeated first trades, testing the completion before each.

**A start is hard** when its picks have no one-absorber completion (`oc_absorb.extends_A`). A run *repairs* it when
the resulting state has one.

| data | hard starts (per order) | best configuration | repaired | log |
|---|---|---|---|---|
| special (T3, Q2, r4253, r3943) | 69 | minval/minval, reverse π, rep | 66 | `ttc_test_special.log`, `ttc_grid_special.log` |
| screen (168 instances) | 662 | minval/minval, reverse π, rep | 564 | `ttc_test_screen.log`, `ttc_grid_screen.log` |
| suite (158) | 797 | minval, reverse π, rep | 687 | `ttc_test_suite.log` |
| random cores n ≤ 3 (3,000 profiles) | 480 | minval, revdanger, rep | 393 | `ttc_test_n3.log` |
| random cores n = 4 (1,500) | 872 | minimal, reverse π, rep | 726 | `ttc_test_n4.log` |
| logged hard profiles (1,637) | 4,574 | minimal, reverse π, rep | 3,622 | `ttc_test_logs.log` |

- *Baseline:* a uniformly random improving chain repairs a distinct hard start with probability 0.32–0.35 on
  average (`ttc_test_*.log`).
- *What matters:*
  - priority to the reverse order (the last agent, never frozen, heads the path) roughly doubles the success rate
    over the order itself;
  - "just enough" requests (`minval`) beat the agents' own preference (`val`, which is what TTC uses): on the screen
    set 564 against 381 repaired starts (`ttc_grid_screen.log`).

## 4. Why fixed rules fail: overshooting and stalling

`k4/ttc/ttc_fail.py`, `results/k4_ttc/ttc_fail.log` (minval, reverse π, rep). Of the 98 screen failures:
- **39 overshoot.** The first trade leaves the region of states that some complete EFX₀ allocation still
  value-dominates (`ttclib.dominated`: SAT on sdclib's encoding with every bundle worth at least the base). Every
  later improving trade stays outside the region, so no monotone method recovers. This is P1 (K4.SDC.P1) met
  dynamically.
  - Example: r4253, picks (5, 1, 4, 6). The head's cheapest request closes the ring 3 ↔ 0, which raises agent 0 from
    10 to 11 and agent 3 from 7 to 10. The resulting state is not dominated.
- **59 stall inside the region.** Every request path dead-ends. From 10 of these stall states one improving chain
  still repairs.

Global least-gain rules do no better (`min_rule.py`, `min_rule.log`; 194 distinct hard screen starts):
- some best-ranked chain repairs for the least total gain on 68 starts, the least largest gain on 67, the least
  relative gain on 11, the fewest agents on 13, and the least gain of x₀ on 108;
- among the Pareto-minimal chains, some repairs on 10 of 16 special starts.

So the 85% of the TTC rules comes from the request structure (priority plus a path to the pool), not from
minimality.

## 5. Realizability: the repairing chains are TTC paths, but no finite rule list picks one

**With every agent tried as head** (`ttc_heads.py`, `ttc_heads.log`), a fixed preference repairs at most 578 of the
662 screen starts (minval), and the last agent as head at most 491.

**The union of runs** (`ttc_union.py`, `ttc_union.log`) takes every head, the 25 head/inner pairs of val, minval,
minimal, lean and small, and modes one and head. Some run repairs all 16 special and all 194 distinct screen starts.

**Candidate TTC₂** (`ttc2.py`): try the 2n runs given by every head and the rules minimal/minval and minval/minval.

| data | hard starts | TTC₂ repairs | the head can absorb |
|---|---|---|---|
| special | 69 | 69 | 69 |
| dichotomy failures (dich3, dich-r7) | 6 | 6 | 6 |
| screen | 662 | 662 | 622 |
| suite | 797 | 797 | 757 |
| logged hard profiles | 4,574 | **4,436** (34 instances fail) | 4,434 |
| random cores n ≤ 3 | 480 | **456** (12 instances) | 451 |
| random cores n = 4 | 872 | **837** (10 instances) | 837 |
| random cores n = 5 (150) | 391 | 391 | 391 |
| random n = 6–9 (oc1_bign generator, 400 instances, 12 orders) | 22 | **21** (1 instance) | 21 |

Logs: `ttc2_curated.log`, `ttc2_data.log`, `ttc2_bign.log`. TTC₂ is **refuted** as a complete rule. Its smallest
failures are n = 3, m = 5 (r1889: sets [[0,2,3,4],[1,2,3,4],[2,3,4]], values [[5,6,7,3],[4,1,6,8],[2,3,4]], order
(0, 2, 1); log59).

On the ten n = 3 failures, the 25-pair union of every head and three modes repairs all but r1174
(`ttc2_failures_union.log`).
- *r1174:* sets [[0,2,4,5],[1,4,5],[3,4,5]], values [[6,3,5,7],[2,4,3],[2,3,4]], picks (5, 4, 3).
- Every rule there makes the dangerous agent 0 request agent 1's pick plus junk, which closes a ring with 1. The
  repair is 0's *pool* request {0, 2}.
- A pool-first rule (`poolval`, `poolmin`), which is Draft and Exchange's chain lemma, repairs it.

With the 49 pairs over the seven rules (`ttc_cover2.log`):
- all 293 distinct random n ≤ 3 starts and all 194 screen starts are covered (two rules suffice for each set:
  minimal/poolmin with minval/poolmin, and minimal/minval with minval/minval);
- 214 of the 215 random n = 4 starts are covered. The exception is r323, picks (4, 6, 5, none), which no run of any of
  the 49 pairs repairs.

*Conclusion.* The repairing chain is almost always a TTC request path with a natural request rule, and the pool-first
rule is the k = 3 chain lemma. But no finite list of rules tried selects it everywhere. §29's finding ("the chain has
to be chosen by the completion test itself") extends to priority rules.

## 6. Local validity is neither necessary nor sufficient

`local_rule.py`, `local_rule.log`; `attempts/k4-ttc-local-validity.md`.
- *Filters:* validity (every wanted good held alone), no threat among bases, (G4) for the frozen agents, x₀ no longer
  dangerous. They raise the repairing fraction of chains from 34% to 80–92%.
- *Not necessary:* on 7 of the 194 screen starts no valid chain result repairs. Example: T3 from picks (0, 1, 4). The
  repair leaves the wanted good 4 inside agent 0's pair, and the completion compensates the wanter with junk.
- *Not sufficient:* on 105 starts some valid, threat-free result does not repair. Example: T3 from (0, 4, 1).

## 7. Displacement: the target allocation and one path

**Housing-market view.** The picks are endowments, and a complete EFX₀ allocation X that value-dominates them is an
individually rational target (MD).
- *Displaced agent:* one whose pick is not in its bundle.
- *One-path:* the displaced agents form one path x₀ → … → x_t, each receiving its predecessor's pick, with x_t's pick
  anywhere. This is one improving chain followed by a free completion.

`displace.py` (SAT, enumerating the placements of the displaced picks among the minimal allocations), `displace.log`,
`displace_all.log`; `repro_attempts.py` (c), (d) for brute-force replays.
- *Fewest displaced agents k\*,* over 2,308 distinct hard starts: 0 (104 starts: the picks extend under the free
  completion but not with one absorber), 1 (1,040), 2 (901), 3 (237), 4 (25), 5 (1).
- **Every** minimal allocation is one-path on all starts but two: r617 (n = 4, m = 8) and r13 (n = 5). At r617 the
  two displaced agents each swap their pick for junk, which gives two independent pool swaps. The brute-force replay
  finds 1 of the 19 minimal allocations not one-path. See `attempts/k4-ttc-min-displacement.md`.
- **Some** minimal allocation is one-path on every start: **Conjecture MDP∃**. With MD it gives OC (up to strictness
  under ties). An extremal proof would choose, among the closest dominating allocations, one that also minimizes a
  second quantity (junk moved, total gain), so that two pool swaps can be merged or one undone. Not yet tested.

## 8. The pool belongs to the head: Conjecture OC₁-H

**Conjecture OC₁-H.** In every instance with at most four relevant goods per agent, for every order π:
- the picks have a one-absorber completion, or
- some improving chain x₀, …, x_t with t ≥ 1 has a one-absorber completion in which the head x_t (the agent whose
  pick becomes junk) is the absorber.

It lies between OC₁ (any absorber) and the strict dichotomy (no absorber after the chain), which is refuted (§29).
- *Source:* AS99's TTC, where a chain ending at a vacant house executes only when its head is the agent the vacant
  houses point to. The pool is the head's endowment.
- *Relation to k = 3:* LB⁺'s Theorem B, which gives the surplus to one owner after one rotation, has the same shape.

**Evidence** (`head_owner.py`, `head_owner.log`, `head_owner_all.log`; distinct hard starts; for each, over every
description of every improving chain):

| data | distinct hard starts | head absorbs | no absorber needed | x₀ absorbs | an agent off the chain absorbs |
|---|---|---|---|---|---|
| special | 16 | 16 | 16 | 16 | 15 |
| dichotomy failures | 2 | **2** | 0 | 1 | 1 |
| screen | 194 | 194 | 194 | 194 | 181 |
| suite | 196 | 196 | 196 | 196 | 183 |
| logged hard profiles (n ≤ 5) | 1,364 | 1,364 | 1,362 | 1,363 | 1,300 |
| random cores n ≤ 3 (3,000) | 293 | 293 | 293 | 293 | 279 |
| random cores n = 4 (1,500) | 215 | 215 | 215 | 215 | 214 |
| random cores n = 5 (150) | 30 | 30 | 29 | 30 | 29 |

- Where the strict dichotomy holds (a chain after which no absorber is needed), any agent can absorb, so OC₁-H's
  content sits in the dichotomy failures. On both known ones the head absorbs, while x₀ fails on one and every
  off-chain agent on the other.
- *Adversarial climbs* (`head_climb.py`) minimize the number of head-absorbed repairing chains at the hardest start,
  with the mutations of `k4/sdc/oc_climb.py`. Runs: n = 3 (12 rounds × 1,200 steps; 25 × 3,000), n = 4 (8 × 400;
  15 × 1,200). Logs `head_climb_n3*.log`, `head_climb_n4*.log`. **No run goes below one.**
- The runs of `ttc2.py` record whether the accepted run's head can absorb: 94–100% of the hard starts (table of §5).

## 9. What the theory offers as an invariant

- *Individual rationality* relative to the picks is value domination. Every state reached by improving chains is IR,
  and MD says IR outcomes exist. §4 shows that the relevant invariant for an iterative method is **staying
  dominated**: the fixed rules fail exactly by leaving the dominated region (39 of 98 failures) or by stalling in it.
  A one-chain statement (OC₁, OC₁-H) avoids iteration altogether.
- *Pareto efficiency* is what makes unit-demand trades useless (Lemma T1). It does not persist as an invariant: a
  repaired state need not be Pareto-optimal among base states (not tested further).
- **Lemma T3 (the pick market's core is trivial).** In the market where coalitions may reallocate only their own
  picks, every allocation X that value-dominates the picks is in the core.

  *Proof.* Suppose S blocks X by a reallocation ν of {Y_i : i ∈ S}, with v_i(ν_i) ≥ v_i(X_i) ≥ v_i(Y_i) on S and one
  strict. Then ν together with Y outside S is a one-good matching that Pareto-dominates Y. That contradicts the
  Pareto optimality of Y (Lemma SDPO). ∎

  So the core adds nothing to MD. A nontrivial core needs the pool to be owned. With the pool owned by the head, as
  in OC₁-H, the induced market has an agent endowed with several goods and additive demand: the setting of KQW's
  Example 5.1, whose core can be empty. Whether some OC₁-H completion lies in the core of the head-owned market is
  untested.
- *P1 and Konishi–Quint–Wako.*
  - P1: a Pareto-maximal partial EFX₀ allocation such that no complete EFX₀ allocation is IR relative to it.
  - KQW §5: an endowment such that every IR allocation is blocked by a coalition.

  Both come from multi-unit additive demand and fail where the unit-demand theory (TTC) succeeds. They are different
  obstructions (a feasibility constraint versus coalitional stability), and neither implies the other. The lesson KQW
  draw, that one-unit consumption is what makes exchange work, matches Lemma T1: every k = 4 repair uses a set demand.
- *Strategy-proofness* (AS99 Thm 1, Ma, Sönmez–Ünver) concerns incentives and gives nothing for existence.

## 10. Next steps (for the coordinator and for burst 2)

1. *OC₁-H at larger n:* run `head_owner.py` on `big:6-9` (needs a lazy chain enumeration, as in
   `k4/sdc/oc1_bign.py`), and climb at n = 5.
2. *A proof route for OC₁-H through Lemma GDT:*
   - after a canonical chain from a dangerous agent, the head's old pick is junk and the head is the absorber;
   - (G5) holds if the head's new base is unwanted;
   - so the missing piece is (G4) for the remaining frozen agents with the head as owner. This is the "missing count"
     of `k4/sdc.md` §30, but now with a prescribed owner.
3. *MDP∃ with a second extremal criterion* (fewest junk goods moved, least total gain), to kill the r617 pattern.
4. *The core of the head-owned market* (Lemma T3's remark): test on the hard starts whether some OC₁-H completion is
   in the core, or whether the KQW-type emptiness appears.
