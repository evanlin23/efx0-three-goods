# Housing-market and TTC view of the improving chains (k = 4)

Workstream `proof/k4-ttc` (branch `claude/k4-ttc`, draft PR #101). Code: `k4/ttc/` (`run_all.sh` reproduces every
log); logs: `results/k4_ttc/`. Notation as in `k4/sdc.md` (§2, §28–§30). Everything called evidence below is evidence
only (PROMPT.md §5 rule 3). This note changes no ledger row; the coordinator integrates.

## Status (burst 7): R2 is owned here; stated, evidenced, a first step proved, the plan written (§14.6)

- **R2** (leaf 5a of the case tree, `k4/oc1_hall.md` §23.2): at a perfect serial-dictatorship start with at least two
  receivers (pick holders nobody values above their own pick), one move gives a one-absorber completion.
  - At the picks there are no multi-good holders, so blocked holders cannot arise. R2⁺, at post-move states, is false
    (§14.5).
- **Evidence:** R2 holds at every hard start with two or more receivers tested. That is 79 in an n = 4 walk and 466
  in an n = 6 sweep sample, plus 4,027 in grown n = 5 walks (there OC₁^max held everywhere). Every known OC₁^max
  failure has exactly one receiver.
- **Strong form R2★, which the data suggest is the proof target:** some canonical chain from a dangerous agent to a
  receiver leaves junk that can be spread one good per agent, so no owner is needed (79/79, 466/466).
- **Proved:** Lemma R2-0. If |J| ≤ |U|, the picks complete with one junk good per receiver. So a hard start with two
  receivers has at least three junk goods.
- **k ≤ 4 is necessary:** PW5 (k = 5) has two receivers and fails. Lemma PL (`claude/k4-ksens`) is the k = 4 count a
  proof must use.
- **Open:** steps 1, 3 and 4 of the plan in §14.6. Rule out a 2-cycle of the pointer map; handle agents sharing one
  good of H₀, and the released pick; count the slots, presumably by Lemma M with no owner.
- **Requested:** an exhaustive n = 4 check of R2 and R2★ from the certifier.

## Status (burst 6): OC₁^max falls at n = 4; two moves always suffice so far, by a pointer rule in the MC2 class

**OC₁^max is refuted** (§14.2).
- *Found by:* the certifier's ordinal CEGAR (`compute/k4-oc1max-cert`), on 11 of the 1,002 n = 4 core hypergraphs,
  all in the K4.MC2 class.
- *Checked here:* by brute force (`refute_oc1.py`) and by SAT on all 11 (`oc1max_cex_n4_ttc.log`).
- *Rare:* 0 of 3,000 random profiles of the first hypergraph fail. So the n = 6 sweep (1.8 million maximum starts, 0
  failures; §14.1) was evidence only.

**Why one move is not enough at n = 4.**
- Every instance has a single receiver.
- In every allocation that could follow a repair (complete, EFX₀, value-dominating the picks), some agent holds the
  picks of two other agents. Its improving bundles are complementary across two owners.
- A move gives each participant one predecessor's base (x₀: part of one base B_{x_t}) plus junk. In TTC terms, a
  cycle serves unit demands, and this exchange is a tree.
- **Lemma T6 (proved, §14.2)** makes this exact: after one move and any completion, an agent holds two other agents'
  picks only as an internal chain member that also receives the chain end's pick. With the brute-force list of
  targets, it gives a human-checkable proof that one move fails, for all 11 instances (`oc1max_cex_n4_ttc.log`).

**Two moves do suffice, and pointers choose them, at n = 4** (§14.3). Call a chain a *minimal pointer fixed point*
when a dangerous agent takes an inclusion-minimal improving junk set as its new base and its pick travels along a pure
want path to the receiver.
- Every such chain is a good first move: 34 of 34 on the instances, and at all 1,174 OC₁^max failures of a walk around
  them (48,504 profiles). One more move then finishes.
- That is the rule **FP+1^max**, which implies OC₂^max.

**FP+1^max fails at n = 5, outside the MC2 class** (`attempts/k4-ttc-fp-plus-one.md`).
- *The core:* strict, with one agent holding two private goods. It is also a new n = 5 counterexample to OC₁^max, in
  the free form too (`oc1max_cex_n5_two_private.json`, brute force).
- *Why the rule fails:* no dangerous agent improves with junk alone, so no fixed point exists. The danger is absorbed
  by a dangerous agent *inside* a chain, taking its predecessor's pick plus its danger junk.
- *Still holding:* OC₂^max, and "every good first move absorbs danger" (1,191 of 1,191 failures tested).
- *MC2-class grow walks* found no n = 5 OC₁^max failure (1,819 instances).

**Every OC₁^max failure tested has exactly one receiver**; at two receivers, one move always sufficed. That gives
Conjecture R2 (§14.3), which would confine the problem to the one-receiver regime.

**Open, in order:**
1. FP+1^max in the MC2 class at n = 5–6; running (§14.4).
2. OC₂^max itself, and R2.
3. A proof of the n = 4 mechanism: one receiver forces the danger set to become a base.

## Status (burst 5, superseded: OC₁^max fails at n = 4, burst 6): "for every order" fails even in the K4.MC2 class; the max-matching form survives everywhere tested, R1-priority only in the MC2 class

**OC and OC₁ fail for some order on a strict connected core in the K4.MC2 class** (`attempts/k4-ttc-oc-every-order.md`).
- *The core:* n = 5, m = 9, three 4-good agents, one private good each. Agent i values {yᵢ:10, aᵢ:6, bᵢ:5, bᵢ₋₁:7};
  two 3-good agents value {y₀, y₁, y₂}.
- *The failing order:* (0, 1, 2, 3, 4), with picks (y₀, y₁, y₂, none, none). The two pickless agents freeze everyone
  else. Each frozen agent's junk is a danger triangle, so the junk has no completion at all, free or one-absorber,
  and none of the 232 improving moves helps.
- *Checks:* SAT, the independent brute force `refute_oc1.py`, and the Hall session's own code and written count.
- *Still true there:* MD holds, two moves suffice, SD-C holds, and every R1-priority order works. The failing
  picks are not a maximum matching (3 of ν = 5 agents matched).
- *Order classes on all 41 core counterexamples* (`order_classes.log`): OC₁^max holds on every one (0 failing
  maximum-matching outcomes). R1-priority OC₁ fails on the three two-private cores (the n = 5 hand core, and B< and
  B>) but on none of the 38 MC2-class ones. Every failing order matches ν − 2 agents.

**What is refuted "for every order":** OC (free completion, one move), OC₁, OC₁ᵖ, OC₁-ED and OC₁-ED\*.

**What survives:**
- MD, SD-C and TARGET₄;
- the R1-priority forms (OC and OC₁ for LB's Phase-1 orders), but only in the K4.MC2 class; they fail on strict cores
  with two-private agents;
- the coordinator's **OC₁^max** (orders whose picks form a maximum matching; such orders exist and are computable, by
  Abraham et al. Thm 1 and §6 Lemma 1, §1).

**Climbs against the surviving forms** (`core_climb.py`; a failure is a hard start with no repairing move):

| climb | class | runs × steps | failures | fewest repairing moves reached |
|---|---|---|---|---|
| R1-priority orders, seeded from the MC2 counterexample (`core_climb_mc2_r1_seeded.log`) | MC2, n = 5 | 6 × 400 (40 orders) | 0 | 3 |
| R1-priority orders, random (`core_climb_mc2_r1_6_7.log`) | MC2, n = 6–7 | 24 × 400 (12 orders) | 0 | 1 |
| OC₁^max, seeded from the two-private n = 5 core (`core_climb_max_seeded_core.log`) | strict cores, n = 5 | 6 × 300 | 0 | 2 |
| OC₁^max, seeded from the MC2 counterexample (`core_climb_max_seeded_mc2.log`) | MC2, n = 5 | 6 × 300 | 0 | 2 |
| OC₁^max, random (`core_climb_max_6_7.log`) | strict cores, n = 6–7 | 24 × 300 (12 maximum-matching orders) | 0 | 1 |
| OC₁^max, Hall-deficient cores with ν < n, kept under mutation (`core_climb_max_deficient.log`) | strict cores, n = 6–8 | 24 × 300 | 0 | 21 |
| OC₁^max, dense cores with m ∈ [2n, 3n] (`core_climb_max_dense.log`) | strict cores, n = 6–8 | 24 × 300 | 0 | 9 |
| OC₁^max, Hall-deficient cores (`core_climb_max_deficient_mc2.log`) | MC2, n = 6–8 | 24 × 300 | 0 | 30 (the cap: no hard start with fewer repairs was reached) |

On the Hall-deficient cores the hardest start still had 21 repairing moves, as Lemma T5 predicts: at
maximum-matching picks the pickless agents only freeze agents without junk.

*A hand-made attack on OC₁^max* (`max_hand.py`, `max_hand.log`) gives each pickless agent of the MC2 counterexample
a private fourth good of the lowest value. Then the failing order matches every agent while the yᵢ stay wanted. On
all 60 MC2-class variants, OC₁^max, OC^max and the R1-priority forms hold.

## Status at the end of burst 4: OC₁ fails on strict cores, but only with agents holding two private goods (superseded: an MC2-class counterexample to OC and OC₁ followed in burst 5)

**OC₁ fails on strict connected k = 4 cores** (`attempts/k4-ttc-oc1-counterexample.md`, §13):
- n = 5, m = 9, built by hand here;
- n = 6, m = 10, found by the Hall session from this note's climb list.

All three sessions verified both independently, by SAT and by brute force. **Every core counterexample has agents
with two private goods** (here they are the danger pairs). K4.MC2 (CERTIFIED) excludes such agents from a minimal
counterexample to TARGET₄. So **OC₁ on the K4.MC2 class** (strict connected cores, no agent with two private goods) is
open and still implies TARGET₄.
- *A natural MC2-class version of the counterexample* (`oc1_mc2_candidate.json`) satisfies OC₁: a chain takes a danger
  pair plus a shared good of another pair.
- *Climbs inside the class* (`core_climb.py … mc2`) are running.
- *OC near the counterexample* (`core_climb.py 12 400 24 81 5 5 free seeded`, `core_climb_oc_seeded.log`): this climb
  uses the free completion and stays inside cores, starting from the n = 5 counterexample. It ran 12 runs × 400 steps
  and OC never failed; 6 runs reach a start with a single repairing move.
- *The unrestricted core climb at n = 6–7* (`core_climb_6_7.log`) was stopped after 35 of 48 runs with no OC₁ failure.
  Random starts did not find the special profiles.
- *OC₁ᵖ* (absorbers counted only among agents holding a base) holds on every counterexample.
- *Not affected:* OC, MD, SD-C and TARGET₄.

**The n = 5 counterexample in detail.**
- *The core:* n = 5, m = 9, three 4-good agents. The 4-good agents value {yᵢ, yᵢ₊₁, aᵢ, bᵢ} at (10, 3, 6, 5), with aᵢ,
  bᵢ private. Two 3-good agents value {y₀, y₁, y₂} at (4, 3, 2) and (2, 4, 3).
- *The failing order:* (0, 1, 2, 3, 4), and also the R1-priority order (0, 2, 1, 3, 4). Its picks
  (y₀, y₁, y₂, none, none) have no one-absorber completion (written count), and none of the 62 improving moves gives
  one (brute force and SAT).

**Earlier in burst 4.** 84 non-core counterexamples at n = 6, m = 10, and a k = 3 family (n = 5, m = 9; R2-peelable).
They led to the core above.

**How rare** (`oc1_n5_many4.log`, `oc1_core_profiles.log`):
- *Random profiles of the n = 5 core lists with three, four and five 4-good agents* (200 profiles each, every order,
  the repository's `oc_absorb.py`): no failure in 72,000 starts.
- *On the counterexample's own hypergraph:* 5 of 259 random strict core profiles fail OC₁ (1.9%), and OC (free
  completion, at most one move) holds on all 259.

The failure is a property of special profiles, the kind random sampling misses (PROMPT.md §5 rule 3).

**Core climb** (`core_climb.py`, every mutation kept inside strict connected cores): at n = 6–7 no failure so far.
Several runs reach a start with a single repairing move. The run is in progress.

**What survives after burst 4.**
- **OC** (one improving move, then a *free* completion), MD and SD-C hold on all data, including every OC₁
  counterexample (zero moves needed there).
- **MDP∃** (§7) is about free completions and is unaffected.
- Lemmas T1–T4 (§2, §9, §11) are proved and unaffected. Lemma T4's pointer argument (§11) was aimed at one-absorber
  completions and needs a multi-owner version.
- *The TTC reading of the failure.* In AS99's TTC the pool has one owner, the top-priority agent. In Pápai's
  hierarchical exchange (§1) each vacant good can have its own owner. The counterexample needs the pool split between
  two owners, so that each holds one good of every danger pair. So the completion shape that k = 4 needs is the
  hierarchical-exchange one, several pool owners, and not AS99's single owner.
- *Suggested next target* (for the Hall-count angle): an exact count for free completions at the picks. Junk goes
  only to unfrozen agents, and no bundle may strictly contain a danger set. That is a list-colouring of the junk
  danger hypergraph by the unfrozen agents, with capacity side conditions. The target is then whether one chain
  restores the colouring.

## Status at the end of burst 3 (OC₁-E and OC₁-ED are refuted with OC₁ in burst 4)

**Refuted in burst 3.** Conjectures OC₁-H (the chain's head absorbs) and OC₁-HD (the same with the dangerous-rotation
shape) fail at n = 6, m = 10 (`attempts/k4-ttc-head-owner.md`).
- The counterexample was found by the adversarial climb `head_bign_climb.py` and replayed independently by
  `refute_head.py`, which shares no code with the rest and uses brute force from the raw EFX₀ definition.
- Two agents end without a pick. The head of every repairing chain is one of them, and it receives a pick the other
  values, so it cannot also take the junk.
- Plain OC₁ holds there.
- At n ≤ 5 the head absorbed on all 2,310 distinct hard starts. Such instances are rare among small cores.

**What survives.**
- **Conjecture OC₁-E** (§8): the absorber is one of the chain's two endpoints, x₀ or the head x_t. Neither alone
  suffices: x₀ fails at dich3 (n = 3, m = 7; `attempts/k4-ttc-x0-owner.md`), and the head fails at the n = 6 instance.
  These are LB⁺'s two owners: Theorem A's r (the end) and Theorem B's k (the start).
- **Conjecture OC₁-ED** (§10) adds the shape:
  - x₀ is a dangerous agent;
  - the middle agents take exactly their predecessor's pick (pure want arrows);
  - only the head may add junk.

  It holds on every start tested: 2,310 distinct hard starts with n ≤ 5, 264 at k = 3, 103 at n = 6–9, and the two
  counterexamples to OC₁-H. Adversarial climbs at n = 3, 4, 5 found nothing. The climb at n = 6–8 with the endpoint
  objective is running (`head_bign_climb_ends_6_8.log`).
- **At k = 3** an even stronger shape holds on all 264 distinct hard starts (n = 5, 6). No agent but x₀ takes junk, x₀'s
  set is minimal, and the head is unwanted and absorbs. That is Draft and Exchange's chain lemma followed by the
  chain's end finishing. This is a concrete target for the k = 3 → k = 4 angle (§10).
- **Conjecture MDP∃** (§7) is unaffected.
- **A pointer argument** (§11) is the TTC proof skeleton:
  - Lemma T4, a corollary of GDT: at a hard start every unwanted owner candidate points at a frozen agent valuing its
    junk plus the owner's pick above its own;
  - a fixed point of "owner → dangerous agent ⇝ owner" is an OC₁-ED chain.

  It repairs on all 215 k = 3 hard starts and on 97% (2,238 of 2,310) of the k = 4 ones. The remaining 3% need a
  wanted head, or a head that takes junk.

**Earlier bursts:**
- Lemmas T1–T3 (§2, §9) are proved.
- No fixed TTC rule picks the chain (§3–§5), and the candidate TTC₂ fails on about 3% of the hard starts.
- Local validity is neither necessary nor sufficient (§6).
- The every-form of MDP fails at r617 (§7).

## Status of burst 1

**Proved (short written proofs, §2):**
- *Lemma T1:* with unit demand, no trade of TTC or YRMH-IGYT changes the serial-dictatorship picks. So every repair
  needs a set demand.
- *Lemma T2:* the improving chains and rings of `k4/sdc.md` §29 (with every passed base inside its receiver's relevant
  goods) are exactly the executed request paths and loops of YRMH-IGYT with set requests.
- Lemma 1 of `k4/sdc.md` §2 is Abraham et al.'s characterization of Pareto-optimal matchings, applied to the
  favourite-good matching F(X). Draft and Exchange's Improvement Lemma is Gale's pointer argument with set demands.

**Conjecture OC₁-H (new in burst 1; refuted in burst 3 at n = 6, see above; §8).** The pool belongs to the chain's head: from every order,
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

## 8. The pool belongs to the head? Conjecture OC₁-H (refuted at n = 6) and OC₁-E

**Refuted at n = 6, m = 10** (burst 3; `attempts/k4-ttc-head-owner.md`, `refute_head.py`, `refute_head.log`). The
surviving form is **Conjecture OC₁-E**: the absorber is x₀ or the head x_t. The evidence below for OC₁-H is also
evidence for OC₁-E. At n = 6 only x₀ (or an agent off the chain) absorbs, and at dich3 only the head does.

**Conjecture OC₁-H (as first stated).** In every instance with at most four relevant goods per agent, for every
order π:
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
- *n = 6–9* (`head_bign.py`, `head_bign.log`; lazy chain enumeration, stopping at the first head-absorbed repair, 120 s
  per start): random instances from `k4/sdc/oc1_bign.py`'s generator (2,000, 12 orders each) give 50, 18, 11 and 14
  distinct hard starts at n = 6, 7, 8, 9; the logged instances with n = 6, 7 (57) give 10. **The head absorbs in
  every one**, with no timeout. Random instances of this size are easy, so this is weak evidence.

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
- *P1 already fails at k = 3.* The coordinator reports this from the charity session (`claude/kgen-charity`): n = 4,
  m = 7, every agent values exactly 3 goods. The coordinator verified it with its own brute force,
  `k4/sdc/p1_k3_verify.py` on its branch, which I have not re-run. So value-monotone stuck states are not what
  separates k = 4 from k = 3, and the KQW analogy above is about multi-unit demand in general, not about k = 4.

## 10. The shape of the repair: Conjecture OC₁-HD (refuted at n = 6) and OC₁-ED

`chain_shape.py`, `chain_shape.log`.
- *Features recorded.* For every distinct hard start and every head-absorbed repairing chain (every description of
  every improving chain with t ≥ 1 whose result has a one-absorber completion with absorber x_t):
  - D0: x₀ dangerous at the start;
  - PJ: x₀ takes junk only;
  - NJH: x₁, …, x_{t−1} take no junk;
  - NJ: no agent but x₀ takes junk;
  - UH: the head is unwanted at the start;
  - M0: x₀'s new bundle is inclusion-minimal improving;
  - T1: t = 1;
  - LAST: the head is the last agent of some order giving these picks.
- *Table.* The number of hard starts having such a chain with each conjunction:

| data | hard starts | D0+NJH | D0+NJH+M0 | D0+NJH+UH | D0+NJ | D0+PJ+NJH | D0+NJH+M0+T1 | LAST |
|---|---|---|---|---|---|---|---|---|
| special | 16 | 16 | 16 | 14 | 14 | 11 | 12 | 15 |
| dichotomy failures | 2 | 2 | 2 | 2 | 2 | 1 | 2 | 2 |
| screen | 194 | 194 | 190 | 177 | 179 | 121 | 151 | 187 |
| suite | 196 | 196 | 192 | 179 | 181 | 132 | 152 | 189 |
| random cores n ≤ 3 | 293 | 293 | 293 | 293 | 293 | 212 | 284 | 293 |
| random cores n = 4 | 215 | 215 | 215 | 215 | 215 | 180 | 202 | 215 |
| random cores n = 5 | 30 | 30 | 30 | 30 | 30 | 28 | 28 | 30 |
| logged hard profiles (n ≤ 5) | 1,364 | 1,364 | 1,364 | 1,342 | 1,347 | 896 | 1,134 | 1,353 |
| **total** | **2,310** | **2,310** | 2,302 | 2,252 | 2,261 | 1,581 | 1,965 | 2,284 |

**OC₁-HD is refuted** at n = 6 with OC₁-H (burst 3). **Conjecture OC₁-ED** keeps its shape and lets the absorber be
either endpoint, x₀ or x_t. On the two n = 6 counterexamples the repairing chains (0, 4) and (1, 4) have this shape
(t = 1, x₀ dangerous) with x₀ absorbing.
- *k = 3* (`chain_shape_k3.log`): on 600 + 3,000 random profiles of the n = 5 cores and 600 of the n = 6 cores, all
  264 distinct hard starts have a head-absorbed repairing chain of the stronger shape D0+NJ+M0+UH. There only x₀ takes
  junk, its set is minimal, and the head is unwanted. That is Draft and Exchange's chain lemma (x takes its pair; its
  top passes along the wanters to an unwanted agent) followed by finishing at the chain's end.
- *Prescribing the head fails* (`head_rule.py`, `head_rule.log`):
  - the last agent of π is a working head on 576 of the 662 screen orders and on 355 of the 403 k = 3 orders;
  - on 30 screen orders every working head is a frozen agent.

**Conjecture OC₁-HD (as first stated).** For every order π whose picks Y have no one-absorber completion, there are:
- a *dangerous* agent k (frozen in Y and valuing some junk good);
- distinct agents k = x₀, x₁, …, x_t (t ≥ 1) such that each x_i with 1 ≤ i < t wants Y_{x_{i−1}} (so x₀, …, x_{t−2}
  are frozen);
- sets H₀ ⊆ (J ∪ {Y_{x_t}}) ∩ R_k with v_k(H₀) > v_k(Y_k), and H_t ⊆ J ∖ H₀ with
  v_{x_t}({Y_{x_{t−1}}} ∪ H_t) > v_{x_t}(Y_{x_t});

such that the following state has a one-absorber completion in which x_t is the absorber:
- k takes H₀;
- each x_i (1 ≤ i < t) takes Y_{x_{i−1}};
- x_t takes {Y_{x_{t−1}}} ∪ H_t;
- the rest of Y_{x_t} becomes junk.

**What the shape says.**
- In the housing market of §2, the head x_t (top priority) requests the pick of x_{t−1}, possibly with junk. Each
  x_i in turn requests the pick it wants. The dangerous agent k makes a *pool request* (its danger set, or part of it
  with the head's pick). The head then owns the rest of the pool. This is LB⁺'s Theorem B shape (one rotation, then
  one owner) with the owner at the rotation's end. It is also Draft and Exchange's chain lemma, where the frozen agent
  takes its pair and passes its top along the wanters, with the k = 3 pair replaced by any danger set and the owner
  placed at the end.
- *Compared with LB₄ʳ's improving rotation* (`k4/sdc.md` §29: x₀ frozen, x₁, …, x_{t−1} frozen, no junk for
  x_i, i ≥ 1), OC₁-HD adds three things:
  - x₀ must be dangerous, not just frozen;
  - the head (= owner) may take junk;
  - x₀ may take the head's pick.

  §29 found that LB₄ʳ's improving rotations with its own output fail from some orders (6 special, 26 screen starts).
  The table shows where the extra freedom is used. On 49 starts every repair of this shape gives the head junk (D0+NJ
  fails). On 729 starts every repair of this shape has x₀ take the head's pick (D0+PJ+NJH fails).
- *What a proof needs, in LB⁺'s format:*
  - a Theorem A for a prescribed owner o: when do picks have a one-absorber completion with absorber o (the Hall-type
    count of the `oc1_hall` angle, with the owner fixed);
  - a Theorem B: if the count fails for every unwanted o, some dangerous agent's rotation to some o repairs it for o.

  The TTC structure suggests the pointer argument for the second part:
  - each candidate owner o whose count fails points, through its violated condition, to a dangerous agent whose
    danger set causes the failure;
  - that agent's pick has a want-path to some owner;
  - Gale's argument closes it.

**Adversarial climbs.**
- *n = 3, 4, 5* (`head_climb.py … hd`; logs `head_climb_hd_n3.log` with 20 rounds × 3,000 steps,
  `head_climb_hd_n4.log` with 12 × 1,000, `head_climb_hd_n5.log` with 4 × 150): they minimize the number of OC₁-HD
  chains at the hardest start, and none goes below one.
- *n = 6–8* (`head_bign_climb.py`, `head_bign_climb_6_8.log`, stopped after 7 of 12 runs): found the two OC₁-HD
  counterexamples above.
- *The endpoint objective* (OC₁-ED, `head_bign_climb.py … ends`, `head_bign_climb_ends_6_8.log`) is running at the
  end of burst 3.

## 11. A pointer argument from Lemma GDT, and where it stops

**Lemma T4 (every candidate owner points at a dangerous agent; corollary of Lemma GDT, `k4/sdc.md` §30).** Let
Y = SD(π) with junk J, and let o be an unwanted agent with a pick y_o.
- If every frozen agent x satisfies v_x((J ∪ {y_o}) ∩ R_x) ≤ v_x(Y_x), then Y has a one-absorber completion with
  owner o.
- So if Y has no one-absorber completion, then for every unwanted o with a pick the set
  S_o = {x frozen : v_x((J ∪ {y_o}) ∩ R_x) > v_x(Y_x)} is nonempty. Each x ∈ S_o has an improving set inside
  (J ∪ {y_o}) ∩ R_x.

*Proof.* At serial-dictatorship picks the hypotheses of Lemma GDT other than (G4) hold:
- (G1) and (G3) hold because there are no pairs;
- (G2) holds because a junk good is worth less to each of its valuers than its pick ((I2); an agent without a pick
  values no junk);
- (G5) holds because o is unwanted;
- (G4) is the displayed condition, with B_o = {y_o}.

GDT gives the completion, in which only o receives several junk goods. ∎

The computation also treats unwanted agents without a pick as owners (y_o = none), for which GDT is not stated. S_o
was nonempty for every unwanted agent on every hard start (column (a) below).

**The pointer map.** Each unwanted o points to some x ∈ S_o. From x, want arrows (x_{i+1} wants Y_{x_i}) lead to an
unwanted agent, because the want graph is acyclic and points backwards in π. Gale's argument closes a cycle of
"owner → dangerous agent ⇝ owner" steps.
- A *fixed point* (o, x, a want path from x ending at o) is exactly a chain of OC₁-ED's shape with head o and
  H₀ ⊆ (J ∪ {y_o}) ∩ R_x.
- A longer cycle is a ring with several pool requests, the analogue of Draft and Exchange's rings with several pair
  arrows (`paper/k3-simple`, Appendix "How large must a ring be?").

`pointer.py`, `pointer.log`; distinct hard starts:

| data | hard starts | (a) every S_o ≠ ∅ | (b) a fixed point exists | (c) a fixed-point chain repairs (absorber o or x) | (c-head) … absorber o | (d) every fixed point repairs |
|---|---|---|---|---|---|---|
| special | 16 | 16 | 15 | 13 | 13 | 12 |
| dichotomy failures | 2 | 2 | 2 | 2 | 2 | 2 |
| screen | 194 | 194 | 189 | 173 | 162 | 144 |
| suite | 196 | 196 | 191 | 175 | 163 | 140 |
| random cores n ≤ 3 | 293 | 293 | 293 | 293 | 293 | 272 |
| random cores n = 4 | 215 | 215 | 215 | 215 | 215 | 196 |
| random cores n = 5 | 30 | 30 | 30 | 30 | 30 | 28 |
| logged hard profiles | 1,364 | 1,364 | 1,359 | 1,337 | 1,335 | 1,266 |
| **total, k = 4** | **2,310** | **2,310** | 2,294 | 2,238 | 2,213 | 2,060 |
| k = 3, n = 5 cores (3,000 profiles) | 215 | 215 | **215** | **215** | **215** | 210 |

- *(a)* is Lemma T4 and holds everywhere, a consistency check of GDT on 2,525 states.
- *At k = 3, a fixed point always exists and always repairs with the head absorbing* (215 of 215). A k = 3 proof of
  OC₁ along these lines needs two statements:
  - **(P1₃)** some fixed point exists. Gale's cycle must close in one step, presumably by an R1 / block argument like
    LB⁺'s (A3)–(A4);
  - **(P2₃)** its chain repairs. GDT's (G4) must hold after the chain for the remaining frozen agents with the head as
    owner, which is where Draft and Exchange's finishing count |H_o| ≤ |F| − 1 enters.

  This is offered to the k = 3 → k = 4 angle (`claude/k4-k3-oc1`).
- *At k = 4 the pointer argument stops in two places:*
  - *no fixed point* (16 of 2,310; e.g. Q2 with picks (3, 7, 5, 4), and two c4one-one-rotation instances): every
    repairing chain has a head that needs junk to improve, or the cycle has length ≥ 2;
  - *a fixed point, but no repairing one* (56 more; e.g. T3 with picks (0, 4, 1), adaptive-p1): the repairing head is
    a *wanted* agent, not an unwanted one.

  These are the cases a k = 4 proof must handle beyond the TTC pointer argument. They are exactly where OC₁-ED's
  extra freedom is used: the head takes junk, or the head is frozen (§10's D0+NJ and D0+NJH+UH columns).

## 13. OC₁ is refuted, also on cores

`attempts/k4-ttc-oc1-counterexample.md` has the core counterexample (n = 5, m = 9), the counting argument, the
replays and the history. What follows is about the first, non-core instances at n = 6 found by the climb. The core
was built by hand from their counting argument (`oc1_core_candidate.json`, `refute_oc1_core.log`).
- *Found by:* `head_bign_climb.py … ends seeded`, a climb on values and incidences started from the OC₁-H
  counterexample with the OC₁-ED objective. When a start had no OC₁-ED chain, the climb also checked plain OC₁ and
  found it false.
- *Instances:* 84 distinct instances (`oc1_counterexamples.json`), all at n = 6, m = 10, all with two agents without a
  pick.
- *Checks:*
  - SAT recheck: all 84 (`oc1_false_check.py`, `oc1_false_check.log`);
  - independent brute-force replay: 7 of them (`refute_oc1.py`, `refute_oc1.log`).
- *What still holds there:* every one of the 84 has a free completion of the picks, and a completion in which at most
  one agent *holding a pick* absorbs (the two pickless agents absorb).

Consequences for this note:
- OC₁-E and OC₁-ED (§8, §10) are refuted with OC₁, also on cores.
- The pointer argument of §11 concerns one-absorber completions, so it fails with them.
- The k = 3 observations of §10 and §11 were made on k = 3 cores and are unaffected.
- Whether OC₁ holds on all k = 3 cores is not settled by this counterexample: it has 4-good agents, and the k = 3
  family is not a core.

What survives, as targets:
- **OC** (free completion; `k4/sdc.md` §29).
- **OC₁ᵖ:** OC₁ with absorbers counted only among agents holding a pick. A k = 4 analogue of Draft and Exchange's rule
  that a free agent holding nothing can always finish.
- **MDP∃** (§7), which is about free completions.

### Lemma T5: at maximum-matching picks, pickless agents freeze only safe agents

This is the matching-theory reason every counterexample of this section starves agents.

**Lemma T5.** Let Y = SD(π) be a maximum matching of agents to relevant goods, J the unpicked goods, and u an agent
with Y_u = none. Call x *reachable from u* if there are distinct agents x₁, …, x_t = x with Y_{x₁} ∈ R_u and
Y_{x_{j+1}} ∈ R_{x_j} for j < t. Then:
- (a) u values no good of J;
- (b) no agent reachable from u values a good of J.

In particular, every agent that u wants (every agent whose pick u values) values no junk. So it is not dangerous, and
its danger sets contain no junk.

*Proof.*
- (a) If u valued g ∈ J, adding (u, g) to Y would give a larger matching.
- (b) If x_t valued g ∈ J, the alternating path u – Y_{x₁} – x₁ – Y_{x₂} – … – x_t – g would augment Y: give
  Y_{x₁} to u, each Y_{x_{j+1}} to x_j, and g to x_t. All these goods are relevant to their new holders. That gives a
  larger matching, which contradicts maximality (Berge). ∎

*Consequences.*
- At maximum-matching picks, a dangerous frozen agent is wanted only by agents that hold a pick. The pickless agents
  value no junk, and junk placed with them threatens nobody whom they freeze.
- In the counterexamples of this section, the pickless agents freeze the dangerous agents directly, which needs
  augmenting paths, i.e. picks that match ν − 2 agents (`order_classes.log`).
- A counterexample to OC₁^max must therefore come from frozen agents whose wanters hold picks. By (b) this is the
  only route even when ν < n, which is the coordinator's "ν = n is the hard case".

## 14. OC₁^max: the n = 6 sweep, the refutation at n = 4, and why two moves are needed

### 14.1 The n = 6 sweep (evidence only)

`oc1max_n6.py` tests OC₁^max on the n = 6 core hypergraphs (`k4/search4.cores`, nauty, one per isomorphism class)
with ν = 6.
- *Profiles:* 3 random strict profiles each, from `search4.domain`, which lists every strict balanced subset ranking
  of an agent; 400 of 400 sampled profiles pass `is_core4`.
- *Orders:* all 720.
- *A start* is a distinct serial-dictatorship outcome that matches all six agents.

| n4 | hypergraphs | maximum starts | needing a move | failures | log |
|---|---|---|---|---|---|
| 2 | all 119,108 with ν = 6 (of 119,283) | 1,812,773 | 37,620 | 0 | `oc1max_n6_n4_2.log` |
| 3–6 | stride 10: stopped at 28,500 of 141,559 when OC₁^max fell at n = 4 (§14.2) | — | — | none printed | `oc1max_n6_n4_3to6_stride10_stopped.log` |

Repairing-move counts at the n4 = 2 starts that need a move: 1: 2,825; 2: 4,348; 3: 5,529; 4: 2,000; ≥ 5: 22,918.

**The hardest starts** (`oc1max_hard.py`, `oc1max_n6_n4_2_hardest.log`; 8 printed, each with exactly one repairing
move, checked by brute force and SAT) all have one shape:
- m = n + 2, five frozen agents and a single receiver r;
- two dangerous agents, each valuing one private junk good;
- *no completion at all:* frozen agents take no junk, so both junk goods go to r, and a dangerous d has
  v_d(Y_r) + v_d(j_d) > v_d(Y_d);
- *the only repair is the swap (d, r):* d takes {j_d, Y_r}, and r, which freezes d, takes Y_d. Then d holds two goods,
  is no longer frozen, and absorbs the other junk good.

**The shape of the repairs** (`oc1max_paths.py`, `oc1max_paths_n6_sample.log`; 238 hypergraphs × 3 profiles, 55
starts needing a move):
- the shortest repairing move has length 1 (7 starts), 2 (24), 3 (15), 4 (7) or 5 (2), so the swap is not always
  enough;
- *canonical repair:* every one of the 55 is repaired by an addition or by a chain whose x₀ is dangerous and whose x₁
  wants x₀'s pick;
- §11's fixed point (a pure want path from a dangerous x₀ to a receiver) repairs 54 of 55. The exception needs junk
  paid to the frozen end of a five-agent cycle.

### 14.2 OC₁^max fails at n = 4 (found by the certifier, `compute/k4-oc1max-cert`)

The certifier's ordinal CEGAR (`k4/oc1cert/cegar.py` on that branch) runs over every strict profile. It finds 11 of
the 1,002 n = 4 core hypergraphs with a profile and a perfect-matching start where no one move gives a completion,
free or one-absorber (`results/k4_oc1max/oc1max_cex_n4.json` there).

**Checked here:**
- `refute_oc1.py` (brute force, no SAT, no shared code) on instance 0;
- `oc1max_cex_n4.py` on all 11: SAT and brute-force completions agree, all 11 are strict connected cores with ν = 4,
  and all are in the K4.MC2 class (`oc1max_cex_n4_ttc.log`);
- *rarity:* 0 of 3,000 random strict profiles of instance 0's hypergraph fail. That is why the random sweeps missed it.

**Instance 0 in TTC terms.**
- *The instance:* sets {g0, g1, g2, g5}, {g1, g2, g5, g6}, {g3, g4, g5, g6}, {g3, g4, g6}; values (2, 10, 4, 7),
  (10, 3, 4, 8), (3, 5, 6, 7), (3, 2, 4).
- *The start:* order (0, 3, 2, 1), picks (g1, g2, g5, g6), junk {g0, g3, g4}.
- *Wants* (i → j: i values Y_j above Y_i): 1 → 0, 2, 3 and 2 → 3. So agents 0, 2 and 3 are frozen.
- *The lone receiver, agent 1,* is starved: it holds its worst good, wants every other pick, and values no junk.
- *Why the picks fail:* all the junk must go to agent 1, and then agent 2 envies that bundle minus g0
  (g3 + g4 = 8 > 6).
- *The targets:* of the 14 complete EFX₀ allocations, 6 value-dominate the picks. In all 6, agent 1 holds g1, agent 0
  holds {g2, g5} (plus g0), and the danger pair {g3, g4} is the whole bundle of agent 2 or 3.
- *Agent 0's demand is complementary:* its improving bundles without g1 are {g2, g5} = 11 and {g0, g2, g5} = 13. Both
  need the picks of two other owners, agents 1 and 2.
- *Why one move fails:*
  - In a move, x₀ takes junk plus part of one base B_{x_t}, and every other participant takes exactly its
    predecessor's base plus junk.
  - So agent 0 could collect the second pick only as junk released by x_t in the completion. Its own step would then
    have to improve with one pick plus junk, which it cannot: {g5, g0} = 9 and {g2, g0} = 6, both below 10.
  - In TTC language: a cycle serves unit demands, and this exchange is a tree.
- *The two moves:*
  1. The danger pair becomes a base: one of the chains (2,1), (3,1), (3,2), (3,2,1). The dangerous agent takes
     {g3, g4}, its pick moves along a want path toward agent 1, and g2 (or g5) drops into the pool.
  2. Then the cycle (0,1), or (0,1,2) after (3,1): agent 1 takes its top g1, and agent 0 takes the bundle of agent 1's
     new base and the pool good.

**All 11** (`oc1max_cex_n4_ttc.log`):
- each has a single receiver;
- in every target, some agent holds the picks of two other agents, and Lemma T6 (below) certifies that one move
  cannot reach any target;
- OC₂^max holds;
- every repairing first move is a chain whose x₀ is dangerous and whose x₁ wants x₀'s pick;
- every *minimal pointer fixed point* (§11's fixed point, with x₀ taking an inclusion-minimal improving set of junk as
  its new base and nothing from a base) is a good first move: 34 of 34, and one exists in each instance;
- the second move is a fixed point in none; it is canonical (dangerous x₀, x₁ wants its pick) in 23 of the 34.

### Lemma T6: one move serves unit demands

**Lemma T6.** Let Y be a serial-dictatorship start in which every agent holds exactly one pick (a perfect matching),
with junk J. Let X be a complete allocation obtained by one improving move of `de_free` (an addition, a chain or a
ring), followed by any completion that keeps the new bases (free, any number of absorbers). Then:
- (a) X value-dominates Y: v_i(X_i) ≥ v_i(Y_i) for every agent i;
- (b) every X_i contains at most two picks of other agents;
- (c) if X_i contains two picks of other agents, then the move is a chain (x₀, …, x_t), i = x_j for some j ≥ 1, and
  X_i ∋ Y_{x_t}. Moreover i's step x_j took Y_{x_{j−1}} together with junk H_j ⊆ J ∩ R_i, with
  v_i(Y_{x_{j−1}}) + v_i(H_j) > v_i(Y_i).

*Proof.*
- (a) Every agent in the move strictly improves its base; the others keep theirs. The completion only adds goods, and
  values are nonnegative.
- (b) and (c): count the other agents' picks an agent can end up with.
  - *A ring:* each member takes exactly one other base B_{w_s} = {Y_{w_s}} plus junk. No pick is released, and the
    completion hands out only goods of J.
  - *An addition:* no base changes hands.
  - *A chain:*
    - x₀ takes junk and possibly Y_{x_t}, the only good of B_{x_t};
    - each x_j (j ≥ 1) takes exactly Y_{x_{j−1}} plus junk;
    - the only pick that can enter the pool is Y_{x_t}, when x₀ does not take it.
  - So the completion can hand at most one pick, Y_{x_t}, to anyone. An agent therefore holds two other agents' picks
    only if it is some x_j with j ≥ 1, holding Y_{x_{j−1}}, and also receives Y_{x_t} from the pool. Its step must have
    improved its base: v_i(Y_{x_{j−1}} + H_j) > v_i(Y_i). ∎

**Corollary (a certificate that one move fails).** Let 𝒯 be the set of complete EFX₀ allocations that value-dominate
Y. Suppose every T ∈ 𝒯 has an agent i such that either
- T_i contains three or more other agents' picks, or
- T_i contains two, P and Q, with v_i(P) + v_i(J ∩ R_i) ≤ v_i(Y_i) and v_i(Q) + v_i(J ∩ R_i) ≤ v_i(Y_i).

Then no single move followed by any completion gives an EFX₀ allocation. By (a), such an allocation would lie in 𝒯;
by (b) and (c), it would avoid the blocked agent's configuration.

**All 11 n = 4 counterexamples satisfy the corollary**, and each through a single agent: the agent whose
improving bundles are complementary across two owners (`oc1max_cex_n4_ttc.log`, "Lemma T6 blocks"). For instance 0,
this is agent 0, with {g2, g5} in every target and 7 + 2, 4 + 2 ≤ 10.

So, given the list of targets (brute force over the n^m allocations), the failure of OC^max, and hence of OC₁^max,
has a short human-checkable proof. The obstruction is exactly the tree-shaped exchange: TTC cycles cannot serve a
demand for two other agents' houses.

### 14.3 A TTC rule for two moves, and where it stops

**Rule FP+1^max.** At a maximum-matching start: either one move gives a one-absorber completion, or some minimal
pointer fixed point exists, and after it, the bases have a one-absorber completion or one more move gives one.
- Every move this rule uses is defined by pointers: the dangerous agent points at a minimal junk set, and each agent on
  the want path points at its predecessor's pick.
- FP+1^max implies OC₂^max.

**Evidence** (`oc2max_fp.py`):
- the 11 instances: FP+1^max holds for every fixed point, not just some;
- a walk over types around them (`walk`, 11 × 300 steps, `oc2max_walk_n4_short.log`): 97 OC₁^max failures among
  3,064 distinct profiles, and FP+1^max holds for every fixed point at all 97;
- a longer walk (11 × 5,000 steps, `oc2max_walk_n4.log`): 1,174 OC₁^max failures among 48,504 distinct profiles.
  At every one, a minimal fixed point exists, every minimal fixed point is a good first move, and OC₂^max holds.

**It fails at n = 5, outside the K4.MC2 class** (`attempts/k4-ttc-fp-plus-one.md`).
- *How it was found:* `oc2max_fp.py grow` adds an agent to each n = 4 counterexample and walks over types and
  incidences (`oc2max_grow_n5_short.log`: 17 failures among 1,895 instances; with `mc2`,
  `oc2max_grow_n5_mc2_short.log`: none among 1,819).
- *What it found:* strict cores with ν = 5 where OC₁^max fails, the free form too (`oc1max_cex_n5_two_private.json`;
  `refute_oc1max_cex_n5.log`, brute force), and where no minimal fixed point exists. The added agent has two private
  goods, so these cores are not in the K4.MC2 class.
- *The instance:* sets {g0, g4, g5, g6}, {g2, g3, g4, g6}, {g0, g1, g5, g6}, {g2, g4, g5, g6}, {g0, g1, g7, g8};
  values (3, 2, 10, 6), (4, 1, 6, 8), (2, 8, 5, 4), (5, 4, 8, 2), (7, 8, 2, 4). Order (1, 3, 4, 2, 0), picks
  (g4, g6, g0, g5, g1), junk {g2, g3, g7, g8}.
- *Its structure:*
  - one receiver (agent 0);
  - the dangerous agents 1, 3 and 4 cannot improve with junk alone ({g2, g3} = 5 and g2 = 5 against 8;
    {g7, g8} = 6 against 8);
  - so the pointer map has no fixed point.
- *The two moves:* in the first, a dangerous agent takes its danger junk *as an internal member of the chain*. In
  (2, 4), agent 4 takes g0 plus its private pair {g7, g8} (13 > 8), and agent 2 takes agent 4's g1. In (0, 1),
  agent 1 takes g4 plus g2. The repairs are (2, 4) followed by (0, 1) or (0, 3), and (0, 1) or (0, 3) (also
  (0, 1, 2), (0, 3, 2)) followed by a chain through 4.
- *Unlike n = 4,* Lemma T6 blocks none of the 41 targets (`oc1max_cex_n5_ttc.log`), and some targets have no agent
  holding two other agents' picks. Here a single move can reach a target's exchange shape, and the obstruction is
  about values.

**What survives on all data so far: danger absorption is necessary.**
- Among OC₁^max failures, every good first move absorbs danger: some agent that is dangerous at the start takes junk
  it values into its new base, as x₀, as an internal member, or by an addition.
- This held at all 1,174 n = 4 walk failures and all 17 grown n = 5 failures. But some danger-absorbing first move is
  always bad.
- So the TTC rule must say *which* danger to absorb first. At n = 4 the minimal fixed point says it.

**One receiver.** Every OC₁^max failure tested has exactly one receiver (one unfrozen agent): 97 of 97 in the short
n = 4 walk and 17 of 17 at n = 5 (the `receivers` lines of the `_short` logs). The 11 instances and the n = 6 hardest
starts are the same. At every start with two receivers, one move gave a completion (151 + 140 starts).
- *Conjecture R2 (evidence only):* at a maximum-matching start with at least two receivers, OC₁^max holds. The
  precise statement, a proof plan and more evidence are in §14.6.
- R2 would confine OC₁^max failures to the one-receiver regime. There, every completion keeping the bases puts all the
  junk with a single agent (Lemma 2(a): frozen agents take none), so the picks extend iff that one bundle is safe.
- A proof of OC₂^max could then split: two receivers (one move, R2), or one receiver (the danger set must become a
  base, as in §14.2).

### 14.4 Longer runs (`oc2max_fp.py`)

- `oc2max_grow_n5.log` (44 grown walks × 1,000 steps, no `mc2`): 36,615 distinct n = 5 instances and 116,196 hard
  maximum starts, with no OC₁^max failure. 4,027 of those starts have two receivers. The 17 failures of the short run
  came from one lineage: failures cluster.
- `oc2max_grow_n5_mc2.log` (the same walk restricted to the K4.MC2 class): 36,100 instances and 104,453 hard starts
  (1,251 with two receivers), with no OC₁^max failure.
- `oc2max_grow_n6.log` (two agents added, 22 walks × 500 steps): 9,368 n = 6 instances and 33,493 hard starts
  (3,840 with two receivers, 93 with three), with no OC₁^max failure.
- Running at the end of burst 7: `oc2max_hunt_n5.log` (`hunt keep`, scored by the fewest good first moves).

*A failed design:* seeds in which the agent holding the receiver's top good needs the picks of three other owners
(values 20; 8, 7, 6), meant to force three moves (`three_owner_seeds.json`; `grow … 300 21 0 1 hunt keep`,
`oc2max_hunt_three_owner.log`). They gave no OC₁^max failure at all in 4,109 instances: a three-owner demand alone does
not produce the one-receiver obstruction.

### 14.5 Hand-built ladders for three moves, and why they collapse

**The idea.** Give the complementary agent c = {T, j, Pa, Pb} a demand {Pa, Pb} on the picks of two *dangerous*
agents a and b, neither of them the receiver r. Each pick can enter the pool only as the released end of its own chain.
Then c's cycle (c, r), with r taking T and c taking {Pa, Pb, j} from the pool, would be move three.

It cannot be done with three owners instead: a junk-free complementary agent is never the bottleneck (§14.4).

`ladder.py`, `ladder.log`: three n = 6, m = 11 designs, each a strict MC2-class core with ν = 6, under one order.

| design | change | receivers at the start | least moves |
|---|---|---|---|
| ladder6 | r wants Pd, Pe | r, a, b | 0 (a and b are not wanted, so they absorb the junk) |
| ladder6b | r wants Pa, Pb instead | r | 1: after (a, r), a holds {u1, u2} = 8 > 7, so d is no longer wanted and splits the w-pair with r |
| ladder6c | e also wants Pd, so d stays frozen | r | 1: now (b, r) unfreezes e in the same way |

**Why they collapse.** Each move satisfies the agents whose wants it serves, and so unfreezes the agents they wanted,
which become new receivers.
- To keep the partner of a moved dangerous agent frozen, it needs a second wanter.
- The want graph at serial-dictatorship picks is acyclic (every wanter picks later), so the partners cannot want each
  other.
- With k = 4 every agent has at most three other goods to want with.

A three-move start has to defeat this twice. Whether degree counting at k = 4 forbids it is the question to settle;
exhaustive type search on these incidences was sent to sd-induct for its fixed-incidence CEGAR.

**R2⁺ is false.** R2 extended to states after one move would say: two or more receivers, then one more move
suffices. Among the first moves at OC₁^max failures, most bad moves leave two or more receivers (`oc2max_fp.py` counts
"first moves at OC₁^max failures"). Agents holding two or more goods count as unfrozen, but they can still be blocked,
for example a holder of another agent's exact danger set. So R2 is stated only at serial-dictatorship starts.

### 14.6 Conjecture R2 (owned here; leaf 5a of `k4/oc1_hall.md` §23.2)

**Setting.**
- A strict connected k = 4 core.
- Y is a *perfect* serial-dictatorship start: every agent holds exactly one pick y_i. Maximum-matching starts reduce
  to perfect ones by leaf 0 of the case tree (Lemma RED with Lemma MAX), so R2 is stated for perfect starts.
- J is the junk.
- *Frozen:* an agent j is frozen if some other agent i values y_j above y_i. F is the set of frozen agents.
- *Receivers:* U = N ∖ F, the pick holders that nobody values above their own pick.
- *Dangerous:* D ⊆ F, the frozen agents that value some junk good.

At the picks every base is a single good, so "frozen" is all there is: no agent holds another agent's exact danger set.
That kind of blocked holder exists only after a move, and it is why R2 does not extend to post-move states (R2⁺ is
false, §14.5).

**Conjecture R2.** If |U| ≥ 2, then Y has a one-absorber completion, or after one official move (an addition, chain
or ring of `de_free`) the bases have one.

**Strong form R2★ (what the data show).** If |U| ≥ 2 and Y has no one-absorber completion, then there is a canonical
chain (x₀, …, x_t) with:
- x₀ ∈ D;
- x₁ valuing y_{x₀} above y_{x₁};
- x_t = z ∈ U;

after which the junk has a completion that gives *every agent at most one junk good*, so no absorber is needed. On
the same data, that chain also repairs with z, with x₀, or with a receiver off the path as owner.

**Evidence** (`r2_shape.py`). In both data sets, at every hard start with |U| ≥ 2: R2 holds, R2★ holds, and some minimal
pointer fixed point of §11 repairs except on 6 and 5 starts.

| data | hard perfect starts | with \|U\| = 1 | with \|U\| ≥ 2 | log |
|---|---|---|---|---|
| random walk over types around the 11 n = 4 cores (11 × 300 steps) | 630 | 551 | 79 | `r2_shape_walk_n4.log` |
| n = 6 sweep sample (n4 = 2, 3, 4, stride 100, 9,162 hypergraphs, 1 profile) | 1,487 | 1,021 | 466 (441 with two, 25 with three) | `r2_shape_n6_sample.log` |

Together with §14.3 (every OC₁^max failure has |U| = 1): no failure of R2 is known at k = 4.

**k ≤ 4 is necessary.** At k = 5, PW5 (`claude/k4-ksens`, `k4/ksens.md` §1, a written proof) is a perfect start with
two receivers (the wanters w₁ and w₂) and no completion after any one chain.
- Three frozen agents share a pool D of four junk goods, every pair of which is dangerous.
- One repair uses two goods of D. The leftover pair still threatens the other two frozen agents, and the two receivers
  give only one slot.
- Lemma PL of that note is the k ≤ 4 count: a frozen agent with |R_x| ≤ 4 values at most three junk goods, so after
  it takes a junk danger set H (|H| ≥ 2) it values at most one more, worth less than its pick. The same holds for
  every agent that values two goods of H. At k = 4 the leftover of a shared pool is at most one good, and one slot
  takes it.

**Proved first step (Lemma R2-0).** At a perfect start, if |J| ≤ |U|, the picks have a completion in which every
agent receives at most one junk good.

*Proof.* Give the junk goods to distinct receivers.
- Bundles with one good are never strongly envied.
- Take a bundle {y_u, g} with u ∈ U and an agent i ≠ u. Removing g leaves y_u, and v_i(y_u) ≤ v_i(y_i) because u is
  unwanted. Removing y_u leaves g, and v_i(g) ≤ v_i(y_i) by (I2), since junk ranks below the pick for its valuers.
- Every agent's own bundle is worth at least its pick. ∎

So a hard start with |U| ≥ 2 has |J| ≥ |U| + 1 ≥ 3.

**Proof plan for R2** (the open steps are marked).
1. *A fixed point exists.* By Proposition T0 (case tree, leaf 2), every receiver z has a dangerous agent threatened by
   J ∪ {y_z}. Follow §11's pointer map on U: each z points to such an x, and want arrows from x lead back to some
   receiver. With |U| ≥ 2 the map has a fixed point (z, x, a want path from x to z), or a 2-cycle (z₁ → x₁ ⇝ z₂ →
   x₂ ⇝ z₁). **Open:** rule out the 2-cycle, or turn it into a ring (§11's "longer cycle").
2. *The chain.* x₀ = x takes a minimal danger set H₀ ⊆ (J ∪ {y_z}) ∩ R_x, and the want path carries y_x to z.
3. *Leftover danger.* By Lemma PL(b, c), x and every agent that shares two goods of H₀ have no junk danger set left.
   **Open:** the agents that share at most one good of H₀ (PL's "what PL does not cover"), and the released pick when
   z's pick is not in H₀.
4. *Slots.* The remaining receivers (|U| − 1 ≥ 1 of them, still unwanted after the chain), together with x₀ and the
   agents the chain unfroze, take the remaining junk one good each, as in Lemma R2-0. **Open:** the count
   |J ∖ H₀| ≤ available slots, presumably from Lemma M at the new bases (`k4/matching.md`), with its exposed-holder
   matching handling the frozen slots of Lemma 1.

R2★ says that step 4 needs no owner at all, so Lemma M's owner-free case, a pure matching of junk to safe agents,
should be the counting tool.

**The tool for step 4: Lemma M^c.** It is in `proof/k4-oc1max-multi`, `k4/oc1max_multi.md` §9, commit 3b69d07: a
written proof, not refereed, whose statement and claim I have read. It is an exact compensated matching condition for
completions of shape S^c:
- the owner o takes the rest;
- holders and frozen singles take at most one junk good each;
- multi-good agents take nothing.

Frozen slots are handled by enumerating F_s; for a fixed F_s the condition is a bipartite matching.

R2★'s completions are S^c completions whose owner (x₀ or z) receives at most one junk good beyond its base, that is,
|J ∖ H| ≤ 1. So step 4 is the statement that after the chain some (H, F_s) with |J ∖ H| ≤ 1 meets (C1)–(C3). The
counting argument must produce it: a Hall-type deficiency δ^c ≤ 0 from Lemma PL and the second receiver.

**No frozen slot is needed** (`r2_slots.py`): at every hard start with |U| ≥ 2, some R2★ chain has a completion in
which no agent frozen at the new state receives junk. That is F_s = ∅ in Lemma M^c, the plain matching case: 79/79 at
n = 4 (`r2_slots_walk_n4.log`) and 466/466 at n = 6 (`r2_slots_n6_sample.log`).
- In the first such completion found, the junk goes to unwanted single-good holders (940 goods at n = 6), to x₀ (410),
  to multi-good agents of the path (65), and to frozen singles (71) only in completions for which another chain exists
  without them.
- The new junk can outnumber the unwanted holders plus x₀, by up to 2. The path's multi-good agents then take the
  excess, so the count in step 4 has to include them.

## 12. Next steps

1. *OC₁-E / OC₁-ED at larger n.* Adversarial climbs at n = 6–8 with the endpoint objective:
   - `head_bign_climb_ends_6_8.log`: 12 runs × 400 steps, no failure;
   - `head_bign_climb_ends_6_8_long.log` (48 × 1,000) and `head_bign_climb_ends_seeded.log` (started from the OC₁-H
     counterexamples): running at the end of burst 3.

   The head-only objective broke OC₁-H within 7 runs, so the endpoint form survives a test that the head form did not.
2. *k = 3 (for the `k4-k3-oc1` angle).* Prove (P1₃) and (P2₃) of §11. Both hold on all 215 distinct hard starts
   tested (n = 5 cores; `pointer.log`).
   The fixed point should come from LB⁺'s block structure ((A3): exposed agents are block leaders), and the repair
   from Draft and Exchange's finishing count with the chain's end as the finisher.
3. *k = 4 beyond the pointer argument (§11).* Classify the 72 starts where no fixed-point chain repairs: a wanted
   head, or a head needing junk. Look for the second pointer that a Theorem B₄ would follow there, for instance from
   the head to the frozen agent wanting its pick, as in Draft and Exchange's want arrows.
4. *MDP∃ with a second extremal criterion* (fewest junk goods moved, least total gain), to rule out the r617 pattern
   of two independent pool swaps.
5. *The core of a pool-owned market* (Lemma T3's remark): not pursued. With the pool owned by an agent, individual
   rationality would force that agent to receive at least its pick plus all the junk it values. That fails as soon
   as another agent's single junk good is one the owner values, which is the typical protective slot. The core of
   such a market looks like the wrong notion; value domination (MD) is the IR invariant that matters.
