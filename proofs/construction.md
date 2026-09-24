# The large bundle (plan Step 2): structure, a necessary condition, and construction LB

Workstream `compute/large-bundle`. Notation as in PROMPT.md §3: a core has n agents and m goods; agent i values exactly three goods, ranked a_i > b_i > c_i, and is balanced (a_i < b_i + c_i). A good is *alone* if it is the only good in its bundle. The slack is σ = 2n − m (so β = σ + 1). A good is a *contested top* if it is the top of at least two agents (its *claimants*). "C2" means an allocation in which every bundle has at most two goods.

Everything in §1–§3 is proved here by hand. The computations behind §4–§5 are in `results/` (logs listed in each section), made with `src/construct.py`, `src/construct.c`, `src/construct_run.py` and `src/large_bundle.py`.

## 1. The smallest core that needs a large bundle: n = 3, m = 5

This is core H3 of `proofs/counterexamples.md` (X1), found independently in Step 0 (`src/c2_small.py`). It is repeated here with the large-bundle allocation, because its shape recurs in §5. Three agents value goods 0 and 1, and each has one private good p_0, p_1, p_2. All three rank (0, 1, own private good). This is the core `[[0, 1, 2], [0, 1, 3], [0, 1, 4]]` with profile (0, 0, 0).

**Claim.** No EFX₀ allocation has all bundles of at most two goods. The allocation {0}, {1}, {p_0, p_1, p_2} (to agents A, B, C in any order) is EFX₀.

*Proof.* Five goods in three bundles of at most two goods means bundle sizes 2, 2, 1, so exactly one good is alone. Apply L5 to each agent that does not hold good 0: case T is impossible, and case C needs both 0 and 1 alone, and so does E. So such an agent is safe only by P (it holds 1 and its private good) or by B (it holds 1, and 0 is alone). Two agents do not hold 0, and each of them must hold good 1. That is impossible.
For the allocation: agent A holds its top 0, and its b = 1 and c = p_A are not together in a bundle of three or more goods (case T). Agent B holds 1 with 0 alone (case B). Agent C holds its c with 0 and 1 alone (case C). ∎

Brute force over every allocation (no SAT; `src/large_bundle.py c2 ... --brute`) and the CEGAR/SAT computation agree on every connected core with n ≤ 4, at every m. No core with n = 2 needs a large bundle. At n = 3 exactly this core does, for 14 of its 216 profiles. At n = 4, 5 profiles need one at m = 6 and 102 at m = 7, and none at m ≤ 5 or m = 8 (`results/large_bundle_c2.log`; Step 0's `results/c2_small.log` has the same counts).

**A core that needs a large bundle of four goods (n = 4, m = 7; X4).** Take the agents (0, 2, 3), (0, 2, 4), (1, 2, 5), (1, 2, 6): goods 3–6 are private, good 2 is every agent's b, and tops 0 and 1 are each claimed twice. Each top has a loser. A loser is safe only by P or B, which need it to hold 2, or by C or E, which need 2 alone. Only one agent holds 2, so 2 is alone, and then no agent can use case P through 2. So the loser holding {2} (if any) is in case B and needs its top alone, and the other loser (C or E) needs its top and 2 alone. Hence 0, 1 and 2 are singletons, and the fourth agent takes all four remaining goods. The allocation {0}, {1}, {2}, {3, 4, 5, 6} (the claimants of 0 and 1 holding their tops, a loser holding 2, the other loser holding the rest) is EFX₀. Brute force over all 4⁷ allocations with the raw definition confirms that every EFX₀ allocation with at most one bundle of ≥ 3 goods has bundle sizes (4, 1, 1, 1). This is a smaller and hand-checkable counterexample to "one bundle of 3 goods always suffices" than the n = 6, m = 11 cores of X4.

## 2. A necessary condition for C2: contested tops, P-capacity, slack

For a ranking profile, let C be the set of contested tops. A set F ⊆ C is *P-fixable* if there are a winner w_g among the claimants of each g ∈ F and, for every other claimant i of g, its bottom pair {b_i, c_i}, such that all these bottom pairs (over all g ∈ F) are pairwise disjoint. The *P-capacity* p is the largest size of a P-fixable set, and the *deficit* is δ = |C| − p.

**Lemma A.** If a core has an EFX₀ allocation with all bundles of at most two goods and e empty bundles, then at least δ contested tops are alone, and δ ≤ σ − 2e ≤ σ.

*Proof.* Let g ∈ C not be alone, and let it lie in the 2-good bundle X_j. Let i ≠ j be a claimant of g. Its top is neither held by i nor alone, so by L5 agent i is safe only by case P: X_i = {b_i, c_i}. So every claimant of g except possibly j holds its bottom pair. Claimants of different tops are different agents, so all these bundles are disjoint. Hence the set of non-alone contested tops is P-fixable, with winner j if j claims g and an arbitrary claimant otherwise. So at most p contested tops are not alone, and at least |C| − p = δ are alone. By L7, a C2 allocation with e empty bundles has exactly σ − 2e alone goods. ∎

So δ > σ forces a large bundle. The converse fails: on top of the alone contested tops, their losers need chains (case B needs a alone, case C needs a and b alone), which need more alone goods. §5 tabulates how often each happens. In the X2 example (PROMPT.md §3), |C| = 3, p = 2 and δ = 1 ≤ σ = 2, yet no C2 allocation exists. The third collision needs a chain and there are not enough alone goods, as PROMPT.md says.

## 3. Construction LB

LB depends only on the ranking profile (L5 makes EFX₀ ordinal in a core) and is deterministic, with ties broken by index.

**Phase 1 (serial dictatorship with an adaptive order).** Agents are processed one at a time, and each takes its favourite remaining good as a singleton, or nothing if none of its goods remains.
- *R1 step.* If some unprocessed agent has at most two of its goods left, the one with the smallest key goes next. The key is (rank of its favourite remaining good, 3 if none; number of its goods left; index).
- *Insertion.* Otherwise every unprocessed agent still has all three goods. For each unprocessed agent i, simulate "i takes a_i, then R1 steps while any apply", and count NA: the goods that some processed agent values more than its pick, after the certain upgrades (below; "certain" meaning the agent's c is left and no unprocessed agent values it). The agent with the smallest (count, index) takes its top.

The unpicked goods are the junk J. Write Y_i for i's pick (possibly none) and "i picked before j" for the processing order.

**Phase 2 (placing the junk).**
- *Upgrades.* While some agent k holds b_k, its c_k is junk, and b_k is not in NA, give c_k to k (smallest k first). Then k holds {b_k, c_k} and no longer needs a_k alone. Here NA is the set of goods that some non-upgraded agent values more than its pick (all three of its goods if it has no pick).
- *Slots.* An agent is *frozen* if its pick is in NA. Frozen agents keep their pick as a singleton. Every other agent that is not upgraded has 1 slot if it holds a pick and 2 slots if it has none.
- If the junk fits in the slots, fill them. Otherwise choose an *owner* o (not frozen) and a set J_L of junk that o takes beyond its slots, such that the rest of the junk fits the other agents' slots. The one constraint is that no agent k ≠ o holding its own top (and not upgraded) has b_k and c_k both in o's bundle. The implementation takes the first such pair (o, J_L) in (index, lexicographic) order. If none exists, LB fails.

**Theorem 1 (soundness).** If LB returns an allocation X, then X is EFX₀ for every additive valuation of the core consistent with the rankings, and at most one bundle of X has more than two goods.

*Proof.* Phase 1 gives two invariants:
- (I1) If agent i values g more than Y_i (any g ∈ R_i if i has no pick), then g was picked before i. At i's turn, i took its favourite remaining good (in a core state all three of its goods remain and it takes a_i), and goods leave the pool only by being picked.
- (I2) If g ∈ R_i is junk, then i has a pick and values it more than g, because g was still available at i's turn.

In particular NA consists of picked goods, so no junk good is in NA. An upgraded agent k has b_k ∉ NA at its upgrade, and NA only shrinks as agents are upgraded, so upgraded agents are not frozen.

Every bundle other than o's has at most two goods: frozen agents keep one good, upgraded agents two, and the others at most their slots. Fix an agent i and another bundle X_j with |X_j| ≥ 2 (singletons are never strongly envied). Then j is not frozen, so X_j ∩ NA = ∅: Y_j ∉ NA, and junk is never in NA.
- If i is upgraded, v_i(X_i) ≥ v_i(b_i) + v_i(c_i) > v_i(a_i) ≥ v_i(X_j), since X_j meets R_i in at most a_i.
- If i is not upgraded, every good of R_i ∩ X_j is outside NA, so i values it at most as much as Y_i (and i has a pick, since otherwise all of R_i ⊆ NA). If R_i ∩ X_j has at most one good, v_i(X_j \ {h}) ≤ v_i(X_j) ≤ v_i(Y_i) ≤ v_i(X_i) for every h.
- Otherwise R_i ∩ X_j consists of two goods that i values below Y_i, so Y_i = a_i and R_i ∩ X_j = {b_i, c_i}. If |X_j| = 2, then v_i(X_j \ {h}) ≤ v_i(b_i) < v_i(a_i). If |X_j| ≥ 3, then j = o, and this is exactly the configuration the owner constraint excludes.

Only agent i's own values were used, so this holds for every consistent valuation. ∎

The proof does not use L5, only additivity and a_i < b_i + c_i for upgraded agents.

**Lemma 2 (size of the large bundle).** Let NA be taken after the upgrades. LB returns bundles of at most two goods iff |NA| ≤ σ. Otherwise its large bundle has exactly |NA| − σ + 2 goods.

*Proof.* Let s agents have a pick, e = n − s have none, and let u be the number of upgraded agents. Each good of NA is the pick of exactly one agent, so f = |NA| agents are frozen, and frozen agents are not upgraded. The junk left after upgrades has m − s − u goods. The total slot count is (s − f − u) + 2e. The overflow is ω = (m − s − u) − (s − f − u) − 2e = m − 2n + f = |NA| − σ. If ω ≤ 0 the junk fits. Otherwise the owner's bundle holds its 2 "slot-sized" goods (pick plus slot, two slots, or the upgraded pair) plus ω more. ∎

This is L7 made operational: each good that must stay alone costs one unit of slack, and the large bundle absorbs the excess.

**What LB needs in order to never fail.** Phase 1 and Theorem 1 always go through. LB can only fail in Phase 2, when every candidate owner's bundle would hold both b_k and c_k of some agent k that holds only its top. Such agents are insertion agents (both of their lower goods were still free when they picked) or R1 agents whose remaining lower good is junk while the other lower good is the owner's pick. Proving that LB never fails would prove conjecture D. §4 records how far this is certified.

## 4. Certification of LB

Tools: `src/construct.c` implements LB step for step as `src/construct.py` does. `src/construct_run.py` enumerates the cores (`cores_nauty.py`) and runs LB on every ranking profile.
- **Raw check.** Every output is checked in `construct.c` against the raw EFX₀ definition, with three balanced realizations of a > b > c that must agree, and against "at most one bundle of ≥ 3 goods". This check does not use LB's reasoning or the cases of L5.
- **Two implementations.** The C and Python implementations produce identical allocations (an FNV hash of all outputs in profile order): on every core with n ≤ 5, on every 10th connected core with n = 6 (314 cores), and on every disconnected core with n ≤ 6.
- **Certificates.** `--cert` stores, per core, allocations output by LB that together cover all 6^n profiles. `tools/check_certs.py` (SAT-free, written independently) accepts `results/certs_lb_2_6.json.gz`. `construct_run.py --check-cert` re-runs its coverage check without the connectivity requirement and checks that no stored allocation has two bundles of ≥ 3 goods. Both certificates pass: 3,436 connected cores with 143,433 allocations, and 131 disconnected cores with 10,269 allocations (`results/check_certs_lb.log`). CI re-checks both.
- **Enumeration.** `cores_nauty.py` (nauty genbg) and the independent `frontier.gen_cores` agree up to isomorphism at every (n, m) with n ≤ 6 (`results/enum_crosscheck.log`, `results/enum_crosscheck_all_m.log`).

Results (LB never fails; "large" = outputs with a bundle of ≥ 3 goods, by its size):

| n | m | cores | (core, profile) pairs | LB fails | large (by size) |
|---|---|---|---|---|---|
| 2 | 3–4 | 2 | 72 | 0 | 0 |
| 3 | 3–6 | 7 | 1,512 | 0 | 14 (3: 14) |
| 4 | 3–8 | 41 | 53,136 | 0 | 139 (3: 136, 4: 3) |
| 5 | 3–10 | 293 | 2,278,368 | 0 | 1,922 (3: 1,912, 4: 10) |
| 6 | 3–12 | 3,093 | 144,307,008 | 0 | 36,829 (3: 36,052, 4: 774, 5: 3) |
| 4–6 | disconnected | 131 | 5,431,536 | 0 | 10,544 |

Logs: `results/construct_2_5.log`, `results/construct_6.log` (with the Python comparison), `results/construct_6_cert.log`, `results/construct_disconnected_4_6.log`.

**Theorem 3 (certified; ledger S2.N6).** Construction LB never fails on a core with at most 6 agents, connected or not, with any number of goods. With Theorem 1, every such core has an EFX₀ allocation in which at most one bundle has more than two goods. This is a second, constructive certification of R3 (Step 0 certified it with SAT-found allocations), and it again gives R1 without Mahara's m ≤ n + 3 theorem.

**Beyond n = 6 (exhaustive, not certified).** LB never fails on any connected core with n = 7 and m ∈ {10, …, 14} (12,251 cores, 3,429,495,936 core–profile pairs), nor with n = 8 and m ∈ {15, 16} (53 cores, 89,019,648 pairs) (`results/construct_7.log`, `results/construct_8.log`). Every output is checked by the raw check in `construct.c`, but no certificate file is stored, so these are not CERTIFIED in the ledger's sense.

Note that LB breaks ties by index, so it is not invariant under relabelling. The runs test one labelling per isomorphism class, the one `cores_nauty.py` produces. Conjecture D is invariant, so Theorem 3 does not depend on this.

LB is not optimal: it uses a large bundle more often than necessary (for instance, 1,492 of the 46,656 profiles of the n = 6, β = 1 core, which L8 solves with bundles of two goods), and sometimes a larger one than necessary.

## 5. Structure of the large bundle

Tool: `src/large_bundle.py`.
- `c2` lists the profiles with no C2 allocation. For n ≤ 4 it also computes them a second way, by brute force over all allocations without SAT, and the two agree.
- `structure` enumerates, for every such (core, profile), *all* EFX₀ allocations with exactly one bundle of ≥ 3 goods. It uses an encoding written independently of `frontier.build`, and re-checks every solution against the raw definition.
- `relate` tabulates every profile by δ − σ (§2).
- `margin` counts, for every profile where LB needs its overflow bundle, the agents that could own it.

Logs: `results/large_bundle_c2.log`, `results/large_bundle_structure.log`, `results/large_bundle_relate.log`, `results/large_bundle_margin.log`.

### 5.1 When a large bundle is needed

C2-failing (core, profile) pairs among all connected cores. Every (n, m) with n ≤ 6 not listed has none; in particular β = 1 (m = 2n, L8) never needs one.

| n | m | σ | cores with a failing profile | failing pairs |
|---|---|---|---|---|
| 3 | 5 | 1 | 1 of 3 | 14 of 648 |
| 4 | 6 | 2 | 3 of 16 | 5 of 20,736 |
| 4 | 7 | 1 | 3 of 8 | 102 of 10,368 |
| 5 | 7 | 3 | 1 of 105 | 1 of 816,480 |
| 5 | 8 | 2 | 11 of 62 | 261 of 482,112 |
| 5 | 9 | 1 | 7 of 15 | 722 of 116,640 |
| 6 | 9 | 3 | 57 of 670 | 1,153 of 31,259,520 |
| 6 | 10 | 2 | 57 of 211 | 7,077 of 9,844,416 |
| 6 | 11 | 1 | 14 of 25 | 4,269 of 1,166,400 |

In the smallest failing cores, the losers of a contested top also lose their b, either to another loser or to another agent's top (§5.3). Examples are H3 (three agents sharing top and b) and the n = 4, m = 7 core of §1 (two pairs sharing b).

### 5.2 Who holds it, what goes in it, and each agent's case

For every C2-failing pair, `structure` enumerates all EFX₀ allocations with exactly one large bundle L (owner o). Summary (`results/large_bundle_structure.log`):

| n | m | pairs | min \|L\| (pairs) | owner can hold its top | owner can be in case C | L = c_o + private goods of agents in case T or B, owner in case C |
|---|---|---|---|---|---|---|
| 3 | 5 | 14 | 3 (14) | 0 | 14 | 14 |
| 4 | 6 | 5 | 3 (5) | 0 | 5 | 5 |
| 4 | 7 | 102 | 3 (101), 4 (1) | 82 | 102 | 102 |
| 5 | 7 | 1 | 3 (1) | 0 | 1 | 1 |
| 5 | 8 | 261 | 3 (261) | 50 | 261 | 261 |
| 5 | 9 | 722 | 3 (722) | 720 | 722 | 722 |
| 6 | 9 | 1,153 | 3 (1,153) | 1 | 1,153 | 1,153 |
| 6 | 10 | 7,077 | 3 (6,999), 4 (78) | 6,354 | 7,077 | 7,077 |
| 6 | 11 | 4,269 | 3 (4,265), 4 (4) | 4,268 | 4,269 | 4,269 |

Findings, for every C2-failing (core, profile) with n ≤ 6:
1. **Who holds it.** An agent in case C (it holds its c, with its a and b alone) can always be the owner. An agent holding its own top can be the owner in most pairs at m = 2n − 1 (and at n = 6, m = 10), but in few or none at smaller m (n = 6, m = 9: 1 of 1,153). So the natural owner is a *loser*: an agent that has already lost its top and its b to others, for which the extra goods cost nothing.
2. **What goes in it.** Some solution's large bundle is c_o together with goods that are private to other agents in case T (they hold their top) or case B (they hold b, with a alone). For such an agent its private good is its b or c, worth less than what it holds, so dumping it anywhere is harmless. Apart from c_o, no shared good is ever needed in the large bundle.
3. **Each agent's case.** In the canonical solution with the most agents holding their tops, almost every other agent holds its top (case T), with a few in P or B. The most common case profiles are TTC and TBC (n = 3); TTTC and TTPC (n = 4, m = 7); TTTTC and TTTPC (n = 5, m = 9); TTTTCC (n = 6, m = 9, where often two agents are in case C); TTTTCC and TTTTBC (n = 6, m = 10); TTTTTC and TTTTPC (n = 6, m = 11). Full histograms are in the log.
4. **Size.** Three goods suffice except in one pair at n = 4, m = 7 (§1), 78 pairs in 7 cores at n = 6, m = 10, and 4 pairs in 3 cores at n = 6, m = 11 (X4). All of these need exactly four. The frontier search tested "one bundle of three" only at m = 2n − 1, so the m = 10 cores are new. The canonical shape often costs size: the allocations `canon` finds have canonical bundles of up to six goods (`results/large_bundle_canon.log`).

This is exactly the shape of the *collector* in the proof of D for β = 2 (`proofs/beta2.md` §4, D2.C). The collector holds its private good together with the private goods of happy agents (case T) and transparent agents (case B). The data say that the same shape suffices beyond β = 2 for every core with n ≤ 6, and that the collector can always be chosen in case C.

**Conjecture K (canonical large bundle; ledger S2.K).** If a core has no EFX₀ allocation with all bundles of at most two goods, it has one whose only large bundle belongs to an agent o in case C and consists of c_o and goods private to agents in case T or B. Exhaustive evidence: every C2-failing (core, profile) with n ≤ 6, by full enumeration (`structure`) and by a direct SAT query with the shape imposed (`canon`, `results/large_bundle_canon.log`, which also covers n = 7, m = 13: all 20,328 C2-failing profiles). With D2.C this suggests a route to D: choose the loser o, and show that the rest admits bundles of at most two goods in which a_o and b_o are alone and the T/B agents' private goods are free.

### 5.3 What forces the large bundle: collisions, P-capacity, slack

Lemma A (§2) is necessary but never the binding reason in the data. Every profile at the levels in `results/large_bundle_relate.log` has δ ≤ σ. These are every level where C2 fails for n ≤ 5, plus n = 4, m = 8, n = 5, m = 10, and n = 6, m ∈ {10, 11, 12}; n = 6, m = 9 was not tabulated. So all C2-failing profiles with n ≤ 5, and those with n = 6 and m ∈ {10, 11}, have δ ≤ σ. The P-capacity bound is far from tight.

What binds is second-order, and LB's accounting shows it. Split LB's goods needed alone (after its upgrades) into tops T (goods that are the top of an agent that needs them alone) and lower goods L (goods that some agent needs alone only as its b or c). By Lemma 2, LB needs a large bundle iff T + L > σ, and a C2-failing profile forces this. Among the C2-failing profiles:

| n | m | σ | T = σ, L ≥ 1 | T > σ, L = 0 | T > σ, L ≥ 1 | T < σ |
|---|---|---|---|---|---|---|
| 3 | 5 | 1 | 14 | 0 | 0 | 0 |
| 4 | 6 | 2 | 5 | 0 | 0 | 0 |
| 4 | 7 | 1 | 86 | 13 | 3 | 0 |
| 5 | 7 | 3 | 0 | 0 | 0 | 1 |
| 5 | 8 | 2 | 230 | 30 | 0 | 1 |
| 5 | 9 | 1 | 570 | 145 | 7 | 0 |
| 6 | 10 | 2 | 5,974 | 670 | 174 | 259 |
| 6 | 11 | 1 | 2,959 | 1,210 | 100 | 0 |

In most failing profiles the tops that must stay alone exactly use up the slack, and one more good must stay alone because some loser has also lost its b. That b is either held by another loser (two losers of the same top share b, as in H3) or it is another agent's top. That loser can only use case C, which needs its a and its b alone. T can exceed σ on its own even though δ ≤ σ, because LB does not minimise the number of tops that must stay alone. In every case the large bundle absorbs the excess: each good it takes beyond two frees one more good to be alone (L7, Lemma 2), and the goods it takes are private goods of agents that do not need them (§5.2).

## 6. How close LB comes to failing, and what remains open

**Margin.** For every profile where LB needs its overflow bundle, `margin` counts the agents that are not frozen (candidate owners) and those that admit an overflow set passing the owner constraint (`results/large_bundle_margin.log`). Often there is exactly one candidate (n = 3: all 14 profiles; n = 5, m = 7: all 56). Sometimes the owner constraint rules out candidates: 2 profiles at n = 4, m = 7 and 11 at n = 5, m = 8 have two candidates of which only one works, and 4 profiles at n = 6, m = 10 have three candidates of which only one works (e.g. the core [[2,4,6], [2,5,7], [3,4,8], [3,5,9], [0,1,4], [0,1,5]] with profile (0,0,0,0,4,4)). A proof that LB never fails must identify this owner.

**Open.**
1. S2.LB: LB never fails. Theorem 1 reduces this to the existence of an owner in the last step. Certified for every core with n ≤ 6 (S2.N6). For n = 7 and n = 8, see `results/construct_7.log`, `results/construct_8.log` (exhaustive, raw check in `construct.c`, no stored certificate).
2. S2.K (Conjecture K above), and whether LB can be changed to output the canonical shape.
3. LB depends on labels through its tie-breaks. Random relabellings (`construct_run.py --relabel`, which permutes agents and goods) are evidence only. Five random labellings of every connected core with n ≤ 6, and one of every connected core with n = 7 and m ≥ 11, give 0 failures in 1,763,924,832 core–profile pairs (`results/construct_relabel.log`). Permuting agents does change LB's outputs: at n = 5, m = 9, 17 of 45 random agent orders change the number of profiles in which LB uses a large bundle.

