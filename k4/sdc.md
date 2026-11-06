# SD-C: EFX₀ allocations that extend a serial dictatorship

Workstream `proof/k4-de4` (PR #95). Ledger rows K4.SDC.*, open item 30. Code and logs: `k4/sdc/`, `results/k4_sdc/`
(`k4/sdc/run_all.sh` reproduces every log). Notation as in PROMPT.md and `k4/de4.md`. Everything called evidence
below is evidence only (PROMPT.md §5 rule 3).

## Summary

**Why a change of approach.** Every k = 4 route so far has the same shape:
1. take an extremal state (a maximum of a potential, a fewest-frozen configuration, a first agent);
2. show that a bad state has an improving move;
3. patch the case analysis when the next instance breaks it.

More than forty potentials, the move catalogues, rule F and DE4 with its tie-breaks all failed at step 3
(`k4/strategy.md`, `k4/de4.md` §10). This note has two results.
- The first explains those failures in one statement.
- The second is a target with no potential: one classical object, plus one feasibility question about it.

**1. No value-monotone method works at k = 4 (K4.SDC.P1, REFUTED).** Consider the statement:
> **P1:** every partial EFX₀ allocation that is Pareto-maximal among partial EFX₀ allocations (comparing value vectors
> (v_i(X_i))_i), and allocates the most goods among those with its value vector, is complete.

P1 is false on the core GM4-E (n = 4, m = 7, §1). A partial EFX₀ allocation X leaves one good out. No partial EFX₀
allocation is at least as good for every agent and either better for one of them or allocates more goods. Every one
of the 15 complete EFX₀ allocations makes some agent worse off than in X.

Consequences:
- Any procedure whose steps keep a partial EFX₀ allocation and never lower an agent's value can stop at X, and has no
  way to continue from it. This covers adding goods, envy-cycle rotations, and path moves in which everybody on the
  path gains.
- The maxima of total value over partial EFX₀ allocations are stuck on GM4-C, -D, -E, -G and -Q, and the leximin
  maxima on GM4-D, -E, -G and -Q.
- Random instances do not show this. No stuck maximum was found on 600 random instances with n = 3 (exhaustive) or on
  420 random instances with n = 4–6 (SAT climbs). The adversarial instances GM4-C, -D, -E, -G and -Q do show it.

So a correct procedure for k = 4 must either avoid states like X or take steps that lower some agent's value. LB⁺
(k = 3) is not of this kind: its intermediate states are pre-allocations, not partial EFX₀ allocations.

**2. A target without a potential (K4.SDC, CONJECTURE).**
> **SD-C:** in every instance in which every agent values at most four goods, some serial-dictatorship order π has
> this property: give each agent the good it picks under π, then hand out the goods nobody picked. Some way of
> handing them out makes the complete allocation EFX₀.

Lemma 1 (§2, proved) gives an equivalent form. SD-C says that some EFX₀ allocation X satisfies two conditions:
- every good an agent prefers to everything it holds is the favourite good of its holder;
- the envy relation between these favourite goods is acyclic.

That is, some EFX₀ allocation extends a Pareto-optimal one-good-per-agent matching.

SD-C implies TARGET₄. The strengthening **SD-C-R1** (K4.SDC.R1) uses only R1-priority orders, i.e. LB's Phase 1 with
some insertion choices, followed by *any* EFX₀ completion. It survives every test too.

| data | SD-C | SD-C-R1 | log |
|---|---|---|---|
| the 164 complete instances of the suite `k4/suite/` (n ≤ 26, m ≤ 65) | 164/164 | 164/164 | `sdc_suite.log` |
| the 168 instances of the DE4 screen set (GM4, A131, B131, C127, D3, the suite with n ≤ 5) | 168/168 | 168/168 (two implementations) | `sdc_screen_*.log` |
| the 86 instances that refuted DE4's candidates (`results/k4_de4/*.json`) | 86/86 | | `sdc_de4_instances.log` |
| H₂–H₅ (`k4/c4.md` §7) and HH₃, HH₄ (n = 26, 34: no first agent of LB₄ʳ works with ≤ 1 rotation, `k4/lemmam_bt.md` §3) | 6/6 | 6/6 | `sdc_ht.log` |
| every connected k = 4 core with n ≤ 3 (56 cores), 2,000 random strict profiles each | | 112,000/112,000 | `sdc_cores_n3.log` |
| every connected k = 4 core with n = 4 (1,002 cores), 200 random strict profiles each | | 200,400/200,400 | `sdc_cores_n4.log` |
| every connected k = 4 core with n = 5 and at most two 4-good agents (7,203 cores), 20 random strict profiles each | | 144,060/144,060 | `sdc_cores_n5.log` |
| random instances: R1 random cores, stuck hypergraphs, the adversarial generators, n = 8 and 12, k = 3 with n = 7, 10 | 2,160/2,160 | | `sdc_rand.log` |
| general additive instances (up to every good relevant, n ≤ 5, m ≤ 10) | 1,400/1,400 | | `sdc_general.log` |
| adversarial climbs (minimizing the number, or the fraction, of SD outcomes that extend; n = 3–5, k ≤ 4 and general) | no counterexample; smallest fraction 1/7 | | `climb_*.log` |

Cross-check: on 230 random instances, both SAT encodings give exactly the set of extendable SD outcomes. That set is
recomputed by enumerating every order and every complete allocation against the raw EFX₀ definition
(`xcheck.log`, 0 mismatches).

**3. What SD-C is not.**
- *Not "every order".* At k = 4, the climbs reach instances where 1 of 7 SD outcomes extends. At k = 3, 38 of 700
  random hard profiles have an R1 order whose outcome does not extend (`k3_every_order.log`), which is why LB⁺ needs
  its rotation. Some R1 order works on all 700.
- *Not LB⁺'s output at k = 3.* LB⁺'s rotation can give an allocation that extends no SD outcome (n = 5, m = 8,
  `k3_lbplus_shape.log`). SD-C still holds on that instance, with another order. At k = 3, SD-C-R1 is a rotation-free
  form of LB⁺: a better insertion choice replaces the rotation (K4.SDC.K3, CONJECTURE).
- *Not an extremal rule.* "Every SD outcome with the least total pick rank extends" and "every SD outcome with the
  most unwanted agents extends" hold on all 70 climb instances, but fail on 30 and 29 of the 168 screen instances,
  among them A131 and B131 (K4.SDC.SEL, `sdc_rules_screen.log`).
- *Not a local property of orders.* From a bad order, moving one agent to the front or swapping two neighbours does
  not always reach a good one: 14 of the 344 bad R1 orders of the screen set reach none (`onemove_screen.log`).

**4. What a proof must do** (§4): choose the order. Lemma 2 states the feasibility question for a fixed order.

**5. Later status (§9–§16).** The explicit forms NO and NOF ("neediest first, then one owner or one deferral") held on
large data sets but are refuted by T3 (n = 3, m = 6) and, in their R1 forms, also by Q2 (n = 4, m = 8) (§16). What
survives:
- SD-C itself;
- Proposition D4 (a deferral is an LB₄ʳ rotation in the main class);
- LB₄ʳ with the neediest-first Phase 1, which needs at most two rotations on all data (K4.SDC.NF), with its Lean frame
  ConjNFR ⟹ TARGET₄.

## 1. P1 is false (K4.SDC.P1)

GM4-E (`k4/de4/gm4_counterexample.py`; a connected k = 4 core with a strict profile):

| agent | goods (value) | ranking |
|---|---|---|
| 0 | 0 (3), 2 (10), 4 (6), 6 (2) | 2 > 4 > 0 > 6 |
| 1 | 1 (3), 3 (4), 5 (8), 6 (2) | 5 > 3 > 1 > 6 |
| 2 | 2 (4), 3 (2), 6 (3) | 2 > 6 > 3 |
| 3 | 4 (2), 5 (4), 6 (3) | 5 > 6 > 4 |

X gives {0, 4} to 0 (value 9), {1, 3} to 1 (7), {2} to 2 (4), {5} to 3 (4), and leaves good 6 out.

*X is partial EFX₀.*
- 0 and 1 envy only singletons ({2} and {5}).
- Agent 2 sees {1, 3}, whose good 3 it values at 2 ≤ 4.
- Agent 3 sees {0, 4}, whose good 4 it values at 2 ≤ 4.

*Good 6 cannot be added anywhere.*
- {0, 4, 6}: agent 3 sees {4, 6} after removing 0, worth 5 > 4.
- {1, 3, 6}: agent 2 sees {3, 6}, worth 5 > 4.
- {2, 6}: agent 0 sees {2}, worth 10 > 9.
- {5, 6}: agent 1 sees {5}, worth 8 > 7.

*Nothing better exists.* Exhaustively, over all 5⁷ partial allocations, no partial EFX₀ allocation gives every agent
at least its value in X and is either better for someone or allocates good 6. The 15 complete EFX₀ allocations each
leave some agent below its value in X. For example ({0, 1, 3, 4}, {5}, {2}, {6}) has values (9, 8, 4, 3): agent 3 drops
from its top (4) to good 6 (3).

The total-value maxima over partial EFX₀ allocations are stuck in the same way on GM4-C, -D, -E, -G and -Q, and the
leximin maxima on GM4-D, -E, -G and -Q (`p1_replay.log`).

Artifacts:
- `k4/sdc/refute_p1.py`: an independent replay from the definitions alone (`refute_p1.log`).
- `k4/sdc/p1_screen.py`: a SAT climb to Pareto maxima over the screen set; 14 of 504 climbs end stuck, all on GM4
  instances (`p1_screen.log`).
- `k4/sdc/p1_brute.py` with `p1_replay.py`: a brute-force recount of every stuck instance found (`p1_replay.log`).
- `p1_rand.log` (brute force, n = 3) and `p1_sat_rand.log` (SAT climbs, n = 4–6): random instances, none stuck.

**What this does and does not say.** DE4's orders are not refinements of the Pareto order on partial EFX₀ allocations,
and they range over restricted state spaces, so P1 does not refute them formally. Each of them failed separately
(`k4/de4.md` §10). What P1 shows is the common cause. At k = 4, the value an agent "deserves" in a completable state
can be lower than what a monotone process has already given it. Here each agent is the one that loses in some
completion (`refute_p1.log`), so no single agent can be singled out in advance.

## 2. SD-C

**Serial dictatorship.** For an order π of the agents, each agent in turn takes its favourite remaining good of R_i
(nothing if none is left). Values are strict per agent; ties are broken once by good index, as everywhere in `k4/`.

The outcome Y = SD(π) has two properties:
- (I1) every good an agent prefers to Y_i was taken earlier;
- (I2) every unpicked good g is worth less to each of its valuers i than Y_i.

A *completion* of Y gives every unpicked good to some agent, so X_i ⊇ {Y_i}. Y *extends* if some completion is EFX₀.

**R1-priority orders** are LB's Phase 1 (`proofs/lb_last_step.md` §1): an agent all of whose goods are still
available is taken only when every unprocessed agent still has all of its goods.

**Conjecture SD-C (K4.SDC).** For every instance with at most four relevant goods per agent, SD(π) extends for some
order π.

**Conjecture SD-C-R1 (K4.SDC.R1).** The same, with π an R1-priority order.

**Lemma 1 (characterization; K4.SDC.CHAR).** For an allocation X, let F_i(X) be agent i's favourite good of
X_i ∩ R_i (none if that set is empty). X is a completion of some SD outcome iff:
- (U) every good g ∈ R_i that i prefers to F_i(X) (every good of R_i if F_i(X) is none) is F_j(X) for its holder j;
- (A) the relation "i prefers F_j(X) to F_i(X)" has no cycle.

Then the SD outcome is F(X), so the outcome is determined by X.

*Proof.* (⇒) Let X ⊇ Y = SD(π).
- Suppose i holds x ∈ X_i ∩ R_i that it prefers to Y_i. By (I1), some earlier agent j picked x. Then x = Y_j ∈ X_j,
  which contradicts x ∈ X_i.
- If Y_i is none, every good of R_i was picked by others, so X_i ∩ R_i = ∅.

So Y = F(X). (U) is (I1). (A) holds because every edge goes from an agent to one processed earlier.

(⇐) Let π be a topological order of (A), with j before i whenever i prefers F_j(X) to F_i(X). Induction along π:
- Every good that i prefers to F_i(X) is, by (U), some F_j(X) that i prefers. That agent j comes earlier, so the good
  is taken.
- F_i(X) itself is untaken: by induction, every earlier agent j took F_j(X), and F_i(X) ≠ F_j(X).

So i takes F_i(X), and X is a completion of SD(π). ∎

So SD-C says that some EFX₀ allocation satisfies (U) and (A). (U) is a no-waste condition: a good that an agent would
rather have than everything it holds is never junk in another bundle; it is the favourite of its holder. (A) can
always be met by rotating favourites along a cycle, but that rotation does not obviously keep EFX₀, so SD-C keeps (A)
as part of the statement.

A matching in which every agent gets at most one good is Pareto-optimal iff it is an SD outcome. This is the
Abdulkadiroğlu–Sönmez characterization for house allocation [unverified: not read in this session; nothing here uses
it, since Lemma 1 is proved directly]. In that language, SD-C says that some Pareto-optimal one-good matching extends
to an EFX₀ allocation.

**Lemma 2 (the completion problem for a fixed order).** Let Y = SD(π) and X a completion, with t_i = v_i(X_i ∩ R_i)
≥ v_i(Y_i).
- (a) If some agent i values Y_j above t_i, then X_j = {Y_j}. A *wanted* pick stays alone.
- (b) A bundle X_j threatens i iff it strictly contains a set T ⊆ R_i with v_i(T) > t_i, or X_j ⊆ R_i and
  v_i(X_j) − min_{X_j} v_i > t_i (`k4/de4.md` Lemma 7).
- (c) Every good of R_i in X_j other than Y_j is unpicked, and so worth less than Y_i to i (I2). Hence a threat by an
  unwanted bundle needs at least two of i's goods in that bundle.

*Proof.*
- (a) T = {Y_j} in (b).
- (b) X_j ∖ h with h ∉ T.
- (c) (I2), and each good is worth at most t_i. ∎

So, for a fixed order, the completion problem is a packing problem:
- the unpicked goods go to unwanted agents (and to agents without a pick);
- no bundle may strictly contain a *danger set* of another agent: two or three of its goods worth more than its
  holding.

An agent's danger sets shrink when it receives goods of its own. At k = 3 the only danger set of a top-holder is
{b, c}. That is LB⁺'s condition (β), and LB⁺'s owner test is a special case of this packing problem: the surplus
goes to one agent.

## 3. Evidence

See the table in the summary. Notes on the data:
- **Two implementations.**
  - `k4/sdc/sdc_orders.py` enumerates every order (all R1-priority orders in mode `r1`), computes each distinct SD
    outcome directly, and asks a SAT solver only for the completion.
  - `k4/sdc/sdsat.py` and `k4/sdc/sdsat_r1.py` encode the order itself: pairwise order variables with transitivity,
    and "every good of R_i ranked at or above i's pick is i's pick or picked by an earlier agent".

  Both share only the EFX₀ clause generator of `k4/sdc/sdclib.py`. `k4/sdc/xcheck.py` checks both against brute force,
  which uses the raw definition and no SAT, by comparing the full set of extendable outcomes.
- **Fraction of good orders.** The climbs `sdc_climb3.py` minimize the fraction of SD outcomes that extend. They reach
  1/7 at n = 4 and 1/5 at n = 5, never 0. So the order matters, and no static rule tried picks it.
- **General additive instances.** SD-C held on all 1,400 random instances in which agents value up to every good
  (n ≤ 5), and on two climbs over such instances. At n = 3 EFX₀ itself is known [Chaudhury–Garg–Mehlhorn, cited in
  `proofs/citations.md`]. Whether SD-C holds for all additive instances is open, and would be a strengthening of EFX₀
  existence; nothing here needs it.
- **The case of distinct tops.** When all tops are distinct, the SD outcome is unique, and SD-C says that some EFX₀
  allocation gives every agent its top. This held on 2,400 random instances (`distinct_tops.log`). If no two agents
  share two goods, "every agent its top, every other good to one of its valuers" is already EFX₀, by Lemma 2(c).

## 4. The proof task

SD-C replaces "potential + moves" with one choice: the order. What is open:
1. **The obstruction for a fixed order.** When SD(π) does not extend, describe the infeasibility certificate of the
   packing problem of Lemma 2: a set of unpicked goods that cannot be placed, and the danger sets that block each
   unwanted agent. Compare Lemma H1's covering form of owner validity (`k4/hall.md` §1), which fixes one owner.
2. **From an obstruction to a better order.** LB⁺'s Theorem B (k = 3) turns the bad case into a rotation along a need
   chain k → … → r. The order-based version is a new insertion choice that processes the chain's agents before k.
   K4.SDC.K3 asks for this at k = 3, where the obstruction is known exactly (`proofs/lb_last_step.md` §4); that is the
   first step to prove.
3. **Global choice.** Single moves do not suffice (Summary, item 3). The order has to be chosen against the obstruction,
   e.g. by an induction on blocks that fixes each block's insertion agent from the obstructions the later blocks would
   create.

Smallest open cases worth proving first: n = 2 for all additive valuations; k = 3 (K4.SDC.K3); distinct tops at
k = 4.

## 5. The rotation as a re-insertion (data toward K4.SDC.K3)

At k = 3, LB⁺ reaches its bad case (`proofs/lb_last_step.md` §4) and rotates along a need chain k* → … → r. The data
suggest replacing the rotation by an order: re-run the last block B* with **r as its leader**, keeping the earlier
blocks. Here r is the last-processed agent that is not upgraded, and the end of every need chain from k*.

- **K3ALG's runs.** On the bad cases of K3ALG's own runs (index insertion), the re-run with leader r never reaches the
  bad case again: 130 of 130 bad cases (n = 5, 6, 8), and 590 of 590 random R1 continuations after r
  (`k3_leader_r.log`). In those runs, r is a working leader in every bad case, while the old leader k* works in 24 of
  70 (`k3_leader.log`).
- **Arbitrary runs.** On bad cases of random runs (random insertion agents and random R1 order), the re-run with leader
  r reaches the bad case again in 7 of 1,075 re-runs (`k3_leader_r2.log`). Iterating, i.e. re-running the new last
  block with its own r, stops without rotation on all 450 bad cases tested, after at most two re-runs
  (`k3_leader_iter.log`).
- **Other rules.** Taking an agent that needs k*'s top as leader fails 7 times in 300 (`k3_needer.log`).
- **No monotone quantity.** The re-run is not monotone either: some agent of B* is worse off in every re-run, and the
  total pick rank of B* goes up in 5 of 300 (`k3_rerun_stats.log`), as P1 predicts.

So the open form of K4.SDC.K3 is:
> **Lemma LR (conjecture):** from any run of Phase 1, repeatedly re-running the last block with its r as leader reaches
> a run that LB⁺ completes without rotation.

Its output then completes an SD outcome: upgraded agents keep their pick b_u, and everybody else keeps its pick. A proof
needs a quantity that the re-runs decrease. The obvious ones (total rank in B*, number of junk goods) do not decrease.

**At k = 4 the order inside a block matters too.** Take R1 runs of the screen set whose SD outcome does not extend.
Re-running only the last block with another leader, then R1 priority by index, repairs 511 of 625; the last-processed
agent works in 402 (`k4_leader_screen.log`). The other cases also need the order among the agents that have lost a good.
Example: c4-exposure-nonleader-n3m5 (n = 3, m = 5), where leader 2 works only if agent 1 goes before agent 0. At k = 3,
by contrast, nothing depends on that order (`proofs/lb_last_step.md` §1). So at k = 4 the target is SD-C-R1 with the
whole order chosen, as stated.

## 6. Theorem DT: distinct tops (SD-C's base case, proved)

When the agents' tops are pairwise distinct, the SD outcome is unique (everyone takes its top) and nobody is frozen. In
that case SD-C has a short proof: one potential and two moves.

**Theorem DT (K4.SDC.DT).** Let every agent value at most four goods (any nonnegative additive values; each agent's
ranking breaks ties by good index; agents that value nothing are ignored), and let the tops a_i be pairwise distinct.
Then for every agent o there is an EFX₀ allocation with these properties:
- every agent holds its top;
- every bundle other than o's has at most two goods;
- nobody envies o.

In particular SD-C holds on these instances.

*Proof.* Let J be the goods that are nobody's top. A *matching* M gives some agents i ≠ o one good m_i ∈ J ∩ R_i,
distinct goods for distinct agents. Let L = J ∖ {m_i}. The allocation X(M) gives X_i = {a_i, m_i} (or {a_i}) to
i ≠ o and X_o = {a_o} ∪ L. A set S ⊆ R_i is *robust* if v_i(S) ≥ v_i(R_i ∖ S).
- (F1) Every good is worth at most v_i(a_i) ≤ v_i(X_i) to i.
- (F2) A bundle of at most two goods threatens nobody: removing one good leaves at most one good, worth at most
  v_i(X_i) by (F1). So only X_o can threaten, and o itself is never threatened.
- (F3) A robust holder is never threatened and envies nobody: for every bundle X_j, v_i(X_j) ≤ v_i(R_i ∖ X_i) ≤ v_i(X_i).
- (F4) {a_i, g} is robust for every g ∈ R_i ∖ {a_i}, with one exception: g = d_i, the last good of a 4-good agent,
  when v_i(b_i) + v_i(c_i) > v_i(a_i) + v_i(d_i). For 3 goods, a ≥ the remaining good; for 4 goods, {a, b} ≥ {c, d}
  and {a, c} ≥ {b, d}. An agent with at most two goods is robust already on {a_i}.

Call T ⊆ X_o ∩ R_i with v_i(T) > v_i(X_i) a *danger set of i inside X_o*. If X_o threatens i, then
T = (X_o ∖ h) ∩ R_i is one, for the h that gives the threat. By (F1), every danger set has at least two goods. If i has
no danger set inside X_o, then v_i(X_o ∩ R_i) ≤ v_i(X_i), so i does not envy X_o.

Moves, for an agent i ≠ o that is not robust and has a danger set T inside X_o:
- **(m1)** If i is unmatched: T has at least two goods and at most one of them is a_o, so T contains a good g ∈ L, and
  g ∈ R_i. Set m_i = g.
- **(m2)** If i is matched, then by (F4) i is a 4-good agent with m_i = d_i, and its only possible danger set is
  {b_i, c_i} (each single good is worth at most a_i). So {b_i, c_i} ⊆ X_o. At most one of them is a_o, so one of them
  lies in L. Rematch i to it; d_i returns to L.

Let π be the number of matched agents i with {a_i, m_i} robust.
- (m1) raises |M| and does not lower π.
- (m2) raises π (i becomes robust) and keeps |M|.

So the pair (π, |M|) rises lexicographically at every move, and the moves stop. Afterwards, every agent i ≠ o is robust
or has no danger set inside X_o. By (F2) and (F3), X(M) is EFX₀ and nobody envies o. ∎

The bound k ≤ 4 is used only in (F4). The construction is run literally, with the raw EFX₀ check, by
`k4/sdc/dt_check.py`. It covers random instances with 1–4 goods per agent, ties and distinct tops: 29,000 runs, with
every owner, n = 4, 6, 10, and no assertion fails (`dt_check.log`).

*Relation to Theorem Z* (K4.C4MIN.Z, in Lean). Theorem Z gives an EFX₀ allocation with at most one large bundle
whenever some valid pre-allocation of `k4/c4x.md` has no frozen agent. That hypothesis holds when tops are distinct.
Theorem DT is the SD-C form of this case:
- every agent keeps its top;
- the owner is arbitrary and unenvied;
- any instance with at most four relevant goods per agent qualifies (no core assumption);
- the proof is a few lines.

**The general completion problem, after Theorem DT.** For an arbitrary SD outcome, the same argument handles every agent
whose pick nobody wants. Two facts carry over:
- (F2) carries over: a two-good bundle {Y_j, g} with Y_j unwanted and g unpicked threatens nobody, by Lemma 2(c).
- (m1) and (m2) carry over for unwanted agents. An unwanted b-holder's only possible danger set is {c, d}, and (m1)
  takes one of them.

What remains are the *frozen* agents, whose pick someone wants. They must stay alone, so they cannot take goods. Their
danger sets among their own lower goods must not lie inside X_o:
- {b, c}, {b, d}, {c, d} or {b, c, d} for a frozen top-holder;
- {c, d} for a frozen b-holder.

Meanwhile the moves of the unwanted agents compete with them for the unpicked goods. So for a fixed order, SD-C's
completion problem is a covering problem about frozen agents only. This is the k = 4 form of LB⁺'s exposed frozen
leader (`proofs/lb_last_step.md` §4), and the order has to be chosen against it.

**Theorem DT⁺ (same proof).** If, in SD(π), no frozen agent values an unpicked good, then SD(π) extends, with any
unwanted owner. The reason: a frozen agent's lower goods are then all picks, so at most one of them (Y_o) lies in X_o,
and a single lower good is never a danger set. The moves (m1) and (m2) of the unwanted agents never touch a good that a
frozen agent values.

This condition can rarely be met by an order. Some order meets it on only 19 of the 168 screen instances. The weaker
condition, that every frozen agent's unpicked goods are worth at most its pick in total, is met on 153
(`sdf_screen.log`). The rest need the covering, including the unfreezing of a frozen agent: its needer takes goods of
its own and stops needing it, as in LB's need-shrinking upgrades.

## 7. At k = 4 the order is global

At k = 3, re-ordering the last block suffices (§5). At k = 4 it does not:
- On the screen set, 14 of 625 bad R1 runs need the whole order changed (`k4_blocks_screen.log`; most of these
  instances have a single block).
- On the stuck hypergraphs of `results/k4_de4/` with random profiles, all 10 bad runs with two blocks need the first
  block changed (`k4_blocks_hyper.log`).

A smallest example (n = 3, m = 8):

| agent | ranking (values) |
|---|---|
| 0 | 2 (10) > 4 (8) > 5 (6) > 1 (3) |
| 1 | 7 (8) > 4 (6) > 1 (5) > 6 (4) |
| 2 | 7 (8) > 3 (5) > 2 (4) > 5 (2) |

The order 1, 2 | 0 has two blocks:
- agent 1 takes 7;
- agent 2, which lost 7, takes 3;
- the next block's leader, agent 0, takes 2.

Agent 1 is frozen, because agent 2 wants 7. All three of its lower goods (4, 1, 6) are unpicked, and any two of them
are worth more than its pick. So two of them must be kept out of the large bundle. But only one other agent can take a
good: agents 0 and 2 are both unwanted, and one of them is the owner. Agent 2 cannot unfreeze agent 1: with its
own unpicked good 5 it holds 5 + 2 = 7 < 8.

The order 0, 2, 1 has one block and gives 7 to the 3-good agent 2. Agent 2 is then frozen, but its unpicked goods
(3 and 5) are worth 5 + 2 = 7 < 8 in total. Agent 1 takes 4.

So the order has to give a contested good to the claimant whose freezing is cheapest. At k = 3 freezing always costs
one good; at k = 4 a frozen top-holder with flat lower goods costs two. This is the counting that LB₄ and rule F lose
(`k4/rulef.md`, `k4/lemmam_bt.md`), now isolated as a statement about orders.

**A naive count does not decide.** Define the deficit of an SD outcome as (the number of unpicked goods each frozen
agent must have kept out, summed) minus (the free slots of the unwanted agents, less one for the owner). This deficit
does not decide extendability (`sdc_deficit_screen.log`, R1 orders of the screen set, 690 outcomes):
- 72 outcomes with deficit ≤ 0 do not extend: unwanted agents need their own slots, and the owner's pick can sit in a
  danger set;
- 38 with deficit > 0 do extend: frozen agents share goods, or one is unfrozen.

So the exact count must include the unfreezing and the unwanted agents' needs. That is the role of Lemma K and K′
(`k4/rulef.md` §2, in Lean), which are exact for a fixed state. The open step is the order that makes it nonpositive.

**No static order rule found.** "Cheapest freezing first" is one fixed order (`k4/sdc/sdc_cheap.py`): at every R1
step, take the agent whose favourite remaining good would need the fewest goods kept out to protect it. Its SD outcome
fails to extend on 14 of the 168 screen instances (among them C127, D3 and c4-lbplus-rotation-n3m6) and on 12 of the
164 suite instances (`sdc_cheap.log`). As with rule F (`k4/rulef.md` §5.3), every static rule tried fails somewhere,
so the order has to be chosen against the obstruction of the run itself (§4, item 2).

## 8. What selects a good order: stronger forms that hold, rules that fail

**Stronger forms that hold on all data** (EVIDENCE):
- **SD-C-PS** (K4.SDC.PS): for *every* agent w, some SD order extends to an EFX₀ allocation in which nobody envies w.
  - All 589 (instance, agent) pairs of the screen set, and all 637 of the suite (n ≤ 26).
  - With R1 orders only, 3 of the 589 pairs fail (`sdc_ps_screen.log`, `sdc_ps_screen_r1.log`, `sdc_ps_suite.log`).
  - It combines SD-C with the prescribed-source property PS of `k4/induct.md`; Theorem DT has this form.
- **Fewest frozen agents:** among the SD outcomes with the fewest frozen agents, *some* extends, on all 168 screen
  instances, with plain or R1 orders (`sdc_fewest.log`).
- **Multigraph and linear instances:** SD-C holds on 560 random multigraph instances (`sdc_multigraph.log`) and on 300
  random linear ones, where two agents share at most one good (`sdc_linear.log`). Even there, not every order works.

**Selections and local rules that fail:**
- *Every* fewest-frozen outcome extends: fails on 30 of the 168 screen instances. Adding the frozen cost, the naive
  deficit or the junk count as a tie-break repairs only 10 of the 30.
- **Static need rules** ("the claimant whose top beats its next two goods by the most goes first", and variants): fail
  on 11–16 of the screen instances (`sdc_need.log`).
  - They come from the n = 2 failures (induct-g-r0, ls-no-exchange-n2m4, lb4-n2m5-upgrade), where the needier
    claimant must win.
  - They fail on c4min-tlam-n3-m6 and c4x-n3m6-onefour-a. There the big-top agent must *lose* its top and own all its
    lower goods, which are private and together worth more than the top (8 < 4 + 3 + 2).
- **Contest swaps** (move an agent that wants a frozen agent's pick to just before it): repair 542 of 634 bad orders in
  one step and 588 by a walk; 46 stay stuck (`sdc_swap.log`).
- **Descent over orders** (exact deficit = fewest goods left out; neighbours: move one agent anywhere): 4 strict local
  minima of deficit 1 among 136 bad orders (`sdc_descent.log`). So SD-C has no local-search proof with these moves,
  like DL₂ (`k4/dl2.md`) for pre-allocations.
- **Last agent:** not every agent can be last in a good order (529 of 589 pairs, `sdc_last.log`). An induction that
  appends one agent must choose that agent.
- **No parity:** the number of extendable SD outcomes is odd on 74 of the 168 instances.

**Reading.** SD-C holds on every instance tested, but no local or extremal criterion found so far selects a good order.
The data say what such an argument must account for:
- the order must resolve each contest in favour of the claimant whose freezing is cheapest;
- whether freezing is cheap depends on whether the loser's own lower goods are free (private, or wanted by nobody);
- a 4-good big-top agent with private lower goods should lose.

At k = 3 the same choice is LB⁺'s bad case. At k = 4 it occurs in every block, not only the last.

## 9. Conjecture NO: neediest first, one owner last

The n = 2 failures of §8 say that a contest must go to the claimant that needs its top more. The tlam-type failures say
that one big-top agent may instead have to lose and own all its lower goods. Combining the two gives an explicit rule
with a single global choice.

**The order NO(o).** Fix an agent o, the *owner*. Process the other agents one at a time. At every step:
- take the unprocessed agent i ≠ o with the largest *need*, need(i) = v_i(y₁) − v_i(y₂) − v_i(y₃);
  - here y₁ > y₂ > y₃ > … are i's goods still available, ranked by i, and missing ones count 0;
  - ties are broken by a fixed priority over the agents;
- i takes y₁.

Finally o takes its favourite remaining good. There is no R1 priority: the need is recomputed from the goods still
available at every step. An agent with no available good picks nothing wherever it stands, so its position does not
matter (the code processes such agents last).

**Conjecture NO (K4.SDC.NO).** In every instance with at most four relevant goods per agent, there is an agent o such
that the picks of NO(o) extend to an EFX₀ allocation. This is SD-C with n candidate orders instead of n!. The owner is
the only global choice, like rule F's first agent (`k4/rulef.md`), but at the other end of the order.

Evidence (EVIDENCE only; `no_*.log`):

| data | NO holds |
|---|---|
| the 168 screen instances and the 164 suite instances (n ≤ 26) | 168/168, 164/164 (`no_screen_suite.log`) |
| the same with 6 random tie-break priorities each | 1,008/1,008 (`no_ties.log`) |
| the 86 instances that refuted DE4's candidates; H₂–H₅, HH₃, HH₄ (owner ℓ) | 92/92 (`no_files.log`) |
| random strict profiles: every connected k = 4 core with n ≤ 3 | 20,000/20,000 |
| the same, n = 4 | 30,000/30,000 (`no_cores_n4.log`) |
| the same, n = 5 with at most two 4-good agents | 8,000/8,000 (`no_cores_n5.log`) |
| random cores, stuck hypergraphs, the adversarial generators, n = 8, k = 3 | 1,050/1,050 (`no_random.log`) |
| general additive instances, every good possibly relevant (n = 3, 4) | 1,800/1,800 (`no_random.log`) |
| adversarial climbs (minimizing the number of working owners, n = 4, 5) | no counterexample; minimum 1 at n = 4, 2 at n = 5 (`no_climb_*.log`) |

**The owner choice is real.** On the screen set, the agent that plain neediest-first processes last works on 153 of the
168 instances; the agent of least initial need on 140; the agent with the most private value on 143. On some
instances exactly one owner of three or four works (`no_owner.log`). Without the owner choice, neediest-first fails on
11–16 instances (§8).

**Lemma N (the contest dichotomy; K4.SDC.N).** In NO(o), let i be processed at time τ and take y, and let j ≠ o be
processed later. Suppose y was j's favourite available good at τ, and j ends up preferring y to its own pick. Let
z₂, z₃ be j's second and third goods available at τ, and w₂, w₃ i's. Then one of the following holds:
- (a) v_j(y) ≤ v_j(z₂) + v_j(z₃). If j's pick is z₂ and j also holds z₃, then j no longer prefers y to its holding: j
  is *compensable*, and i is not frozen by j.
- (b) v_i(y) − v_i(w₂) − v_i(w₃) ≥ v_j(y) − v_j(z₂) − v_j(z₃) > 0. Then any two goods of i other than y that were
  available at τ are worth less than y to i. So if i is frozen, its only possible danger set among those goods is the
  set of all of them (at most three). Keeping one of them out of the large bundle protects it.

*Proof.* At τ the rule chose i over j, so need(i) ≥ need(j). If need(j) ≤ 0 we are in (a). Otherwise
need(i) ≥ need(j) > 0, which is (b): v_i(w₂) + v_i(w₃) < v_i(y), and every other good available at τ is worth at most
v_i(w₃). ∎

So under NO every contest is decided in one of two ways:
- the loser can be compensated by one of its own goods, so nobody stays frozen by it; or
- the winner is "big-top on what remained", and its freezing costs at most one good kept out.

This is the k = 3 situation, where a frozen exposed top-holder costs exactly one good (`proofs/lb_last_step.md`
Lemma 1), and the case analysis of LB⁺ has this shape.

What a proof of NO must add:
1. The compensations must be simultaneously feasible. The loser's z₂, z₃ may be taken later by other agents, and one
   agent may lose several contests.
2. A counting step: one slot per remaining frozen exposed agent, as LB⁺'s Theorem A finds one terminal per block.
3. The choice of o, which replaces LB⁺'s rotation. At k = 3, o = r, the last non-upgraded agent, works outside the bad
   case, and the bad case is §5's re-insertion.

**The k = 3 instance of NO.** At k = 3 every balanced agent with all its goods available has need < 0. Only agents that
have lost goods can have positive need. So NO at k = 3 is a serial dictatorship that serves the agents that lost
goods, in order of need, before fresh agents, close to LB's R1 priority. Proving NO at k = 3 with LB⁺'s machinery is
the natural first step.

**Fresh owners.** Call o *fresh* in NO(o) if no other agent picks a good of o. Every fresh owner found works: 12 on the
screen set, 31 on the suite. But only 24 of the 332 instances have one (`no_fresh.log`).
- At k = 3 a fresh owner is provably enough. The order NO(o) is then an R1 run of LB's Phase 1 (agents that lost goods
  have positive need, fresh ones negative; agents left without goods pick nothing wherever they stand). o is the leader
  of the last block {o} and the last agent that is not upgraded. So r = o = k*, and LB⁺'s bad case, which needs
  k* ≠ r, cannot occur (`proofs/lb_last_step.md` Theorem A).
- At k = 4 the analogue of Theorem A is what is missing.
- When no owner is fresh, the owner has lost goods to others, and its block structure is that of a deferred R1 agent.
  That is where a proof of NO must do new work.

**Two candidate owners do not suffice.** On the screen set and the suite, the owner can always be taken to be the first
or the last agent of the plain neediest-first run. In the 15 screen instances where "last" fails, the first agent is a
big-top agent with two or three of its own goods unpicked, and it should give up its top and own its lower goods. But
this two-candidate form fails on 2 of 20,000 random profiles of the n = 4 cores (`no_first.log`). For example, on
sets [[0, 1, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5]] with values [[8, 4, 3, 10], [8, 5, 4, 6],
[3, 7, 6, 5], [8, 4, 2, 3]]:
- the plain order is 3, 0, 1, 2;
- only owner 0, the second agent, works.

So NO's owner remains a genuine choice among n.

**The owner walk.** Start from o = the last agent of the plain neediest-first run. While NO(o) does not extend, hand the
owner role to an agent that holds a good o prefers to its own pick (an agent o *needs from*).
- The greedy walk reaches a working owner on all 168 screen and 164 suite instances, almost always in one step, and on
  19,999 of 20,000 random n = 4 core profiles.
- A breadth-first search over the same moves reaches one on all 20,000 (`no_walk.log`).

At k = 3 the walk is LB⁺'s structure:
- if the plain run is not in LB⁺'s bad case, its last agent works (Theorem A);
- in the bad case, the need chain k* → … → r leads from r back to k*, and deferring k* makes the chain agents move up,
  as in LB⁺'s rotation (Theorem B). The agent that needed k*'s top takes it, and so on, and k* takes its b, which the
  plain run had left unpicked or given to r.

On bad cases of random k = 3 core profiles, NO(k*) or NO(r) extends in every case (200 of 200 at n = 5, `no_k3_*.log`);
NO(k*) alone fails once. It fails when an agent squeezed by the new cascade takes b_{k*} first. So at k = 3, NO reduces
to one statement about the last block: deferring k* or r repairs the bad case. That is Lemma LR of §5 with the
re-insertion replaced by a deferral, and the next proof target.

## 10. Deferral and displacement chains (toward K4.SDC.K3)

**Lemma DC (displacement chain; K4.SDC.DC).** Let π be any order, Y = SD(π), and k an agent with a pick. Let π_k be π
with k moved to the end. Define a chain j₀ = k, j₁, j₂, … and holes h₀ = Y_k, h₁, h₂, …:
- j_{i+1} is the first agent after j_i in π that prefers h_i to its own pick Y_{j_{i+1}} (or has no pick and values h_i);
- h_{i+1} = Y_{j_{i+1}};
- the chain stops when no such agent exists, or when a hole is "none".

Then SD(π_k) gives:
- j_i (i ≥ 1) the good h_{i−1};
- every other agent other than k its pick Y;
- k its favourite remaining good, from the final hole and the goods SD(π) leaves unpicked.

In particular every agent other than k gets a weakly better good.

*Proof.* Induction along π_k, with the invariant: just before an agent x ≠ k moves, its available set in π_k is its
available set in π plus exactly one good, the current hole h (for agents before k in π the sets are equal). x's
favourite in π is Y_x.
- If h ∉ R_x, or x ranks h below Y_x, x takes Y_x in π_k too, and the invariant holds with the same hole.
- Otherwise x takes h. Its π-pick Y_x stays available, so Y_x becomes the hole.

At the end k finds the final hole and the goods nobody picked. ∎ (Checked against serial dictatorship on 3,000 random
instances, `k3_disp_n5.log`.)

So deferring one agent is a single chain of upgrades. LB⁺'s rotation (Theorem B) is such a chain, run backwards in
time.

**Proposition D3 (K4.SDC.D3).** At k = 3, let π be an R1 run of Phase 1 in LB⁺'s bad case with leader k* and owner r.
Suppose the displacement chain from k* in π avoids the upgraded agents and ends at r. Then SD(π with k* last) extends
to an EFX₀ allocation.

*Proof.*
1. Every j_{i+1} prefers h_i = Y_{j_i} to its pick, so Y_{j_i} ∈ N_{j_{i+1}}, and j_{i+1} ∉ U by hypothesis. Hence
   j₀, …, j_{t−1} are frozen and j_t = r is a terminal (A1). The chain is a need chain from k* to r in LB⁺'s sense
   (`proofs/lb_last_step.md` (A4)).
2. By Lemma DC, SD(π_{k*}) gives each j_i (i ≥ 1) the good Y_{j_{i−1}}, every agent off the chain its pick, and k* its
   favourite among a_{k*}, b_{k*}, c_{k*} still available. Now a_{k*} is taken by j₁. In the bad case b_{k*}, c_{k*} lie
   in J ∪ {Y_r}, unpicked goods stay unpicked, and Y_r is the final hole. So k* takes b_{k*}.
3. These are exactly the picks of LB⁺'s rotated pre-allocation P′ along this chain (Theorem B: Y′_{x_i} = Y_{x_{i−1}},
   Y′_{k*} = b_{k*}). The goods c_u (u ∈ U′ = U ∪ {k*}) are picks of neither.
4. By Theorem B, P′ is valid and k* is a valid owner (or ω′ ≤ 0), so it has a completion that is EFX₀ (Theorem 1′).
5. That completion gives every agent its P′ pick, so it extends SD(π_{k*}). ∎

**The other bad cases** (`k3_disp_n5.log`, 300 bad cases of random R1 runs at n = 5):
- In 262 the chain avoids U and ends at r (Proposition D3).
- In 26 it passes through an upgraded agent u, which takes its top a_u. The hole becomes b_u. SD(π with k* last)
  extends in 22 of these, and with r last in the other 4.
- In 12 it continues past r. It does so only through upgraded agents (all agents after r are upgraded, (A2)), and
  SD(π with k* last) extends in all 12.

So K4.SDC.K3, and with it a rotation-free proof of TARGET in the SD-C form, reduces to these two classes. In both, an
upgraded agent u takes its top a_u, and c_u stays unpicked for u. The completion of P′ must then be adapted: u gives up
its upgrade c_u and holds a_u (with c_u as a slot good if needed). And when b_{k*} = Y_r has been taken past r, k*
holds c_{k*}.

Lemma DC is not specific to k = 3. It gives exact control of every owner change in Conjecture NO's fixed-order
variants, and it is the tool for the k = 4 owner walk.

## 11. Conjecture NOF: the plain neediest-first run, or one deferral

Lemma DC makes deferral exact in a fixed order. That suggests replacing NO's dynamic owner by a fixed-order deferral.

**Conjecture NOF (K4.SDC.NOF).** Let π be the plain neediest-first order (NO without owner). In every instance with at
most four relevant goods per agent, either SD(π) extends to an EFX₀ allocation, or SD(π with one agent o moved to the
end) does. By Lemma DC each candidate is SD(π) changed along one displacement chain.

Evidence (`nof.log`, `nof_files.log`; EVIDENCE only):
- all 168 screen and 164 suite instances; the plain run alone works on 153 and 150;
- the 86 DE4 refutation instances and H₂–H₅, HH₃, HH₄ (all by the plain run);
- random strict profiles of the connected k = 4 cores:
  - 20,000 with n ≤ 3, of which 76 need a deferral;
  - 20,000 with n = 4, of which 75 need one;
  - 6,000 with n = 5 and at most two 4-good agents, of which 17 need one;
- 1,800 random and adversarial instances, n up to 12;
- 1,800 general additive instances;
- every NO₂ counterexample of §9.

In total no failure. **The plain neediest-first run alone works on about 99.6% of random profiles.**

**What the deferred agent is** (`nof_roles.log`, the 75 n = 4 profiles whose plain run fails):
- every working deferral defers a frozen agent (135 of 135);
- in 74 of the 75, a frozen agent that holds its top works;
- its displacement chain has length 1 to 3.

This is LB⁺'s k*: the exposed frozen top-holder gives up its top. The agent that wanted it takes it, the chain moves up,
and the deferred agent owns its lower goods.

**The proof architecture this suggests.** One run, one repair, two theorems:
- **(A) When the plain run works:** SD(π) extends unless some frozen agent is exposed beyond what the free slots can
  cover. At k = 3 this is LB⁺'s Theorem A for the R1 run π. At k = 4 the counting must use Lemma N.
- **(B) The repair:** in that case, deferring a suitable frozen agent works, and its effect is the displacement chain of
  Lemma DC. At k = 3 this is Proposition D3 in the main class. The classes with upgraded agents on the chain remain.

So TARGET₄ ⟸ NOF ⟸ (A₄) + (B₄). Each is a statement about one explicit run and one explicit chain, with no
potential, no move catalogue and no search over orders.

**Adversarial climbs against NOF** (`nof_climb_n4.log`, `nof_climb_n5.log`): 70 rounds at n = 4, 5. Every round ends with
exactly one working candidate, the plain run or one deferral, and never with none.

## 12. Toward theorem (A₄): what replaces "exposed agents are leaders"

At k = 3, LB⁺'s count rests on (A3): an exposed agent had all its goods at its turn, so it leads its block, and each
block holds at most one exposed agent, which costs one good. In a neediest-first run at k = 4, define blocks as the
maximal segments that start when every unprocessed agent still has all its goods. Then (B1) and (B2) hold as before:
an agent's better goods are picked inside its own block, earlier.

Lemma N suggests the k = 4 form of (A3). Call a frozen agent x *hard* if some agent that needs its pick cannot be
compensated by one own unpicked good. If x is hard and exposed (a set of its goods inside the unpicked goods plus the
owner's pick is worth more than its pick), Lemma N's case (b) would make x big-top on the goods available at its turn.
Then x was fresh, hence a leader, and its only danger set is its three other goods, so it costs one.

On the screen set this holds for most hard exposed agents but not all (`a3_k4_screen.log`):
- 72 of 73 were fresh at their turn;
- 61 of 73 have exactly that one danger set.

The violations (GM4-S, GM4-P, two gap instances) come from Lemma N's case (a) failing *later*. The needer was
compensable at the time of the contest, but its next good was taken afterwards by another agent, so its compensation
is gone.

So (A₄) must track compensations over time. A needer's compensation is a promise that later picks can break, and the
count has to charge the agent that breaks it. This is the precise form of item 1 under Lemma N.

**With R1 priority.** NOF also holds for the neediest-first order *with* LB's R1 priority (agents that lost a good
first, by need), whose plain run is a genuine R1 run of LB's Phase 1 with need-based choices (`nof_r1.log`):
- 168/168 screen and 164/164 suite instances, the plain run alone on 157 and 154;
- 20,000/20,000 random n = 4 profiles (69 need a deferral) and 6,000/6,000 n = 5 profiles (13).

This R1 form (K4.SDC.NOF.R1) is the better proof target: its blocks are LB's, and at k = 3 it coincides with NOF.

**Cost one, but not leaders** (`a3_k4_screen.log`; "hard exposed" as above, R1 runs):

| | screen set | 5,000 random n = 4 profiles |
|---|---|---|
| hard exposed agents for which one good meets every danger set | 63 of 63 | 297 of 298 |
| ... that were also fresh at their turn | 62 | 245 |

So the k = 4 count keeps LB⁺'s unit price: every hard exposed agent is protected by keeping one good out of the large
bundle. It loses LB⁺'s "one per block": exposed agents that are not leaders occur. Theorem (A₄) must charge each of
them to a terminal of its own block, as Theorem A charges leaders through τ(x), or show that their needers can be
compensated.

## 13. NOF certified by LB₄ʳ's owner step, and its Lean frame

The repository already has an exact, machine-checked notion of "these picks complete":
- LB₄ʳ's states (`lean/EFX/LB4R.lean`) with its three upgrade policies (need-shrinking, envy-free, none);
- the owner step `EFX.LB4R.Output`, whose outputs are sound completions (Theorem 1′₄): EFX₀ allocations with at most
  one bundle of more than two goods;
- Lemma K of `k4/rulef.md`, an exact owner count that is also in Lean.

**Conjecture NOF-K (K4.SDC.NOF.K).** For every strict k = 4 core, one of NOF's candidates (the neediest-first R1 order,
or it with one agent moved last) has an LB₄ʳ output after a run of upgrades of some policy.

Evidence (`nof_lemmak.log`; `k4/sdc/nof_lemmak.py` builds the LB₄ʳ state from the picks and uses PR #33's
transcription `k4/c4_verify_H/lb4r.py` of the Lean definitions):

| data | some candidate has an output | the plain run alone: extends / has an output |
|---|---|---|
| screen set (168) | 168 | 157 / 153 |
| suite, n ≤ 9 (161) | 161 | 151 / 145 |
| 3,000 random n = 4 core profiles | 3,000 | 2,989 / 2,988 |

The plain run sometimes extends without an LB₄ʳ output (4 screen instances). The LB₄ʳ shape (one large bundle, the
other bundles built from bases) is then too narrow, and a deferral restores it. Lemma K's deficit is ≤ 0 on 151 of the
157 plain runs that extend.

**The Lean frame** (`lean/EFX/NOF.lean`, K4.SDC.NOF.LEAN; machine-checked, standard axioms only):
- `EFX.NOF.sdList_spec`: serial dictatorship in any order satisfies Phase 1's run specification `EFX.LB4R.RunSpec`.
- `EFX.NOF.runState_inv`: the state of *every* run satisfying `RunSpec` satisfies LB₄ʳ's invariant `EFX.LB4R.Inv`. This
  is `EFX.LB4R.phase1State_inv` for any order, by the same proof.
- `EFX.NOF.nofOrder`, `EFX.NOF.nofCandidates`: the neediest-first order, as a selection-rule run, and NOF's candidates.
  `EFX.NOF.nofCandidates_perm`: every candidate is a permutation of the agents.
- `EFX.NOF.ConjNOFK r1` and `EFX.NOF.ConjSDCK` (the same for any order) as `Prop`s.
  `EFX.NOF.target4_of_conjNOFK`: **ConjNOFK ⟹ TARGET₄**; `EFX.NOF.target4_of_conjSDCK`: **ConjSDCK ⟹ TARGET₄**.

Correspondence with the Python checks:
- Ties in the need go to the earliest agent in index order, in both.
- An agent with no available good has need 0 in Lean and is processed last in Python. It picks nothing either way,
  so the candidates' picks coincide.
- `lb4r.py`'s upgrade run is one of the runs `EFX.LB4R.UpRun` allows, and its `Output` test (owner's needs from the
  bundle) is Lean's.

So TARGET₄ now follows from one explicit statement about one explicit order: some candidate of NOF admits an LB₄ʳ
output. What is left is mathematics: the counting theorem (A₄) and the deferral theorem (B₄) of §11–§12.

## 14. Lemma N′: the non-compensable contests are LB⁺'s

**Scope of Lemma N.** Lemma N compares need(i) with need(j) because the rule chose i over j. That holds in NO's plain
order (every unprocessed agent other than o is a candidate). With R1 priority it holds only when j was a candidate at
that step: on the screen set, 1 of 308 direct contests violates it (an R1 step chose a lost agent over a fresh j,
`lemma_n_check.log`).

**Lemma N′ (K4.SDC.N2).** In NO's plain order, let x take y at time τ. Let j be a later agent for which y was the
favourite available good at τ and that ends up preferring y to its pick, with need(j) > 0 at τ. Let W be the goods
unpicked at the end plus the owner's pick. If some set of x's goods inside W is worth more than y to x, then:
- x had all its goods available at τ (x is *fresh*), and x has four goods;
- the only such set is the set of x's three other goods, so keeping one of them out of the owner's bundle protects x.

*Proof.*
1. By Lemma N (b), any two of x's goods other than y that were available at τ are together worth less than y.
2. A good of W was available at τ: unpicked goods are never picked, and the owner picks last.
3. So a set T ⊆ W of x's goods worth more than y consists of goods available at τ other than y, and has at least three
   goods.
4. x has at most four goods, so T is the set of its three other goods, all available at τ. Hence x was fresh, and every
   such set is that one set. ∎

On the data the hypotheses and conclusion match exactly (`lemma_n_check.log`):
- every direct contest with need(j) > 0 has x big-top on its available goods (116 of 116 on the screen set, 321 of 321
  on 4,000 random n = 4 profiles);
- every such x that is exposed is fresh and costs one good (47 of 47 and 13 of 13).

**What it means for (A₄).** The frozen agents that LB⁺'s machinery cannot already handle are of two kinds:
- (a) frozen only through contests whose losers were compensable at the time (need(j) ≤ 0); or
- (b) indirect contests (y was not the loser's favourite at τ): 30 of 349 needer pairs on the screen set, 87 of 3,310
  at n = 4.

Those that come only from non-compensable direct contests are, by Lemma N′, exactly LB⁺'s exposed agents: fresh
leaders costing one good. Theorem A's per-block count then applies to them as at k = 3 (one terminal per block).
So (A₄) reduces to two questions:
- that the compensations of kind (a) can be made simultaneously (the loser j takes its z₃, the shrink upgrade of LB₄ʳ,
  when j is not frozen itself);
- that indirect contests reduce to direct ones along a chain.

Both are statements about one run, with no search.

**Kind (a) is not settled by the contest itself** (`comp_check.log`). Take the direct contests whose loser j was
compensable at the time (need(j) ≤ 0). The compensation is still intact at the end in only:
- 78 of 203 on the screen set;
- 1,791 of 2,902 on 4,000 random n = 4 profiles.

"Intact" means j picked z₂, z₃ is unpicked, and j is not frozen, so the shrink upgrade gives j the good z₃. Otherwise:
- z₃ was picked by another agent (43 and 657);
- z₂ was taken by a later agent before j's turn (40 and 226);
- j was frozen itself (42 and 228).

So (A₄) must count frozen agents whose losers' compensation broke later. The plain run still extends on about 99.6% of
profiles, so the count works out in practice. Proving that it does is the open step. The natural form: charge each
broken compensation to the agent that took z₂ or z₃, which then holds a good j values and lies on j's need chain.

## 15. Where the plain run fails: only at the owner step, and LB⁺'s k* at k = 4

**The owner-free count.** Take the plain neediest-first R1 run π and LB₄ʳ's state after need-shrinking upgrades. Let J be
the unpicked goods. Call x *J-threatened* if the owner's bundle, holding J ∩ R_x and some good x does not value, would
strongly envy-threaten x: v_x(J ∩ R_x) > v_x(base(x)). Three facts need no case analysis.
1. *An upgraded agent u is never J-threatened.* u took its best unpicked good g (the eligibility condition of a
   shrink upgrade is monotone in v_u(g), and `up_run` takes the most valuable eligible good). Its other unpicked goods
   are at most two, each worth at most v_u(g), and each worth less than Y_u, since it was available at u's turn. So
   their total is less than v_u(Y_u) + v_u(g).
2. *A free J-threatened agent x with a one-good base is protected by its own best unpicked good* (self-service, using
   its own slot place). The same argument applies.
3. *An agent without a pick values no unpicked good.* All its goods were gone at its turn, and unpicked goods are never
   picked.

So the only agents that need places of others are the *frozen* J-threatened ones. For a block B, let
d(B) = places(B) − need(B), with Lemma K's least service of B's J-threatened agents (sharing allowed inside B) and every
slot place of B's agents counted (`k4/sdc/blocks4j.py`).

| data | blocks with d(B) < 0 (need-shrinking upgrades) | without upgrades |
|---|---|---|
| screen set (168), suite (161) | 0, 0 | 0 (screen) |
| 6,000 random n ≤ 3 core profiles, 6,000 n = 4, 3,000 n = 5 | 0, 0, 0 | –, 46, 7 |

(`blocks4j_*.log`, `blocks4j_none_*.log`.) Without the upgrades, which are Lemma N's compensations, the count fails in
some blocks.

**The per-block form is false nonetheless** (`k4/sdc/blocks_hand.py`, `blocks_hand.log`). Take the strict core with
n = 3, m = 8:
- agent 0 values goods 0, 1, 2, 3 at 18, 8, 7, 6;
- agent 1 values goods 0, 4, 5, 6 at 16, 8, 6, 4;
- agent 2 values goods 7, 5, 3 at 10, 7, 5.

The run:
1. Agent 0 has need 3, agent 1 has need 2, so agent 0 takes good 0.
2. Agent 1 has lost good 0 and takes good 4.
3. A new block starts, and agent 2 takes good 7.

Block 0 = {0, 1}:
- Agent 0 is frozen, since agent 1 prefers good 0 (16) to good 4 (8). It is J-threatened, since 8 + 7 + 6 > 18.
- Agent 1 is free and J-threatened, since 6 + 4 > 8. It is not compensable: 8 + 6 < 16.
- The only place in block 0 is agent 1's. Agent 0 needs one of goods 1, 2, 3 kept out, and agent 1 needs one of goods
  5, 6. These sets are disjoint, so block 0 needs two places and has one.

The plain run still extends. Agent 2's self-service good can be good 3, which also breaks agent 0's danger set. So the
count must be global, with sharing across blocks. This is LB⁺'s "two π-sets meet", now between blocks. The random
profiles never produce this case, but it is a core.

**Every failure of the plain run is an owner-step failure** (`k4/sdc/nof_bad.py`, `nof_bad_*.log`). This covers 82 plain
runs that do not extend: 11 screen, 10 suite, and 24 + 27 + 10 random profiles with n ≤ 3, n = 4 and n = 5. In every one:
- ω > 0, so an owner is needed;
- every block has d(B) ≥ 0, and the owner-free surplus is 0 or 1;
- the best owner's Lemma K deficit (K = ∅) is exactly 1, except in one case with 2 (n = 4, sets
  [[0,3,4,7],[1,3,6],[2,5,6,7],[4,5,7]], values [[6,10,2,7],[2,4,3],[7,10,2,6],[2,3,4]]);
- the working deferrals all lie in the last block B*.

So the plain run fails exactly when choosing the owner costs a place that the count cannot spare. That is LB⁺'s bad
case, where the owner r takes the terminal of k*'s chain.

**NOF-L is refuted (K4.SDC.NOFL).** The two-candidate rule "the plain run, or the run with the last frozen block leader
deferred" generalizes LB⁺'s k* = leader of B* literally. It holds on:
- the screen set (11 repairs) and the suite (10 repairs);
- the 92 instances of `nofl_files.log`;
- 20,000 random n ≤ 3 core profiles (92 repairs);
- adversarial climbs at n = 3, 4 (`nofl_climb_*.log`, no counterexample).

It fails on one of 40,000 random n = 4 profiles and one of 12,000 n = 5 profiles (`nofl_n4.log`, `nofl_n5.log`). Both
are replayed from the definitions by brute force in `k4/sdc/refute_nofl.py` (`refute_nofl.log`).
- n = 4: sets [[0,2,5,6],[1,4,6],[2,3,4,5],[3,4,5,6]], values [[2,4,10,7],[2,4,3],[4,5,8,2],[2,6,10,7]].
  - The order is 0, 2, 3, 1, all one block. Only the deferral of agent 2, the second agent, works.
  - Agent 2 is frozen (agent 1 needs good 4) and threatened by its unpicked goods 2, 3. Its need chain ends at
    r = agent 1, the owner.
- n = 5: sets [[0,1,3,4],[2,3,4,5],[2,3,6],[2,5,6],[4,5,6]], values [[6,4,1,8],[6,8,5,4],[3,4,2],[4,2,3],[4,2,3]].
  - The order is 2, 0, 1, 3, 4. Only the deferrals of agents 0 and 1 work.
  - Agent 0 is the frozen agent threatened by W_r, with its chain ending at r = 4.

NOF itself holds on both.

**LB⁺'s k* at k = 4** (`k4/sdc/nof_kstar.py`, `nof_kstar_*.log`). In both counterexamples, the agent to defer is LB⁺'s
k* in its *defining* form rather than its k = 3 position:
- it is the frozen agent threatened by the owner's bundle W_r = J ∪ base(r);
- its need chain ends at r;
- at k = 3 it is the leader of B* ((A3)); at k = 4 it need not be a leader.

| | n ≤ 3 (20,000) | n = 4 (20,000) | n = 5 (6,000) | screen |
|---|---|---|---|---|
| plain-run failures | 92 | 71 | 13 | 11 |
| exactly one frozen agent threatened by W_r | 86 | 63 | 12 | 10 |
| deferring the first such agent works | 87 | 71 | 13 | 10 |

The exceptions:
- In three n ≤ 3 cases and in D3 (screen), no frozen agent is threatened by W_r. In D3 the short agent is an *upgraded*
  agent threatened through the owner's pick Y_r, its old top, which it stopped needing when it upgraded. This is
  exactly §10's k = 3 class of chains through upgraded agents. There the leader of B*, frozen, works.
- In two n ≤ 3 cases, the first such agent fails, and another deferral works.

So no single explicit choice of k* survives every test, as at k = 3 (§10). The clean statement remains NOF: some one
deferral works.

**What this does to the proof plan.**
- (A₄) is a global count with sharing, not a sum of block counts. Its inputs are the facts above (only frozen
  J-threatened agents need others' places), Lemma N′ (the non-compensable ones are fresh and cost one), and LB₄ʳ's
  shrink upgrades for the compensable ones.
- The count closes owner-free on all data. What fails is only the owner's place.
- (B₄) is LB⁺'s Theorem B with k* defined through W_r and its need chain, not as a leader. The class with upgraded
  agents on the chain needs the adaptation of §10 at k = 4 as well.

## 16. NO and NOF are refuted; a deferral is a rotation; LB₄ʳ with the neediest-first Phase 1

**Two counterexamples** (both replayed from the definitions by brute force in `k4/sdc/refute_nofl.py`,
`refute_nofl.log`).

*Q2* (n = 4, m = 8; the core of `attempts/k4-rulef-bigtop-first.md` that refuted a big-top rule for LB₄ʳ):
- sets [[0,1,3,4],[2,3,6,7],[2,5,7],[4,5,6,7]], values [[2,3,10,6],[2,8,3,4],[2,4,3],[4,8,2,3]].
- The neediest-first R1 order is 0, 1, 2, 3. Neither its picks nor those of any order with one agent deferred extend.
- R1 priority forces agent 1, which lost good 3, ahead of agent 3, whose need is larger. Without R1 the order is
  0, 3, 2, 1 and its picks extend.
- So **NOF-R1 is refuted (K4.SDC.NOF.R1)**, and with it **NOF-K (K4.SDC.NOF.K)**, which uses the R1 order: no
  candidate extends, so none has an output.

*T3* (n = 3, m = 6; a strict k = 4 core found by the adversarial climb of `k4/sdc/nf_lb4r.py`, values rescaled to make
the profile strict):

| agent | goods (value) |
|---|---|
| 0 | 0 (38), 4 (36), 2 (6), 5 (1) |
| 1 | 4 (30), 1 (22), 3 (12) |
| 2 | 0 (38), 4 (28), 1 (20), 3 (12) |

- Of the six orders, only 2, 0, 1 has picks that extend. There agent 2 takes good 0, agent 0 takes good 4, agent 1
  takes good 1, and for example ({4, 2, 5}, {1, 3}, {0}) is EFX₀.
- The neediest-first order (with or without R1) puts agent 0 first: needs −2, −2, −5, ties by index. Then agent 0 takes
  its top 0, agent 1 its top 4, and agent 2 good 1.
- No candidate of NOF extends, and no owner of NO works. So **Conjecture NO (K4.SDC.NO) and Conjecture NOF (K4.SDC.NOF)
  are refuted.**

The agent that must go first is the one of *least* need: agent 2 has the largest gap between its top and its second
good (38 against 28), while agent 0 barely prefers its top (38 against 36). The need score y₁ − y₂ − y₃ does not see
this. SD-C and its R1 form still hold on T3: 2, 0, 1 is an R1 order with insertion choice 2.

**What stays true.** The lemmas about the order are unaffected:
- Lemma N (contests in the neediest-first order) and Lemma N′;
- Lemma DC;
- Proposition D3;
- Theorem DT and the characterization.

So do the Lean frames: they are implications, and ConjNOFK is now known to be false for both values of `r1`.

**Proposition D4: in the main class a deferral is a rotation** (K4.SDC.D4, written proof). Let π be any order,
Y = SD(π), and P the LB₄ʳ state of Y after a run of upgrades. P satisfies `EFX.LB4R.Inv` (`EFX.NOF.runState_inv`,
`EFX.LB4R.upRun_inv`). Every base of P contains its agent's pick: an upgrade adds one junk good to an unmarked agent's
one-good base. Let k be an agent that is FrozenAt in P, and let c = (k = j₀, j₁, …, j_t) be the displacement chain of
Lemma DC for π_k (π with k moved last). Let y be k's pick in SD(π_k). Suppose:
- (R1) t ≥ 1; j₀, …, j_{t−1} are FrozenAt in P; Y_{j_i} ∈ N_{j_{i+1}} (P's needs) for i < t; j_t is not FrozenAt; and
  no j_i is marked.
- (R2) y ∈ R_k ∩ (J ∪ B_{j_t}), J the junk of P.

Let O be a set with y ∈ O ⊆ R_k ∩ (J ∪ B_{j_t}) for which P′ := rotate(P, c, O) passes `RotChecks`. Then P → P′ is a
`RotStep`, and every output X of P′ is an EFX₀ allocation in which every agent holds its SD(π_k) pick. In particular,
if some such P′ has an output, SD(π_k) extends.

*Proof.*
1. *P → P′ is a `RotStep`.* c consists of distinct agents (each j_{i+1} comes after j_i in π) and has at least two.
   The chain condition is (R1): an unmarked agent's pick is its base (`Inv.unmarked`), and its P-pick is Y. O is
   nonempty (y ∈ O) and lies in R_k ∩ (J ∪ B_{j_t}), and `RotChecks` holds by assumption.
2. *Outputs are EFX₀.* By `EFX.LB4R.rotStep_inv`, P′ satisfies `Inv`, so every output is a sound completion
   (`Inv.sound`). By Theorem 1′₄ it is EFX₀.
3. *The picks are in the bases of P′.* By Lemma DC, SD(π_k) gives:
   - j_i (1 ≤ i ≤ t) the good Y_{j_{i−1}};
   - k the good y;
   - every other agent its pick in Y.

   `rotate` moves a base good of j_i (i < t) to j_{i+1}, returns j_t's base to the junk, gives O to k, and leaves every
   other base unchanged. The chain agents are unmarked, so their bases in P are {Y_{j_i}}. Hence:
   - base′(j_i) = {Y_{j_{i−1}}} for 1 ≤ i ≤ t;
   - base′(k) = O ∋ y;
   - an agent off the chain keeps a base that contains its pick, and no good of O came from it, since O ⊆ J ∪ B_{j_t}.

   y is not an upgraded agent's second good, because those goods are not in J.
4. *Conclusion.* An output is a `Completion` of P′, so every bundle contains its agent's base, hence its SD(π_k)
   pick. ∎

D4 makes Lemma KR (K4.RF.KR, in Lean) the counting tool for a deferral. It is the k = 4 form of Proposition D3, which
also required the chain to avoid upgraded agents. `k4/sdc/nof_d4.py` (`nof_d4*.log`) checks it on every plain-run
failure. For each frozen k it tests whether the deferral is a rotation ((R1), (R2)) and whether some rotated state has
an output (exact SAT test of `Output`):

| plain-run failures | screen | suite | random n ≤ 3 | n = 4 | n = 5 |
|---|---|---|---|---|---|
| R1 order: repaired by a deferral that D4 certifies | 8 of 11 | 8 of 10 | 84 of 92 | 71 of 71 | 13 of 13 |
| order without R1 | | | 85 of 91 | 74 of 74 | 15 of 15 |

The uncertified cases all have an upgraded agent on the displacement chain. This is §10's class at k = 3, and D3 had
the same restriction.

**LB₄ʳ with the neediest-first Phase 1** (`k4/sdc/nf_lb4r.py`, `nf_lb4r_*.log`; K4.SDC.NF). Build LB₄ʳ's state from the
picks of the neediest-first order, run the upgrades of a policy, then up to d rotations (every `RotStep`, PR #33's
model `k4/c4_verify_H/lb4r.py`), and test for an output. The table gives the least number of rotations needed.

| data | R1 order: 0 / 1 / 2 | without R1: 0 / 1 / 2 |
|---|---|---|
| screen set (168) | 153 / 15 / 0 | 149 / 19 / 0 |
| suite (164, n ≤ 26) | 146 / 15 / 0 (161 with n ≤ 9) | 145 / 19 / 0 |
| the 92 file instances (DE4 refutations, H₂–H₅, HH₃, HH₄) | 92 / 0 / 0 | 92 / 0 / 0 |
| 20,000 random n ≤ 3, 20,000 n = 4, 6,000 n = 5 core profiles | none needs 2 | none needs 2 |
| instances of the random generators (300 each of rand, hyper, advt4x, advt3x, big8, and big12 without R1) | 1,500: none needs 2 | 1,800: none needs 2 |
| the special instances (T3, Q2, r4253, r3943, the rule-F refutations) | Q2 needs 2, T3 needs 1 | T3 needs 2 (and its unscaled climb form) |

The first column is with R1 priority, the second without.

LB₄ʳ with index insertion needs more than three rotations on H₅ (K4.C4.R), and rule F fails on HH₃ (K4.AD.F). With the
neediest-first Phase 1 both need none, and nothing tested needs more than two. The rotation counts come from a single
implementation, PR #33's independent model of the Lean definitions. Adversarial climbs for an instance needing three
rotations found none (`nf_lb4r_climb*.log`; they rarely reach two).

The Lean frame takes this form directly (`lean/EFX/NOF.lean`, K4.SDC.NF.LEAN): `EFX.NOF.ConjNFR r1 d` is the
statement, and `EFX.NOF.target4_of_conjNFR` proves ConjNFR ⟹ TARGET₄. The proof is the invariant chain
`runState_inv` → `upRun_inv` → `rotReach_inv`, then `Inv.sound`.

**Other order rules** (`k4/sdc/nof_var.py`, `nof_var.log`; evidence only, recorded so that the next attempt does not
repeat it). Every "need score plus one move" rule tested fails somewhere except three:
- "y₁ − y₂ (regret) first, plain or with one agent moved to the end";
- the same with one agent moved to either end;
- need2 with one agent moved to either end.

These hold on T3, Q2, r4253, r3943, the screen set, the suite, 6,000 random n ≤ 3 and 5,000 n = 4 core profiles.
- Moving one agent to the front alone fails for every score, on 2 to 9 instances per data set.
- needall with one deferral fails on lb4-fixed-insertion-n3m6.

Rules of this kind have been refuted one after another (§8, §9, K4.SDC.SEL, K4.SDC.LOCAL, now NO and NOF). So none of
them is put forward as a conjecture.

**Where this leaves the plan.**
- The neediest-first *order* is not canonical: T3 refutes every "neediest first plus one deferral" statement.
- The neediest-first *start* still makes LB₄ʳ short. By D4, its rotations are the deferrals in the main class, and
  Lemma KR's count is how a proof would bound them.

## 17. Two potentials over LB₄ʳ's rotations, both refuted on the data

D4 makes LB₄ʳ's rotations the deferrals, so a proof could run a potential over rotations instead of over orders. Two
natural forms fail. These are evidence only, from a single implementation (PR #33's model); they are recorded so that
the next attempt does not repeat them.

- **RD (descent of Lemma K's deficit):** "a reachable state without an output has a rotation to a state with an output
  or a smaller deficit".
  - Fails on 18 of the 168 screen instances within one rotation (`k4/sdc/rd_check.py`, `rd_check.log`).
  - On T3 the neediest-first state has deficit 1. None of its four rotations lowers the deficit, but two rotations
    reach an output. The deficit is not monotone along a successful rotation sequence.
- **RM (improving rotations):** a rotation whose agent k gains (v_k(O) > v_k(Y_k)) raises every base value on its chain
  and changes no other base. So sequences of improving rotations are finite, and with upgrades this is a Pareto
  potential on base values.
  - At k = 3, LB⁺'s rotation is improving, since b + c > a.
  - RM says every dead end of improving rotations has an output. It fails: 92 of 2,520 starts on the screen set
    (21 instances) and 13 of 60 on the special instances, including Q2 from the R1 start (`k4/sdc/rm_check.py`,
    `rm_check.log`).
  - A successful search sometimes needs a downgrade rotation, as rule F's instance of
    `attempts/k4-rulef-least-count.md` already showed. This is P1 (§1) again, now on LB₄ʳ's pre-allocations.

- **OF (the owner-free count closes globally):** for the neediest-first run without R1 after need-shrinking upgrades,
  the agents threatened by the unpicked goods alone can be served with all slot places (`k4/sdc/of_count.py`,
  `of_count.log`).
  - It holds on the special instances, the screen set, the suite and the 86 DE4 file instances.
  - It fails on 1 of 20,000 random n ≤ 3 and 4 of 20,000 n = 4 profiles, and more often without upgrades (16 of
    20,000 at n = 4).
  - On the first failure (sets [[0,2,5,6],[1,3,4,6],[3,4,5,6]], values [[4,5,2,8],[6,3,8,10],[2,7,6,10]]) the plain
    picks extend nevertheless. The completion needs the owner's needs taken from its *bundle*: Lemma K's kept set K
    unfreezes agents that only the owner needs.
  - So a count that closes the plain run must involve the owner's kept set. The §15 picture "owner-free count closes,
    the owner costs one place" is a property of the R1 runs on the data, not of the order.

So the picture of §1 persists inside LB₄ʳ: completable states are reached only by moves that lower some agent's value,
and neither the deficit nor the base values order the search. What the data support is a bound on the search from a
good start (K4.SDC.NF), not a potential.

## 18. Stress tests of NF, and NOF at k = 3

- **Seeded climbs against NF** (`nf_lb4r.py climb` with `NFSEEDS`, `NFQ=3`; `nf_lb4r_seeded.log`). Climbs from T3 (n = 3)
  and Q2 (n = 4), with and without R1, 40 rounds each, maximize the least number of rotations. None reaches three; the
  instances drift back to zero or one rotation.
- **Gluing.** Copies of T3 glued through one of agent 0's private goods (n = 6, 9) need no rotation. The shared good
  changes the run, and one copy's agents serve as the other copy's owner. Forcing more rotations would need gadgets
  in the style of Proposition H (`k4/c4.md` §7).
- **NOF at k = 3** (`k4/sdc/nof_k3_climb.py`, `nof_k3_climb.log`). Every agent values exactly three goods, so the
  neediest-first order is an R1 run of LB's Phase 1. 110 rounds of climbs at n = 3, 4 minimize the number of working
  NOF candidates, and the minimum stays 1: no counterexample. Proposition D3 proves it in LB⁺'s main bad-case class;
  the classes with an upgraded agent on the chain, or a chain past r (§10), remain.

## 19. NOF2: the neediest-first order with at most two deferrals

Proposition D4 identifies a rotation with a deferral in its main class. So NF's "at most two rotations" has a
serial-dictatorship form, which needs no LB₄ʳ.

**Conjecture NOF2 (K4.SDC.NOF2).** With π the neediest-first order (without R1 priority), for every instance with at
most four relevant goods per agent, one of these extends to an EFX₀ allocation:
- SD(π);
- SD(π with one agent moved to the end);
- SD(π with two agents moved to the end, in either relative order).

By Lemma DC each deferral is one displacement chain. There are at most n² + 1 candidates.

Evidence (`k4/sdc/nof2.py`, `nof2.log`, `nof2_climb.log`; EVIDENCE only):
- T3 needs exactly two deferrals: π = 0, 1, 2, and moving 0 and 1 to the end gives 2, 0, 1.
- Q2, r4253 and r3943 need none without R1. With R1, Q2 needs two.
- The screen set and the suite need at most one: 153 + 15 and 150 + 14 instances.
- 20,000 random n ≤ 3, 20,000 n = 4 and 6,000 n = 5 core profiles need at most one: 104, 65 and 30 need one.
- Adversarial climbs (60 rounds at n = 3, 40 at n = 4, minimizing the number of working candidates) always keep at
  least one.

NOF2 is the explicit statement left after NO and NOF. It shares their weakness: the order is fixed by a need score
that T3 shows is not the right invariant. So it is recorded as the sharpest explicit form consistent with the data,
not as a proof target in its own right. Proving it would need (A₄) and (B₄) of §11 with two repairs. By D4, those
repairs are Lemma KR's rotations in the main class.

## 20. Is SD-consistency free? The favourite-value potential Φ

Adversarial climbs against SD-C seeded from T3 and Q2 (`sdc_climb.py` with seed files, `sdc_climb_seeded.log`; 160 rounds) always end with
exactly one extendable SD outcome, never zero. So SD-C is tight but holds. Which EFX₀ allocations are SD-consistent?

**The potential.** For an allocation X let F_i(X) be agent i's favourite good in X_i, and Φ(X) = Σ_i v_i(F_i(X)).
Moving a non-favourite good never lowers Φ: the giver keeps its favourite, and the receiver's favourite can only
improve. Only moving a favourite away from its holder lowers Φ.

**Conjecture PHI₄ (K4.SDC.PHI4; refuted in §21).** For strict valuations with at most four relevant goods per agent, every EFX₀
allocation that maximizes Φ among the EFX₀ allocations is SD-consistent: some serial-dictatorship order's picks lie
in the bundles. If PHI₄ holds, *SD-C₄ is equivalent to TARGET₄* on strict instances: any EFX₀ allocation yields a
Φ-maximal one, which then extends an SD outcome. So SD-C would be a free normalization of every EFX₀ allocation, not
a weaker stepping stone toward TARGET₄.

Evidence (`k4/sdc/phi_check.py`, `phi_check.log`; exhaustive over all allocations of each instance, raw EFX₀
definition; EVIDENCE only), with at most four valued goods per agent unless stated:

| data | instances | every Φ-maximizer SD-consistent |
|---|---|---|
| n = 2, up to 9 goods, any number valued | 3,184 | 3,184 |
| n = 3, up to 7 goods | 1,247 + 3,922 | all |
| n = 3, up to five valued goods per agent | 3,121 | all |
| n = 4, up to 7 and 8 goods | 280 + 1,081 + 319 | all |
| n = 5, up to 7 goods | 239 | all |
| T3, Q2, r4253, r3943; the 151 screen and 136 suite instances with at most 600,000 allocations | 4 + 151 + 136 | all |

Adversarial climbs (`phi_check.py climb`) maximized the gap: the best Φ of an SD-inconsistent EFX₀ allocation minus the
best Φ of an SD-consistent one, where a gap ≥ 0 refutes. They ran at n = 2 (any k), n = 3 (k ≤ 4 and k ≤ 7) and n = 4
(k ≤ 4), 220 rounds in all, and reach −1 but never 0.

Strictness is needed: with tied values a Φ-maximizer can hold a tied twin of an SD pick. On 4,000 tied two-agent
instances some maximizer was always SD-consistent, every one on 2,983 (`k4/sdc/phi_ties.py`, `phi_ties.log`).

**For general valuations PHI is false** (K4.SDC.PHI, REFUTED; `k4/sdc/refute_phi.py`, `refute_phi.log`, an independent
brute force).
- The instance: n = 3, m = 7, strict, with agents valuing 2, 6 and 6 goods; values [[0,0,55,57,0,0,0],
  [50,1,0,58,76,75,70], [0,11,58,68,41,26,21]].
- The unique Φ-maximizer, Φ = 198, is ({2, 4}, {0, 1, 5, 6}, {3}). It holds no SD outcome: agent 0 parks good 4, which
  it values at 0 and which is agent 1's top.
- In agent 1's bundle, good 4 would let agent 2 strongly envy that bundle.
- The SD-consistent EFX₀ allocations reach only Φ = 191. SD-C itself holds there (28 SD-consistent EFX₀ allocations).

Random search finds this on 2 of 1,395 n = 3 instances with up to seven valued goods per agent, and on none with at
most five. The parking needs a bundle with many goods valued by a third agent.

**Two agents.**
- **Lemma DT₂ (K4.SDC.DT2, written proof).** For two agents with any additive valuations and distinct tops a (agent 1)
  and b (agent 2), some EFX₀ allocation gives each agent its top. So SD-C holds for n = 2 whenever the tops differ.
  - *Construction.* Agent 1 splits M′ = M ∖ {a, b} by the greedy EFX₀ partition for v₁: goods in decreasing v₁, each
    to the part of smaller v₁-value. Agent 2 adds its preferred part C to b, and agent 1 gets a plus the other part D.
  - *Agent 2* is envy-free: v₂(b + C) ≥ v₂(a) + v₂(D), since v₂(b) ≥ v₂(a) and v₂(C) ≥ v₂(D).
  - *Agent 1.* Write θ(S) = v(S) − min_S v. The greedy partition is EFX₀ for identical valuations v₁, so
    v₁(D) ≥ θ₁(C) and v₁(C) ≥ θ₁(D). (The bundle that received the last good had the smaller value then; for the other
    bundle, its own last good is its least.) We need v₁(a + D) ≥ θ₁(b + C).
    - If min(v₁(b), min_C v₁) = min_C v₁: then θ₁(b + C) = v₁(b) + θ₁(C) ≤ v₁(a) + v₁(D).
    - Otherwise v₁(b) < min_C v₁, and θ₁(b + C) = v₁(C) ≤ v₁(D) + min_C v₁ ≤ v₁(D) + v₁(a), because a is agent 1's
      top.
    - If C = ∅, θ₁({b}) = 0.

    The same holds with C and D exchanged, so agent 2's choice does not matter. ∎
- **Lemma Φ₂ (K4.SDC.PHI2, written proof).** For two agents with strict valuations, let X be an EFX₀ allocation that
  maximizes Φ. Then:
  - (A) holds: the agents do not each prefer the other's favourite;
  - (U) holds for agent i unless i prefers a non-favourite good g of X_j to F_i while j values g above every good of
    X_i.

  *Proof.* Replacing a good of S by one the observer values at most as much does not raise θ(S): θ is the sum of all
  values but the least, a coordinatewise monotone function of the values.
  - (A): if each prefers the other's favourite, swap the two favourites. Each agent's own value rises, and the other
    bundle, as it sees it, had a good replaced by one it values less. So EFX₀ is kept, both favourites improve, and Φ
    rises.
  - (U): let i prefer g ∈ X_j ∖ {F_j} to F_i, hence to every good of X_i, and let h ∈ X_i have v_j(h) ≥ v_j(g). Swap g
    and h.
    - Agent i's value rises, and agent j's bundle, as i sees it, had g replaced by h, which i values less.
    - Agent j's value does not fall, and agent i's bundle, as j sees it, had h replaced by g, which j values at most as
      much.
    - i's favourite becomes g and j keeps F_j, so Φ rises.

  Both contradict maximality. ∎ (`k4/sdc/n2_lemmas.py`, `n2_lemmas.log`: the DT₂ construction is EFX₀ on all 15,498
  random distinct-top instances, and both swaps keep EFX₀ in all 1,472 and 12,170 cases.)

The remaining case of Lemma Φ₂ is the only gap in a proof of SD-C for n = 2, through EFX₀ existence for two agents
(cut and choose). In that case agent j values g above all of X_i, and i may also prefer F_j to g. SD-C for n = 2
holds on 20,000 random instances (`k4/sdc/n2_sdc.py`, `n2_sdc.log`).

Plain cut and choose with either cutter is not always SD-consistent on shared tops: both cutters fail on 7% of random
instances. The fix "move the chooser's second good" closes all but rare cases; an adversarial search finds 79 where
neither works. So the remaining case needs the potential, not a fixed protocol. Two further partial results:
- *In the remaining case, if v_i(g) ≥ v_i(F_j)* (with g chosen as i's best good of X_j other than F_j), the
  construction of DT₂ applies with seeds g → i and F_j → j. Agent i cuts M ∖ {g, F_j}, agent j chooses, and the result
  raises Φ. So only "i prefers F_j to g" is open.
  - There, on all 145 random states, some swap of g against a subset T ⊆ X_i keeps EFX₀ and raises Φ.
  - But no canonical T: a subset of X_i covering v_j(g) may not exist (35 states), and the cheapest cover works on 55
    of 110.
- *Lemma P*: a split of M, EFX₀ for v₁ in both directions, with agent 1's top a on one side and its second b₁ and
  agent 2's second b₂ on the other, would settle shared tops. With agent 1 cutting so and agent 2 choosing, either
  choice is SD-consistent. Lemma P fails on 459 of 27,096 random cases, e.g. v = (1, 5, 8, 5)
  (`k4/sdc/n2_lemmaP.py`, `n2_lemmaP.log`).

**What this changes** (written before §21 refuted PHI₄; the conditional stands, its hypothesis does not). If PHI₄ holds, the search for "the right order" in §§8–19 was a search for a normalization that
comes for free. A proof of TARGET₄ need not construct the order; any EFX₀ allocation can be made SD-consistent by
maximizing Φ. Conversely, the explicit orders failed (NO, NOF) because SD-C carries no information beyond EFX₀
existence. What LB₄ʳ's shape (one large bundle) adds is the other half of the structure. Whether a Φ-maximal EFX₀
allocation can also be taken in LB₄ʳ's shape is the natural next question.

## 21. PHI₄ is refuted: SD-consistency is not free at k = 4

**The counterexample** (K4.SDC.PHI4, REFUTED). This is a strict k = 4 core with n = 3, m = 7:

| agent | goods (value) |
|---|---|
| 0 | 0 (25), 3 (50), 4 (55) |
| 1 | 0 (63), 2 (23), 4 (16), 5 (62) |
| 2 | 1 (31), 2 (44), 4 (61), 6 (49) |

- Core conditions: every agent's top is worth less than half its total; private goods are 3 (agent 0), 5 (agent 1),
  and 1 and 6 (agent 2, worth 80 < 105); the agents are connected through goods 0, 2 and 4.
- There are 35 EFX₀ allocations. Their maximum Φ is 173, attained by four allocations, and none of the four holds an SD
  outcome. The SD-consistent EFX₀ allocations, 18 of them, reach only Φ = 167. SD-C itself holds.
- Replayed by the independent brute force `k4/sdc/refute_phi.py` (`refute_phi.log`).

*Mechanism.* In the maximizer ({0, 1, 3}, {2, 5}, {4, 6}), agent 0 keeps good 0, agent 1's top, as a non-favourite
*value supplement*. Without good 0, agent 0 holds 50 and strongly envies agent 2's bundle {4, 6}: good 6 is worth 0
to agent 0, so removing it leaves 55. The general counterexample of §20 *parks* a good; this one *needs* it.

*How it was found.* Random search at k ≤ 4 never met it:
- 4,396 n = 3 instances with up to 8 goods, on top of the about 11,000 of §20;
- 4,034 more with k ≤ 5;
- one failure in 4,702 with k ≤ 6, an instance whose agents value 3, 5 and 4 goods.

Zeroing one of agent 1's five values (good 3, worth 1) keeps the failure and gives the core above
(`k4/sdc/phi_reduce.py`, `phi_reduce.log`). *Reducing a counterexample found at larger k* is a search method worth
reusing. The k ≤ 4 random rates were about 0 in 15,000; at k ≤ 6 about 1 in 5,000.

**The shape version fails with it.** On 3,521 random instances with k ≤ 4 and n = 3 to 5 (`k4/sdc/phi_shape.py`,
`phi_shape.log`):
- some Φ-maximal EFX₀ allocation was D-shaped, i.e. at most one bundle has more than two goods;
- every Φ-maximizer among the D-shaped ones was SD-consistent.

On the counterexample, all four maximizers are D-shaped (bundle sizes 3, 2, 2) and none is SD-consistent.

**What is left.**
- SD-C is again a genuine statement. It may be strictly stronger than EFX₀ existence; no instance separates them yet.
- Lemma DT₂ and Lemma Φ₂ (§20) are unaffected. They concern two agents, where no third agent can force a value
  supplement or a parking.
- The two mechanisms (parking, value supplement) are the k = 4 form of P1's lesson. An SD-consistent EFX₀ allocation
  can require some agent to give up a good that raises Φ, or to hold a good it does not value.

## 22. SD-C and NOF2 at larger k; the lexicographic favourite potential

The PHI₄ counterexample came from reducing a k = 5 failure. So the two explicit statements still open were searched at
larger k, where failures might be easier to meet and then reduce.

- **Random search** (`k4/sdc/sdc_bigk.py`, `sdc_bigk.log`): 10,636 strict instances with n = 3, 4, 5, up to 10 goods,
  and every good possibly valued, plus k ≤ 6.
  - No SD-C failure.
  - NOF2 never needs two deferrals; the plain neediest-first run works on all but 6.
- **Adversarial climbs** with up to four or six valued goods per agent (`k4/sdc/bigk_climb.py`, `bigk_climb.log`, 410
  rounds), against SD-C (the number of extendable SD outcomes) and NOF2 (the number of working candidates).
  - Each was run plain and with the number of complete EFX₀ allocations as a secondary objective.
  - Every round ends with exactly one extendable outcome or working candidate, never zero.
  - With the secondary objective, the climbs reach instances with only 3 EFX₀ allocations at n = 3, one of them
    SD-consistent.
- **The lexicographic favourite potential** (`k4/sdc/phi_lex.py`, `phi_lex.log`). For an order π, maximize
  (v_π₁(F_π₁), v_π₂(F_π₂), …) lexicographically over the EFX₀ allocations.
  - On both PHI counterexamples the maximizers are SD-inconsistent for the orders that start with agent 2. On T3 and on
    318 random instances every order works.
  - "For some π" is SD-C again: SD(π) is the lexicographic upper bound, attained iff it extends.

So SD-C and NOF2 survive at larger k as well, and no potential found so far explains SD-C.

## 23. Rotation completeness: every order is a good start for LB₄ʳ, but the rotations must be chosen

D4 identifies LB₄ʳ's rotations with deferrals, and the reachable states of an LB₄ʳ run form a finite graph. So one
can ask, exhaustively, whether rotations are a *complete* repair move.

**Conjecture RC (K4.SDC.RC).** For every strict k = 4 core and every order of the agents, there is an upgrade policy
and a finite sequence of rotations after which the state of that order's serial dictatorship has an LB₄ʳ output. The
number of rotations is not bounded: Proposition H (K4.C4.R) forces about t − t/3 of them on H_t for any fixed order.

Evidence (`k4/sdc/rot_complete.py`, `rot_complete.log`; every reachable state searched; EVIDENCE only):
- *every* order with n ≤ 5, and 20 to 30 sampled orders at n = 6 to 9, plus LB₄ʳ's own Phase 1 with index insertion;
- the special instances, the screen set, the suite (also with n ≤ 9), and random cores: 3,000 at n ≤ 3, 1,500 at
  n = 4, 600 at n = 5.

In all, 143,476 start runs, none dead; the two suite runs overlap. No start needs more than **two** rotations at these sizes:

| data | starts | 0 rotations | 1 | 2 |
|---|---|---|---|---|
| screen set | 4,237 | 3,556 | 620 | 61 |
| suite (n ≤ 9, sampled orders above 5) | 4,548 | 3,717 | 767 | 64 |
| random n ≤ 3 / n = 4 / n = 5 cores | 19,928 / 37,500 / 72,600 | 97% / 97% / 99% | the rest | 0 |

The repository already knew that every *R1 insertion order* of LB₄ʳ works with at most three rotations exhaustively
at n ≤ 4 (K4.LB4R). RC adds that any serial-dictatorship order works as a start. The neediest-first order (NF, §16) is
special only in needing no rotation on H_t and HH_t.

**The rotations must be chosen** (`k4/sdc/rot_traps.py`, `rot_traps.log`). In the graph of states reachable from all
starts, some states are *traps*: no output is reachable from them.
- There are 42 trap states on 18 of the 168 screen instances, and one on Q2.
- On one screen instance, a start with a particular upgrade policy is a trap, while another policy from the same
  order succeeds.

So a proof of RC cannot be "any rotation sequence terminates in success". It must choose the rotation, as LB⁺'s
Theorem B chooses k*. The refuted potentials of §17 show that neither the deficit nor the base values guide that
choice.

**Lean frame** (`lean/EFX/NOF.lean`, K4.SDC.RC.LEAN): `EFX.NOF.ConjRC` (every order, some policy, some d) and
`EFX.NOF.target4_of_conjRC` (ConjRC ⟹ C₄∃ ⟹ TARGET₄). The implication uses only the agents' own list as the order.

## 24. LB⁺'s rotation choice, applied greedily, is not enough at k = 4

The greedy repair rule (`k4/sdc/greedy_kstar.py`, `greedy_kstar.log`) applies LB⁺'s choice at every step:
- r is the last agent of the order that is neither frozen nor marked;
- k* is the first FrozenAt agent threatened by W_r = J ∪ base(r) that has a need chain to r;
- rotate k* along a shortest such chain, with the largest admissible base, and move k* to the end of the order (D4).

Results:
- **Screen set:** this succeeds from 3,946 of 4,069 starts, every order with n ≤ 5 and the best of the three upgrade
  policies. It fails from 123 starts on 21 instances.
- **Special instances:** it fails from 7 of 174 starts.

The failures do not have one cause (`k4/sdc/rot_classify.py`, `rot_classify.log`). Among the first rotations that do
lead to an output within two steps:
- many chains end at a non-frozen agent other than r, so a different owner is needed;
- many have k not threatened by the bundle of the chain's end;
- in some starts a rotation of LB⁺'s kind exists, but the greedy's own choices (first k*, shortest chain, largest base)
  lead to a state with no k*.

This is the k = 4 form of the classes that Proposition D3 left open at k = 3 (§10), made larger by the owner choice. A
rule that also picks the owner and the chain end would be one more case-based rule of the kind refuted throughout
this note. It is not pursued. What RC needs is a reason why *some* rotation avoids the traps of §23.

## 25. Three proof structures for RC and NF, each with its obstruction

After §23–§24 the open step is a reason why some rotation avoids the traps. Three structures that would supply one
were tested and fail.

1. **A lexicographic potential** (`k4/sdc/lex_check.py`, `lex_check.log`). Call a rotation *lex-improving* if it
   reaches an output, or lowers Lemma K's deficit, or keeps the deficit and raises the base values. Three readings of
   "raises" were tested: Pareto, the sum, or the favourite sum Φ.
   - If every state without an output had a lex-improving rotation, (deficit, values) would be a potential proving RC.
   - Lex-traps exist on T3 and Q2 for each reading. They exist even when the search follows only lex-improving
     rotations from the starts (`LEX_MODE=guided`).
   - So no potential of this form works. The deficit must sometimes rise, or the values fall, on the way to an
     output.
2. **PS₃ through LBO** (`k4/induct.md` §4b). PS₃ asks for an EFX₀ allocation of a k = 3 instance in which nobody
   envies a prescribed agent w. It would give TARGET₄ for instances whose only 4-good agent has a private good
   (K4.IND.STEP).
   - With w processed last, LB⁺'s Theorem A count for owner w loses one terminal for each block whose exposed leader's
     need chains all end at w. There are at most |N_w| ≤ 3 such blocks, since each chain enters w through a distinct
     good w needs.
   - Lemma 7 (|N_w| = 0) and Lemma 8 cover the cases without such blocks.
   - If some other agent's top is w's top, w misses it in every run with w last. Then the count can be short by up to
     three, and one rotation of Theorem B's kind repairs one block. This is the open step of LBO in count form.
3. **"Neediest-first runs expose at most one 4-good agent"** (`k4/sdc/exposed4.py`, `exposed4.log`). This would let
   the proved Theorems A₄, B₄ʷ and A₄ᵀ (K4.C4.AB, K4.C4.AB.L) cover the runs. It is false.
   - On 20 of the 168 screen instances, the neediest-first R1 run after envy-free upgrades exposes two or more 4-good
     agents with respect to r. LB₄ʳ's index runs do so on 21, random R1 runs on 22.
   - Most of these runs have an output without a rotation anyway, so the counts of K4.C4.AB are not tight there.

What a proof needs, stated once more in the sharpest form the data allow: a *count with sharing* that handles two or
more exposed 4-good agents (K4.C4.GAP), together with a rule for the rotation that the count itself designates.
LB⁺'s Theorem A designates k*, the unique short block. At k = 4 the short part can involve several blocks and several
owners.

## 26. The smallest gap configurations, Lemma Ωʳ, and ω as a potential from the neediest-first start

**The three smallest configurations of K4.C4.GAP** (`attempts/k4-c4-exposure-counting.md`, rebuilt from their
recorded picks by `k4/sdc/gap_explain.py`, `gap_explain.log`) are repaired by three mechanisms, all inside LB₄ʳ:
1. *Exposed non-leader* (n = 3, m = 5): a rotation absorbs the danger set. The frozen exposed 4-good agent is rotated
   to its needer with its two danger goods as base O.
   - J loses those two goods and gets the chain end's one good back, so ω falls from 1 to 0 and an output with no
     owner exists.
   - Lemma K's deficit was 1 before the rotation.
2. *Deficit 2* (n = 2, m = 5): this is a deficit of LB⁺'s count with owner-base needs, not of Lemma K.
   - With the owner's needs from its bundle and the kept set {4}, the owner's bundle beats the good it needed. The
     frozen agent is released and serves itself.
   - Lemma K's deficit is 0, and an output exists without rotation.
3. *Earlier-block deficit* (n = 3, m = 6): the free exposed 4-good agent is the owner (deficit −1), and an output
   exists without rotation.

So two of the three are already closed by Lemma K's count (kept set, choice of owner). The third is closed by ω.

**Lemma Ωʳ (K4.SDC.OMEGA, written proof; checked on every rotation met, `k4/sdc/lemma_omega.py`, `lemma_omega.log`).**
Let P be an LB₄ʳ state with `Inv`. Let P → P′ be a RotStep along k = x₀, x₁, …, x_t with new base O for k, such that:
- |O| = 2 and v_k(O) > v_k(Y_k);
- the chain end x_t has a one-good base and is not frozen.

Then ω′ = ω − f − u, where f is the number of chain agents x₁, …, x_t not frozen in P′, and u the number of agents
off the chain frozen in P and not in P′. No agent off the chain becomes frozen.

*Proof.* Write ω = |J| − Σ_i cap(i), with cap(i) = 0 if i is frozen and 2 − |B_i| otherwise.
1. *Junk.* O ⊆ J ∪ B_{x_t}, and x_t's base returns to the junk, so |J′| = |J| − |O| + |B_{x_t}| = |J| − 1.
2. *Needs.* k's new base is worth more than its pick, so NA′ ⊆ NA by the validity step of Lemma KR (`k4/rulef.md` §3,
   `EFX.LB4R.NA_rotate_inv`): each chain agent's new needs are worth more than the good it needed, and k's are worth
   more than v_k(O) > v_k(Y_k); the argument does not use where the chain ends.
   Hence an agent off the chain, whose base is unchanged, stays free if it was free, and may stop being frozen.
3. *Caps.*
   - k was frozen (cap 0) and has two goods after (cap 0).
   - x₁, …, x_{t−1} were frozen (cap 0).
   - x_t had cap 1.
   - After the rotation every chain agent x_i (i ≥ 1) has a one-good base, so cap 1 if free, 0 if frozen.

   So Σ cap′ − Σ cap = f − 1 + u, and ω′ − ω = −1 − (f − 1 + u) = −f − u. ∎

With |O| = 3 the same count gives ω′ ≤ ω − 1 always, k's cap being −1, but k then holds a three-good base and must be
the owner. Since ω ≤ 0 gives an output with no owner (`EFX.LB4R.output_none_of_omega`), ω is a natural potential: a
repair that lowers it at every step uses at most ω(start) rotations.

**ω as a potential** (`k4/sdc/omega_check.py`, `omega_check.log`; `k4/sdc/omega_nf.py`, `omega_nf.log`).
- *From every start it fails.* At Q2's R1 start every rotation raises ω, by 1 or 2, and none lowers Lemma K's
  deficit; two rotations still reach an output. So no nonnegative combination of ω, the deficit and the negated base
  values can be a potential from every start.
- *From the plain neediest-first start it works on all data:*
  - with envy-free upgrades, **some ω-decreasing rotation sequence reaches an output on every start that needs
    rotations**: 20 screen, 20 suite, 85 random n ≤ 3, 88 random n = 4 and 18 random n = 5 profiles, 231 in all;
  - with shrink upgrades it misses twice;
  - *every* ω-decreasing sequence reaches an output (no trap) on 228 of the 231.
  - In the 3 exceptions (n = 4, e.g. sets [[0,1,2,3],[0,2,6],[1,4,5,6],[3,4,5,6]], values [[2,4,7,10],[2,3,4],
    [1,4,8,6],[10,3,6,8]]), the shortest repair is one rotation that lowers ω from 2 to 0. It is a downgrade: agent 0
    gives up its top for its third good, and agent 3, which needed three goods, takes agent 0's top and releases two
    frozen agents. Some other ω-decreasing rotation leads into a trap.
- *Two-good improving rotations alone are not enough:* restricted to Lemma Ωʳ's rotations, the search is trap-free from
  some policy on only 7 of the 40 file instances that need rotations. The useful rotations include downgrades that
  satisfy an agent needing several goods (the n = 4 example) and three-good bases.

**Conjecture NF-Ω (K4.SDC.NFO).** For every strict k = 4 core, the state of the plain neediest-first run after
envy-free upgrades either has an output, or has a RotStep that lowers ω and leads to a state with the same property.
Equivalently, an output is reachable by rotations each lowering ω, so at most ω(start) of them. This adds to NF (§16)
a potential that bounds the search. A proof needs the existence step:
- at a state reached this way, without an output, some rotation lowers ω without entering a trap;
- Lemma Ωʳ computes ω′ exactly for the improving two-good rotations, and the general formula
  ω′ − ω = |B_{x_t}| − |O| − (Σ cap′ − Σ cap) covers the others.

## 27. The repairing rotation from the neediest-first start: what it is, who owns afterwards, and what a proof must use

Throughout, P is the state of the plain neediest-first run (`need2`, no R1 priority) after envy-free upgrades. The data
are the starts P without an output: 1 special instance (T3), 21 screen, 21 suite (the two sets overlap), and 118 random
profiles with n ≤ 3, 100 with n = 4 and 19 with n = 5 (seeds 91–93). That is 280 starts in all.

**Greedy ω repairs every start** (`k4/sdc/omega_greedy.py`, `omega_greedy.log`).
- *Rule.* Take the RotStep with the least resulting ω, with an output counting as −∞ and ties broken by Lemma K's
  deficit. Stop at an output; fail if no rotation lowers ω.
- *Result.* The rule reaches an output on all 280 starts: 279 in one rotation, and T3 in two (ω 2 → 1 → output). The
  variant that prefers improving rotations does the same.
- *ω at these starts:* 1 on 86, 2 on 126, 3 on 41, 4 on 22, 5 on 5. One rotation therefore usually reaches an output
  while ω stays positive, so that output has an owner. Lemma Ωʳ's count (ω falls by f + u) is not what closes these
  starts.

**What the greedy rotation is** (`k4/sdc/omega_classify.py`, `omega_classify.log`; chain k = x₀, …, x_t, new base O).
| property | starts (of 280) |
|---|---|
| downgrade, v_k(O) ≤ v_k(Y_k) | 175 |
| improving | 105 |
| k threatened by W_t = J ∪ B_t | 264 |
| the chain ends at LB⁺'s owner r (the last agent of the order neither frozen nor marked) | 263 |
| \|O\| = 1 / 2 / 3 | 120 / 145 / 15 |
| chain length 2 / 3 / 4 / 5 | 147 / 115 / 17 / 1 |
| the chain end frozen afterwards | 95 |

LB⁺'s rotation (k threatened by W_r, a chain to r, a better base) is the minority shape. Most repairing rotations are
downgrades: k gives up its pick for one or two junk goods.

**NF-B, Theorem B's shape from the neediest-first start** (`k4/sdc/nf_thmB.py`, `nf_thmB.log`).
- *Statement.* Some FrozenAt agent k threatened by W_r, with a need chain to r and some base O, gives an output in one
  rotation.
- *Result.* It holds on 264 of the 280 starts, and some one-rotation repair exists on 279.
- *Failures.* Of the 15 failures with a one-rotation repair, 13 have no repairing chain that ends at r. In
  rc-n5m12-f2, for example, r holds its favourite and needs nothing, so no chain can end at r; in nsw-strict-n4m8 the
  only chain to r does not repair. The other 2 (random profiles r11278, seed 91, and r15366, seed 92) have a
  repairing chain to r, but its k is not threatened by W_r.

**Who owns the output after the repairing rotation** (`k4/sdc/nf_owner.py`, `nf_owner.log`; every repairing rotation
and every owner of an output of the rotated state).
- *Owner counts* (starts on which some repairing rotation leaves an output with that owner, of 279):
  | owner | starts |
  |---|---|
  | k itself | 220 |
  | no owner | 161 |
  | r at the chain end | 101 |
  | an agent off the chain | 116 |
  | a middle chain agent | 22 |
  | a chain end other than r | 7 |
- *Every one of the 279 starts* has a repairing rotation whose output is owned by k, by r at the chain end, or by no
  one. k or no one alone covers 275; the other 4 are the screen and suite copies of c4x-n3m6-ef-bases and 2 random
  profiles.
- These are the three mechanisms the proved theorems already use:
  - k as owner after the shift is LB⁺'s Theorem B, where k* rotates and becomes the owner;
  - r staying owner after a rotation to r is Theorem B₄ (K4.C4.AB);
  - no owner is ω′ ≤ 0 with two-good bases (`EFX.LB4R.output_none_of_omega`).

  What is missing is a count that says one of them always applies after a suitable rotation.

**The rotation is unavoidable; the owner step is not too strict** (`k4/sdc/frozen_owner.py`, `frozen_owner.log`).
- *Relaxing the owner step* (any agent may own, frozen or not; the other agents keep LB₄ʳ's caps; every pair checked
  for EFX₀ directly by brute force over the junk) repairs only 27 of the 280 starts, all random profiles with n ≤ 4.
- *The bases of P extend to an EFX₀ allocation at all* (any placement of the junk, no caps) on only 69 of the 280.
- On the other 211, no EFX₀ allocation contains the bases of P. Some base must change (a rotation, or a deferral in
  serial-dictatorship terms, K4.SDC.D4). So the gap K4.C4.GAP is in the picks, not in LB₄ʳ's owner step.

**Excess one is not repaired from every start** (`k4/sdc/omega_small.py`, `omega_small.log`).
- *Test.* From every order's serial-dictatorship start (n ≤ 5), each upgrade policy, and every state reachable by
  RotSteps, ask whether some rotation reaches an output or lowers ω.
- *Result at ω = 1:* it fails on 31 of 132 such states without an output (screen), 31 of 128 (suite) and 3 of 16
  (special: T3 and Q2).
- *Consequence.* A local statement "excess one is closed by one rotation" is false in general. A proof of NF-Ω or NF
  must use what the neediest-first order guarantees, not only the state's counts.
- *Side remark.* States with ω ≤ 0 and no output exist (8 and 2 on the screen set). Each has a three-good base, which
  `output_none_of_omega` excludes.

**Where this leaves the gap count.** A proof of NF along these lines has three parts:
1. *(order)* a property of the neediest-first start that fails for other orders, such as the ω = 1 states above;
2. *(existence)* from that property, a frozen k and a need chain k → … → t such that after the shift (x_i takes
   B_{x_{i−1}}, t's base returns to the junk) one of the three mechanisms applies: k owns W = J ∪ B_t, r = t stays
   owner, or ω′ ≤ 0;
3. *(iteration)* T3: the first rotation lowers ω from 2 to 1 without an output, so the property in (1) must survive
   one rotation.

The data say (2) is true at every start tested. The data also say the rotation is usually a downgrade for k: the
count has to credit k's new, smaller base O with the goods it frees for the others. LB⁺'s count, where k* gains, does
not do that.

## 28. Matching domination: every order's picks are value-dominated, and where domination stops

**Definitions.**
- A *matching* gives each agent at most one good it values, and no good to two agents.
- A complete EFX₀ allocation X *value-dominates* a matching (or a partial allocation) μ if v_i(X_i) ≥ v_i(μ_i) for
  every agent i.
- This is weaker than "μ extends" (μ_i ∈ X_i, the target of SD-C and NOF) and implied by it.

**Conjecture MD (K4.SDC.MD).** In every instance with at most four relevant goods per agent, every matching is
value-dominated by a complete EFX₀ allocation.
- MD contains TARGET₄ (take the empty matching).
- MD is order-free: it holds for every order at once, while extendability needs a good order (SD-C) or deferrals
  (NOF2), and the neediest-first picks do not extend on T3.

**Lemma SDPO (K4.SDC.SDPO, written proof; checked on 332 instances with n ≤ 6, `k4/sdc/sd_po.py`, `sd_po.log`).** With strict
values (an agent may stay unmatched), the serial-dictatorship outcomes over all orders are exactly the Pareto-optimal
matchings. So MD is equivalent to *value domination of every order's picks* ("VD").

*Proof.*
1. *(⊆)* Let μ′ Pareto-dominate Y = SD(π), and let i be the first agent of π with μ′_i ≠ Y_i.
   - The agents before i hold the same goods in both, so μ′_i was available when i picked.
   - i took its favourite available good, so v_i(μ′_i) < v_i(Y_i) by strictness, which contradicts domination.
   - Hence μ′ = Y.
2. *(⊇)* Let μ be Pareto-optimal and nonempty.
   - Let each matched agent that does not hold its favourite good point to the holder of that good. The holder exists
     and is matched, since otherwise the agent could take the good.
   - If no matched agent held its favourite, these pointers would form a cycle among matched agents. Trading along it
     would improve each agent on it.
   - So some agent a holds its favourite. Put a first and remove a and μ_a; μ stays Pareto-optimal in the rest.
     Induct, with "favourite" meaning the favourite remaining good. Unmatched agents go last.
3. *(Equivalence)* Every matching is dominated by a Pareto-optimal one, which by step 2 is an SD outcome. ∎

**Evidence for MD** (`k4/sdc/vdom.py`, `vdom.log`; `k4/sdc/mdom.py`, `mdom.log`; SAT on sdclib's EFX₀ encoding with
the value thresholds as unit clauses).
| data | orders / maximal matchings | not dominated |
|---|---|---|
| every order: special, screen, suite, 7,600 random core profiles (n ≤ 5) | 175,250 orders | 0 |
| every maximal matching: special, screen, suite, 4,700 random core profiles | 251,706 matchings | 0 |
| the 1,413 hard profiles printed in `results/k4_sdc/*.log` (climb results, counterexamples, failures of §15–§27) | 84,762 matchings | 0 |
| 888 random instances with up to 8 relevant goods per agent (`k4/sdc/mdom_bigk.py`, n = 3, 4) | 34,226 matchings | 0 |

- Adversarial climbs (`k4/sdc/mdom_climb.py`, `mdom_climb.log`) minimize the number of dominating allocations of the
  hardest Pareto-optimal matching, from random starts and from the GM4 instances below. They never fall below one.
- On the neediest-first picks, the picks themselves extend on 147–157 of the 161–168 curated instances, and are
  dominated on all of them.

**Where domination stops** (`k4/sdc/pdom.py`, `pdom.log`; `k4/sdc/refute_md2.py`, `refute_md2.log`).
- *Setting.* Partial EFX₀ allocations whose bundles lie inside the holders' relevant sets, tested by their
  Pareto-maximal value vectors.
- *One two-good bundle, the rest at most one good (MD₁).* Every such allocation is dominated:
  - 861 vectors on the screen set, 840 on the suite, 19 on the special instances;
  - 2,805 on the larger-k random instances.
- *Two two-good bundles.* Domination fails on 20 screen instances: the GM4 family, whose GM4-E refutes P1
  (K4.SDC.P1).
  - Example GM4-A: sets [[0,2,5,6],[1,4,5,6],[2,3,5,6],[3,4,5,6]], values [[3,6,2,10],[1,6,8,4],[2,7,8,4],[6,3,4,8]].
  - X = ({0,2}, {1,4}, {5}, {6}), with good 3 unallocated, is EFX₀ with values (9, 7, 8, 8).
  - None of the 16 complete EFX₀ allocations reaches these values.
  - Replayed by brute force over all 4⁷ allocations, without SAT and without shared code (`refute_md2.py`). The same
    replay finds all 337 matchings of GM4-A dominated.

So the obstruction behind P1 needs two agents that are each held above their best available single good by a pair.
With at most one such agent (LB's owner has the only large bundle), domination survived every test. MD₁ is recorded
as K4.SDC.MD1, the two-pair failure as K4.SDC.MD2.

**What MD says about LB₄ʳ** (`k4/sdc/imp_only.py`, `imp_only.log`).
- *LB₄ʳ's outputs need not dominate the picks*, because a downgrading rotation lowers k. With improving rotations only
  (v_k(O) > v_k(Y_k), so every reached state dominates the picks), LB₄ʳ reaches an output from the neediest-first start
  on 20 of the 21 screen starts and T3, for some upgrade policy. It fails on nsw-strict-n4m8 for every policy.
- *There, the neediest-first picks (3, 4, 7, 6) extend in exactly one way* (brute force over all 4⁸ allocations):
  X = ({3}, {4}, {1,2,7}, {0,5,6}). Two agents absorb junk beyond two goods. LB₄ʳ's Output, with one owner and caps
  of 2 − |B| for the others, cannot express this. The repair LB₄ʳ finds instead is a downgrading rotation (§27).
- So part of the gap K4.C4.GAP comes from the shape of LB₄ʳ's output, not from the instance. A completion step that
  lets several agents take junk that nobody else values enough would need fewer rotations. MD says that a dominating
  allocation always exists.

## 29. One improving chain from every order, with a free completion

§28 shows that a dominating allocation exists. This section asks how far it is from the picks. LB₄ʳ's rotations are
an awkward measure, because its Output allows a single owner, and its useful rotations are downgrades (§27). Here
instead:
- *States* are partial allocations B, each agent holding a base inside its relevant goods; the rest is the junk J.
- *A state is terminal* when its bases extend: some complete EFX₀ allocation gives every base good to its holder, with
  the junk placed anywhere (SAT on sdclib's encoding). This is the free completion.
- *The move* is the chain of Draft and Exchange (`paper/k3-simple`, Lemma chain) with general improving sets.

**Improving chain.** A chain is distinct agents x₀, …, x_t (t ≥ 1) with disjoint sets H₀ ⊆ J ∪ B_{x_t} and
H_i ⊆ J (i ≥ 1), all inside the receivers' relevant goods, such that:
- v_{x₀}(H₀) > v_{x₀}(B_{x₀}), and
- v_{x_i}(B_{x_{i−1}} ∪ H_i) > v_{x_i}(B_{x_i}) for i ≥ 1.

Applying it, x₀ takes H₀, each x_i takes B_{x_{i−1}} ∪ H_i, and the rest of B_{x_t} becomes junk. Every agent on the
chain gains and the others keep their bases. So every state reached from the picks value-dominates them, and a
terminal state reached this way proves MD for that order.
- LB₄ʳ's improving rotation (§27) is the special case where x₀ is frozen, x₁, …, x_{t−1} are frozen, and H_i = ∅ for
  i ≥ 1.
- At k = 3, Draft and Exchange's chain is the case H₀ = {b_x, c_x} ⊆ J.

**Conjecture OC (K4.SDC.OC).** In every instance with at most four relevant goods per agent, for every order π:
- the serial-dictatorship picks of π extend to an EFX₀ allocation, or
- after one improving chain they do.

OC implies MD for every order (each chain agent gains), hence MD by Lemma SDPO, hence TARGET₄.

**Evidence** (`k4/sdc/de_free.py`, `de_free.log`; `k4/sdc/de_free_bigk.py`, `de_free_bigk.log`).
| data (every order) | starts | picks extend | one chain | more |
|---|---|---|---|---|
| special (n ≤ 5) | 174 | 105 | 69 | 0 |
| screen (n ≤ 5) | 4,069 | 3,540 | 529 | 0 |
| suite (n ≤ 5) | 4,327 | 3,807 | 520 | 0 |
| 3,000 random core profiles, n ≤ 3 | 16,972 | 16,495 | 477 | 0 |
| 1,500 random core profiles, n = 4 | 36,000 | 35,208 | 792 | 0 |
| 150 random core profiles, n = 5 | 18,000 | 17,819 | 181 | 0 |
| the hard profiles of `results/k4_sdc/*.log` (n ≤ 4) | 19,940 | 17,602 | 2,338 | 0 |
| random instances with up to 8 relevant goods per agent (n = 3, 4) | 5,106 | 4,959 | 147 | 0 |

So no start tested needs more than one chain: 99,482 starts at k = 4, plus 5,106 at larger k. That includes T3,
whose neediest-first picks need two LB₄ʳ rotations.

**What the move needs** (the same files; `k4/sdc/de_free_shape.py`, `de_free_shape.log`).
- *Bigger sets.* With |H| ≤ 2 and bases of at most three goods, 70 of the 2,149 screen starts with n ≤ 4 have no
  repair, even with rings added. Example: c4min-tlam-n3-m6, picks (5, 4, 3). Agent 0 must give up its top (worth 8)
  for three junk goods worth 4 + 3 + 2, so that agent 2 can take the top.
- *Rings are not needed:* with large enough sets, chains alone repair every start.
- *LB₄ʳ's own improving rotations are not enough from every order* (`k4/sdc/imp_extend.py`, `imp_extend.log`; with the
  same free completion and every upgrade policy).
  - They fail on 6 of the 174 special starts (Q2), on 26 of the 4,069 screen starts and on starts of 2 suite
    instances.
  - From the neediest-first order they never fail: 46,000 random profiles, 1,587 logged ones and the curated sets. At
    most two rotations are needed; two only on T3, 2 random profiles and 4 logged profiles.
- *Shapes on the screen set* (147 starts whose picks do not extend):
  - 124 have a repairing chain in which only x₀ takes junk;
  - 137 have one that starts at an agent whose pick another agent needs;
  - the rest need junk for a middle agent, or start at an agent nobody envies (often a swap: x₀ takes x₁'s base and
    x₁ takes x₀'s base plus junk).

**Where the difficulty now sits.** OC moves the whole difficulty into the free completion: when do given bases extend?
- At k = 3, Draft and Exchange's finishing test counts the blockers' leftover goods (|H_o| ≤ |F| − 1). Its Improvement
  Lemma then needs up to 4n trades, because its completion has a single finisher.
- At k = 4, one chain suffices on the data once the completion is free.

A proof along these lines needs:
1. a Hall-type characterization of extendable bases (several agents absorbing junk, unlike LB₄ʳ's single owner);
2. the existence of a chain that repairs a violated condition. The counts of §26–§27 are the one-owner special case of
   step 1.
