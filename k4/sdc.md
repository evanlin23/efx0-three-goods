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
