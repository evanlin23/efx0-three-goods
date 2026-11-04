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
