# k = 4: what a minimal counterexample to Conjecture RF can look like

Workstream `proof/k4-rf-min` (asked for by the coordinator, 2026-11-27 05:25). Conjecture RF (receiver first) is row
K4.SDC.RF, `k4/sdc.md` §31 end. Here, *start* means the picks Y of a serial-dictatorship order whose picks form a maximum
matching, *receiver* an agent with a pick that no other agent prefers to its own (a pickless agent "prefers" any good it
values), *frozen* an agent with a pick that some other agent prefers to its own, *junk* J the goods nobody picked, and
*OC₁* the conjecture's completion statement (a one-absorber completion of the picks, or one after one improving move).

**Results.**
1. *What a minimal RF counterexample can be assumed to satisfy* (§1, Proposition RF-𝒦, proved). For TARGET₄, RF is
   needed only on the class 𝒦 of possible minimal counterexamples to TARGET₄: strict connected k = 4 cores with β ≥ 5,
   6 ≤ n ≤ 3(β − 1), no agent with two private goods, no good of degree 2 shared by two P3 agents, no double edge without
   a Q4 agent, no claw, and profiles inside K4.MC5's and K4.MC8's recorded sets. RF failures outside 𝒦 refute RF as
   stated but not the TARGET₄ route. RF is not closed under the reductions themselves (§1), so they enter this way,
   not as reductions of RF.
2. *Lemma RF-TOP and its corollary* (§2, proved). Moving an agent that holds its top good to the front of an order
   changes no pick. Hence RF forbids a receiver holding its top at any start where OC₁ fails. In particular, **RF implies
   OC₁ at every start of every core with an agent whose top good is private.** Every OC₁ failure in such a core is
   therefore an RF counterexample that needs no reordering to detect: a cheap target for the hunt.
3. *Lemma ABS* (§3, proved; uses k ≤ 4). At any serial-dictatorship start, if some agent holds a private good and no
   frozen agent values the whole junk set above its pick, then the picks have a one-absorber completion. So every
   OC₁-failing start, hence every RF counterexample, in which some agent holds a private good has a frozen agent that
   values the junk set above its pick. Checked: the construction is EFX₀ on 6,650 random starts where the hypotheses
   hold, and fails at k = 5 exactly where the proof uses k ≤ 4. The hypotheses hold at none of the 1,398,810 stored
   failing starts, although 138,979 of them have an agent holding a private good.
4. *Census of the n ≤ 5 failures* (§4, EVIDENCE: n = 4 complete, n = 5 partial).
   - Every receiver has four goods (P4 or Q4).
   - No receiver holds its top.
   - No failing start is in a core with a private-top agent.
   - The receiver-first classes (|U′|, |D_T′|) grow with n: at most (2, 2) at n = 4, up to (1, 3), (2, 2) and (3, 2) at
     n = 5. So the data give no constant bound.
5. *The list for the hunt* (§5).
6. *RF-PRIV* (§6): proved when no frozen agent values the junk above its pick (Lemma ABS). The general case is open.
   - In every stored n = 5 failure whose receiver picked a private good, lifting that good to the receiver's top makes
     the picks complete (35,299 of 35,299).
   - At n = 4 the conclusion holds outright.
7. *Transfer to RKMAX* (§7): Proposition RF-𝒦 and Lemma ABS transfer verbatim; Corollaries RF-TOP and RF-PRIV are
   RF-specific.

## 1. Which reductions a minimal RF counterexample admits

**Why the minimal-counterexample reductions do not transfer as such.** K4.MC1's reductions replace a configuration
by a smaller gadget instance H′ and extend an EFX₀ allocation of H′. They use only that H′ has *some* EFX₀ allocation,
which is the inductive statement (TARGET₄ on smaller instances). RF is a statement about every OC₁-failing start of H
and the reorders of its receiver. An extension of an allocation of H′ says nothing about which starts of H fail, nor
about the order its receiver-first picks come from. So a minimal counterexample to RF, minimal for RF, inherits
nothing from K4.MC2–K4.MC9. RF is also not hereditary: deleting agents changes the picks of every order.

**Proposition RF-𝒦 (proved).** Let 𝒦 be the set of strict type profiles of strict connected k = 4 cores H with:
- β ≥ 5 (K4.MC7), n ≤ 3(β − 1) (K4.MC4), n ≥ 6 (K4.R3–K4.R5p settle n ≤ 5), and at least two 4-good agents when
  n = 6 (K4.R6a settles exactly one);
- no PP4 agent (K4.MC2), no good of degree 2 shared by two P3 agents (K4.MC3);
- the pair profile of every px pair in K4.MC5's recorded set;
- no Q3–Q3, Q3–P4 or P4–P4 double edge, and no closed Q3–Q4 or P4–Q4 one; every other double edge's pair profile in
  K4.MC8's recorded sets;
- no claw (K4.MC9).

If RF holds on 𝒦 (for every start of these cores at these profiles), then TARGET₄ holds.

*Proof.* Suppose TARGET₄ fails, and let H be a minimal counterexample (fewest agents, then goods). By K4.MC0 it is a
strict connected k = 4 core, with strict types, and only the types matter. By K4.MC2–K4.MC9 and the β ≤ 4 results it
lies in 𝒦. By Lemma MAXSD (`k4/sdc.md` §31) some serial-dictatorship order of H has maximum-matching picks Y.
- If OC₁ holds at Y, H has an EFX₀ allocation: the completion.
- Otherwise RF gives a receiver-first order with maximum-matching picks at which OC₁ holds, which again gives one.

Either way this contradicts the choice of H. ∎

The proposition replaces "RF on every core" by "RF on 𝒦". It is the same implication as `EFX.OC1Max.target4_of_conjRF`
(row K4.SDC.RF.LEAN), with the class restricted by the certified reductions. A search for RF counterexamples that
matter for TARGET₄ may therefore run on the minimal-counterexample candidate lists:
- β = 5, n = 6…12: `results/k4_twins/mc_n*_b5_mc9.json.gz`, 320,348 cores in all;
- n = 6, every β from 5 to 9: `results/k4_rfmin/mc_n6_b*_mc9.json.gz`, written by `k4/twins_count.py 6 β --mc9`, with
  the counts below.

| n = 6, β | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|
| candidate cores (K4.MC2, MC3, MC5, MC8, MC9; a 4-good agent) | 20,553 | 94,469 | 192,417 | 212,897 | 138,259 |
| of which at least two 4-good agents (in 𝒦) | 18,044 | 89,626 | 188,986 | 211,900 | 138,142 |
| of those, m ≥ 10 | 18,044 | 70,924 | 114,954 | 86,018 | 25,372 |

The domains are those of `mincex_shapes.restricted_domains`, cut further by `twins_filter.restricted_domains`. For
m ≤ n + 3 the literature (Mahara) also covers TARGET₄; K4.MC does not use it.

## 2. Lemma RF-TOP

**Lemma RF-TOP (proved).** Let Y be the serial-dictatorship picks of an order σ (strict values), and let u be an agent
whose pick Y_u is its top good. Then σ′ = (u, σ − u) gives the same picks.

*Proof.* With u first, u takes its top good, Y_u. Take any other agent a, and suppose all agents before a in σ′ have
their σ-picks.
- If u comes before a in σ, a has the same free goods in both orders.
- If u comes after a in σ, a's free goods in σ′ are those of σ without Y_u. Y_a ≠ Y_u, and Y_a is a's favourite among
  the σ-free goods, so it is also its favourite among them without Y_u.
- If a had no pick in σ, it has none in σ′.

∎ This is the first sentence of the girth session's Lemma RF-PATH (`k4/girth.md` §7 on `claude/k4-girth`), there
for a receiver u; the receiver hypothesis is not needed for this part.

**Corollary RF-TOP.** If RF holds, no receiver of an OC₁-failing start holds its top good. (Otherwise σ′ is a receiver-first
order with the same maximum-matching picks, at which OC₁ fails.)

**Corollary RF-PRIV.** If RF holds, then OC₁ holds at every start of every core in which some agent's top good is private.
Such an agent always picks its top (nobody else takes it), and it is always a receiver (nobody else values it). So in
such a core every OC₁ failure is an RF counterexample.
- In 𝒦 these cores exist. A P3 or P4 agent may rank its private good first, except when K4.MC5 forces its ranking.
- The data: at n = 4 the certifier's export lists every OC₁^max failure (`two_move_starts_n4.json.gz`, sha256
  6159e38d…). None is at a profile with a private-top agent. With that export's completeness, **Corollary RF-PRIV's
  conclusion is certified at n = 4.** At n = 5, none of the 1,285,930 stored failing starts has a private-top agent either
  (`results/k4_rfmin/classes_n4.log`, `classes_n5.log`).

## 3. Lemma ABS: a private pick absorbs the junk

**Lemma ABS (proved).** Let Y be the serial-dictatorship picks of an order (strict additive values; every agent values at
most four goods). Suppose:
- some agent f holds a private good, i.e. no other agent values Y_f;
- no frozen agent i values the junk set above its pick: v_i(J) ≤ v_i(Y_i).

Then the picks have a one-absorber EFX₀ completion with absorber f.

*Construction.* Take the receivers r ≠ f in any order. If r values the junk still free above its pick, r takes its most
valuable free junk good. Then f takes all junk still free. Everybody else keeps its pick, and pickless agents keep
nothing.

*Proof.* Two facts about serial dictatorship:
- (SD1) An agent with a pick values every junk good below its pick: the good was free at its turn.
- (SD2) A pickless agent values no junk good: nothing it valued was free at its turn, and junk is never taken.

The only bundles with two or more goods are f's bundle X_f = {Y_f} ∪ F (F the junk f takes) and the bundles {Y_r, g_r}
of receivers that took a junk good g_r.

- *Threats from {Y_r, g_r}.* For any agent i ≠ r the threat is θ_i = max(v_i(Y_r), v_i(g_r)). r is a receiver, so
  v_i(Y_r) ≤ v_i(Y_i), which is 0 for a pickless agent. And v_i(g_r) < v_i(Y_i) by SD1, or = 0 by SD2. So θ_i ≤ v_i(Y_i)
  ≤ v_i(X_i). This includes i = f.
- *Threats from X_f.* Nobody but f values Y_f, so for i ≠ f the minimum over X_f is 0, and θ_i(X_f) = v_i(F).
  - Pickless i: v_i(F) = 0 by SD2.
  - Frozen i: v_i(F) ≤ v_i(J) ≤ v_i(Y_i) by hypothesis.
  - A receiver r ≠ f that took nothing: when its turn came, the free junk was worth at most v_r(Y_r) to it, and F is
    contained in that free junk.
  - A receiver r that took g_r: r values at most four goods, so it values at most three free junk goods at its turn, and
    at most two of them, h and h′, can end in F. By SD1, v_r(h) < v_r(Y_r), and v_r(h′) < v_r(g_r) since g_r was the
    most valuable. So v_r(F) < v_r(Y_r) + v_r(g_r) = v_r(X_r).
- *Singletons* never threaten.

Only f receives two or more junk goods. ∎ The bound "at most three junk goods" is where k ≤ 4 enters. At k = 5 a
receiver with four junk goods g > h > h′ > h″ can face h + h′ + h″ > Y_r + g, and the construction fails
(`results/k4_rfmin/absorb_k5_sensitivity.log`: 2 such starts in 1,054). Maximum matchings are not used.

**Corollary ABS.** At every start where OC₁ fails (in fact, wherever the picks have no one-absorber completion) and some
agent holds a private good, some frozen agent values the junk set above its pick. This holds in particular at every RF
counterexample with that property.

*Checks* (`k4/rfmin/absorb.py`):
- The construction is EFX₀ by the raw definition at all 6,650 random starts where the hypotheses hold: 3,860 with 2–4
  goods per agent, and 2,790 with 4 goods per agent, n = 3–6 (`results/k4_rfmin/absorb_random.log`).
- At k = 5 it fails twice, as predicted.
- On the stored failing starts (`results/k4_rfmin/absorb_data.log`), the hypotheses hold at none of the 1,398,810, and
  138,979 of them have an agent holding a private good.

## 4. Census of the known failures (EVIDENCE)

*Data.* All OC₁^max-failing starts known (raw OC₁ failures and their orders, from the certifier
compute/k4-oc1max-cert), as copied to other branches:
- `two_move_starts_n4.json.gz` (claude/k4-referee, `results/k4_base_phantom/data/`, sha256 6159e38d…): n = 4, complete,
  11 hypergraphs, 112,880 starts.
- `two_move_starts_n5_partial6.json.gz` (proof/k4-base-phantom, sha256 4141bd4c…): n = 5, partial, 6 hypergraphs,
  702,250 starts.
- `two_move_starts_n5_sel2.json.gz` (proof/k4-base-phantom, sha256 d1f6f082…): n = 5, partial, 3 hypergraphs, 583,680
  starts.

Scripts: `k4/rfmin/census.py` and `k4/rfmin/classes.py`. Logs: `results/k4_rfmin/census.log`, `classes_n4.log`,
`classes_n5.log`.

| | n = 4 (complete) | n = 5 partial6 | n = 5 sel2 |
|---|---|---|---|
| failing starts | 112,880 | 702,250 | 583,680 |
| receivers per start | 1 | 1 | 1 |
| receiver kind | Q4 110,080, P4 2,800 | Q4 611,070, P4 91,180 | Q4 468,480, P4 115,200 |
| receiver holds its top | 0 | 0 | 0 |
| receiver's pick private | 0 | 23,779 | 115,200 |
| hypergraphs in the K4.MC2/3/8/9 structural class | 8 of 11 (3 have a closed P4–Q4 double edge, among them instance 1 of `k4/sdc.md` §31) | 6 of 6 | 0 of 3 (all have a PP4 agent) |
| starts with a private-top agent | 0 | 0 | 0 |

Every start in these exports has exactly one receiver. The four known two-receiver starts (row K4.SDC.R2.N5, chunk
5_pure_s5o1) are not in them.

*Receiver-first classes.* Take every receiver u and every order with u first. At the maximum-matching picks Y′ it gives,
U′ is the set of unfrozen agents and D_T′ the frozen agents threatened by the whole junk set at their pick, as in
`k4/referee/rfres_ref.py`. The table counts pick vectors.

| (\|U′\|, \|D_T′\|) | n = 4 | n = 5 partial6 | n = 5 sel2 |
|---|---|---|---|
| (1, 0) | 40,000 | 166,889 | 46,800 |
| (1, 1) | 28,720 | 501,802 | 86,400 |
| (1, 2) | 47,040 | 189,376 | 39,600 |
| (1, 3) | – | 7,733 | – |
| (2, 0) | 77,640 | 1,256,409 | 72,000 |
| (2, 1) | 92,800 | 643,491 | 379,200 |
| (2, 2) | – | 79,428 | 192,000 |
| (3, 0) | – | 450,551 | 860,160 |
| (3, 1) | – | 171,921 | – |
| (3, 2) | – | 6,019 | – |

The largest classes grow from n = 4 to n = 5, in both coordinates. These data therefore give no constant bound on
(|U′|, |D_T′|), and a proof by cases over the classes would have to handle a growing family.

## 5. The list for the hunt session

For a search for counterexamples to RF at n ≥ 6:
1. *Where to search* (Proposition RF-𝒦, proved). On the minimal-counterexample candidate lists:
   - β = 5: `results/k4_twins/mc_n*_b5_mc9.json.gz`, 320,348 cores;
   - n = 6, β = 5–9: `results/k4_rfmin/mc_n6_b*_mc9.json.gz`;
   - other (n, β): `twins_count.py N β --mc9`;
   - with the domain cuts of `twins_filter.restricted_domains`.

   RF failures outside this class are irrelevant to TARGET₄.
2. *What to check first* (Corollaries RF-TOP and RF-PRIV, proved). At every OC₁-failing start found:
   - if a receiver holds its top good, RF fails there, with no reordering needed;
   - in a core with a private-top agent, every OC₁^max failure is an RF counterexample.
3. *What a failing start must have* (Corollary ABS, proved). If some agent holds a private good, some frozen agent values
   the junk set above its pick. So in a CEGAR the clause "some agent picks a private good and every frozen agent's junk
   is worth at most its pick" excludes the start.
4. *What the n ≤ 5 failures look like* (EVIDENCE).
   - The receiver is a 4-good agent.
   - The receiver does not hold its top.
   - Receiver-first classes reach (3, 2) at n = 5.

## 6. RF-PRIV: status of a direct proof

RF-PRIV's conclusion is: OC₁ holds at every maximum-matching start of every core in which some agent f's top good p is
private. It is a sub-case of RF that a proof of RF must contain (Corollary RF-PRIV).

**Proved part.** Lemma ABS gives it whenever no frozen agent values the junk set above its pick. f holds p, which is
private, so f can be the absorber.

**Not proved.** The case where some frozen agent d has v_d(J) > v_d(Y_d) is open. The natural route is one chain: d takes
its junk (a pair if possible, H₀ ⊆ J ∩ R_d with v_d(H₀) > v_d(Y_d)), a wanter w of Y_d takes Y_d, and w's old pick is
released, after which f absorbs. It runs into two gaps:
- the released pick Y_w can threaten agents that wanted it, unless w is unfrozen;
- a three-good H₀ can threaten other agents.

Closing it needs the exact one-absorber completability count (the Hall session's Lemma 2*) at the post-move state.

**Evidence.**
- At n = 4 the conclusion holds outright: no OC₁^max failure at a private-top profile in the complete export (§2).
- *Lift test* (`k4/rfmin/privtop_lift.py`). Take every stored n = 5 failing start whose receiver u picked a private but
  non-top good. Raise that good above u's other goods, keeping the type strict and balanced; the picks are unchanged.
  Then OC₁ holds, and always already **at the picks**: 23,779 of 23,779 (partial6, `results/k4_rfmin/privtop_lift_n5p6.log`)
  and 11,520 of 11,520 (sel2, every 10th, `privtop_lift_n5s2.log`).
  - Probable mechanism (an inference, not checked on the completions): before the lift, u wants its top t, so t's holder
    x₁ is frozen and cannot take junk. After the lift u wants nothing, and the completion uses the room this frees.
- *Random private-top cores*, n = 4–6, 400 instances (`k4/rfmin/privtop_random.py`, `results/k4_rfmin/privtop_random.log`):
  1,297 maximum-matching pick vectors; 1,294 complete at the picks, 3 after one move, none fail. Random cores rarely fail
  OC₁ at all, so this is weak.

**The lift test, read on the completions** (`k4/rfmin/privtop_mech.py`; samples of the partial6 lifted starts).
- *The first guess is wrong.* The guess was that u's wish freezes the holder x₁ of u's old top t, and that the lift frees
  x₁.
  - At all 1,191 sampled starts (every 20th), t is also wanted by another agent, so x₁ stays frozen after the lift.
  - At 949 of them, no lifted completion gives x₁ any junk; a completion in which x₁ takes none always exists.
- *What the lift frees.* Only u's valuation changes, so a lifted completion fails in the original values only through u's
  own safety. At all 240 sampled starts (every 100th), some lifted completion is blocked in the original values by
  exactly one kind of bundle: a single-junk bundle {g, j}, where g is a good u ranks above its private pick (u's top in 45
  of them, another such good otherwise).
  - So u's wishes freeze, for junk, the holders of every good u ranks above its private pick.
  - The lift frees those holders as parking slots.
- *The owner is the private-top agent itself.* At all 478 sampled lifted starts (every 50th), a lifted completion with
  absorber u exists, so the lift completes the picks with the private-top agent as owner.

**Lemma 2 at the picks, with owner f.** Take Hall's Lemma 2 (`k4/oc1_hall.md` §4; slot count for S\* completions with
owner o) at the picks, with owner o = f, the private-top agent. Its hypotheses hold automatically:
- (G1): every non-owner bundle is a singleton, and singletons never threaten;
- (G2): junk is never wanted (SD1);
- (G5′) and (H3): B_o = {p} is private.

Its condition (H1) for a frozen q is exactly v_q(J ∖ H) ≤ v_q(Y_q), because p is worthless to q. So at the picks, "a
completion with owner f" is exactly the count: some H ⊆ J meets (H1) and |H| + θ(H) − ν(H) ≤ |N₁|. Lemma ABS is the case
H = ∅ with no threatened receiver unserved.

**After one move** (`k4/rfmin/privtop_gap.py`, `results/k4_rfmin/privtop_gap.log`). Random strict connected cores with a
private-top agent, n = 4–6, 20,000 instances: 62,531 maximum-matching starts, of which 103 do not complete at the picks.
- At all 103, some one-move state has a completion **with owner f**. This is RF-PRIV's conclusion on them, with the
  owner fixed.
- At 87 of them a two-agent chain does it: d ∈ D^full takes a pair H₀ of its junk goods, an *unfrozen* wanter w of Y_d
  takes Y_d, and Y_w is released.
  - This is the case where Lemma 2's hypotheses also hold after the move:
    - (G2), because Y_w is unwanted when w is unfrozen;
    - (G1), because a two-good junk bundle threatens nobody.
  - A wanter of Y_d always holds a pick at a maximum-matching start: by Lemma MAX, a pickless wanter would make d value
    no junk.
- The other 16 need one of:
  - a frozen wanter (27 repairs);
  - a three-good H₀ (18);
  - a longer chain;
  - f adding junk to its own base (31).
- Ten have no two-agent repair at all.

So a uniform proof by Lemma 2 at the post-move state needs its hypotheses (G1) and (G2) relaxed, or a second case.

**Conjecture RF-PRIV⁺** (EVIDENCE: the 103 starts above, and the 35,299 lifted n = 5 starts). In a core where some agent f's
top good is private, at every maximum-matching start the picks, or the bases after one move, have a one-absorber
completion with owner f.

**Where private-top agents survive in 𝒦.** K4.MC5 forces y > p > g for a P3 agent next to an E3 agent (Q3 or P4) through a
degree-2 good, so such an agent's top is not private. In px-Q4's recorded set, 576 of the 1,080 open profiles have the P3
agent ranking its private good first (`results/k4_min_cex_px_uncovered.json`). So in 𝒦, RF-PRIV concerns:
- P3 agents next to a Q4 agent through a degree-2 good;
- P3 agents whose two shared goods both have degree ≥ 3;
- P4 agents outside px pairs.

## 7. Transfer to Conjecture RKMAX

Conjecture RKMAX (`k4/sdc.md` §31 end on `claude/kind-lamport-y8fdme`, row K4.SDC.RKMAX) says that OC₁ holds at every
maximum-matching start whose rank signature σ is lexicographically maximal.
- **Proposition RF-𝒦 transfers verbatim.** RKMAX implies OC₁^∃max, so RKMAX on 𝒦 implies TARGET₄ by the same proof (§1).
  The candidate lists serve an RKMAX search as they serve an RF search.
- **Lemma ABS transfers verbatim.** It is about any serial-dictatorship start, so in particular σ-maximal ones. At a
  σ-maximal start where some agent holds a private good and no frozen agent values the junk above its pick, OC₁ holds.
  - D_T (θ(J) above the pick) ⊆ D^full (v(J) above the pick). So among the starts with |D_T| = 0, ABS closes those at which
    D^full is empty as well and some agent holds a private good.
  - It does not reach Hall's remaining classes (1, 1) and (2, 0) directly.
- **Lemma RF-TOP transfers; its corollaries do not.** The lemma is about serial dictatorship itself. Its corollaries
  RF-TOP and RF-PRIV come from RF's universal clause, "every receiver-first maximum-matching order satisfies OC₁".
  RKMAX asks for OC₁ only at σ-maximal starts, so it implies neither. In a core with a private-top agent, RKMAX needs OC₁
  at the σ-maximal starts only, while RF needs it at every maximum-matching start.
  - Conversely, a proof of RF-PRIV's conclusion would prove RKMAX on those cores.
- **What RF-TOP says about σ.** An agent holding its top good has rank 1, and moving it to the front changes no pick, so
  σ is unchanged. The σ-raising rotations of `k4/sdc.md` §31 (RF and σ) are therefore rotations of receivers that do not
  hold their top, which is exactly where RF-PATH has a nonempty ejection path.

## Reproduce

```
cd k4/rfmin
python3 absorb.py random 3000 1; python3 absorb.py random 4000 2 --kmin=4 --kmax=4     # Lemma ABS, ~5 min
python3 absorb.py random 3000 3 --kmin=4 --kmax=5          # sensitivity: fails at k = 5 (expected), ~3 min
python3 absorb.py data N4 N5P6 N5S2                         # the stored failing starts (paths in §4), ~30 s
python3 census.py N4 N5P6 N5S2; python3 classes.py N4; python3 classes.py N5P6 N5S2     # §4, ~30 min for n = 5
python3 privtop_lift.py N5P6 1; python3 privtop_lift.py N5S2 10                     # §6 lift test, ~10 min
python3 privtop_random.py 400 7 4 6                                                 # §6 random private-top cores, ~5 min
python3 privtop_mech.py N5P6 20                                                     # §6 lift mechanism (x1), ~10 min
python3 privtop_gap.py 20000 13 4 6                                                 # §6 the starts needing a move, ~20 min
cd ..; for b in 5 6 7 8 9; do python3 twins_count.py 6 $b --mc9 --write=../results/k4_rfmin/mc_n6_b${b}_mc9.json.gz; done
```
