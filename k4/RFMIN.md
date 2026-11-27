# k = 4: what a minimal counterexample to Conjecture RF can look like

Workstream `proof/k4-rf-min` (asked for by the coordinator, 2026-11-27 05:25). Conjecture RF (receiver first) is row
K4.SDC.RF, `k4/sdc.md` §31 end. Here, *start* means the picks Y of a serial-dictatorship order whose picks form a maximum
matching, *receiver* an agent with a pick that no other agent prefers to its own (a pickless agent "prefers" any good it
values), *frozen* an agent with a pick that some other agent prefers to its own, *junk* J the goods nobody picked, and
*OC₁* the conjecture's completion statement (a one-absorber completion of the picks, or one after one improving move).

Refereed (§1–§4, at `d32e566d`): `k4/referee/rfmin.md` on `claude/k4-referee`. The material of §6 from Lemma M^c on
(ABS′, CH, RF-PRIV′) was added after that review.

**Results.**
1. *What a minimal RF counterexample can be assumed to satisfy* (§1, Proposition RF-𝒦, proved). For TARGET₄, RF is
   needed only on the class 𝒦 of possible minimal counterexamples to TARGET₄: strict connected k = 4 cores with β ≥ 5,
   6 ≤ n ≤ 3(β − 1), no agent with two private goods, no good of degree 2 shared by two P3 agents, no double edge without
   a Q4 agent, no claw, and profiles inside K4.MC5's and K4.MC8's recorded sets. RF failures outside 𝒦 refute RF as
   stated but not the TARGET₄ route. RF is not closed under the reductions themselves (§1), so they enter this way,
   not as reductions of RF. Refereed CORRECT WITH FIXES: the proof needs a receiver at the failing start, which the
   referee's Lemma REC-∃ supplies (§1).
2. *Lemma RF-TOP and its corollary* (§2, proved). Moving an agent that holds its top good to the front of an order
   changes no pick. Hence RF forbids a receiver holding its top at any start where OC₁ fails. In particular, **RF implies
   OC₁ at every start of every core with an agent whose top good is private.** Every OC₁ failure in such a core is
   therefore an RF counterexample that needs no reordering to detect: a cheap target for the hunt. Refereed CORRECT.
3. *Lemma ABS* (§3, proved; uses k ≤ 4). At any serial-dictatorship start, if some agent holds a private good and no
   frozen agent values the whole junk set above its pick, then the picks have a one-absorber completion. So every
   OC₁-failing start, hence every RF counterexample, in which some agent holds a private good has a frozen agent that
   values the junk set above its pick. Checked: the construction is EFX₀ on 6,650 random starts where the hypotheses
   hold, and fails at k = 5 exactly where the proof uses k ≤ 4. The hypotheses hold at none of the 1,398,810 stored
   failing starts, although 138,979 of them have an agent holding a private good. Refereed CORRECT.
4. *Census of the n ≤ 5 failures* (§4, EVIDENCE: n = 4 complete, n = 5 partial; every count confirmed by the referee).
   - Every receiver has four goods (P4 or Q4).
   - No receiver holds its top.
   - No failing start is in a core with a private-top agent.
   - The receiver-first classes (|U′|, |D_T′|) grow with n: at most (2, 2) at n = 4, up to (1, 3), (2, 2) and (3, 2) at
     n = 5. So the data give no constant bound.
5. *The list for the hunt* (§5).
6. *RF-PRIV* (§6): proved when no frozen agent values the junk above its pick (Lemma ABS). The general case is open.
   - *Lemma ABS′* (proved): Lemma ABS at any state satisfying (G1) and (G2), with "frozen" read as "not a receiver".
     *Lemma CH* (proved): after a canonical chain from a dangerous agent with a junk pair and an unfrozen head, ABS′ holds
     unless one of two explicit conditions, (V1) and (V2), fails.
   - *Conjecture RF-PRIV′* (EVIDENCE: all 1,824 gap starts in 440,000 random private-top cores, n = 4–7): the picks
     complete, or after some official move ABS′ holds for the private-top agent. This is a covering statement with no
     matching. A canonical chain is enough at 1,609 of the 1,759 gap starts at n = 4–6. The other 150 need a move in which an
     agent takes a pick together with junk.
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
- Otherwise Y has a receiver, by the referee's Lemma REC-∃ (below). For that receiver u, RF gives a u-first order
  with maximum-matching picks at which OC₁ holds, which again gives an EFX₀ allocation.

Either way this contradicts the choice of H. ∎

*The fix (referee, `k4/referee/rfmin.md` §1 on `claude/k4-referee`).* RF as amended (`k4/sdc.md` §31, row K4.SDC.RF)
quantifies over the receivers of a failing start and does not assert that one exists. The first version of this proof
took the receiver for granted. The referee's **Lemma REC-∃** supplies it. If a maximum-matching start Y has no
receiver, then:
- some agent is pickless;
- no agent values a junk good;
- giving all junk to one pickless agent is an EFX₀ one-absorber completion.

So every OC₁-failing maximum-matching start has a receiver. The referee's proof:
1. If no agent were pickless, the last agent of the order would be a receiver.
2. Without receivers, every pick has a wanter. Wanting goes forward in the order, so wanter chains end at pickless
   agents.
3. The alternating path from such a pickless agent back to any pick holder shows, by maximality, that no pick holder
   values junk (Lemma MAX).
4. Pickless agents value no junk (SD2).

I have read this proof and it is correct. Its check (`norecv_ref.py`): 421,258 starts without a receiver among 1,457,079
maximum-matching starts of random instances, n = 3–6, all with no valued junk, none failing OC₁. The referee also notes
that the Lean `ConjRFWith` asserts a *unique* receiver, which the n = 5 two-receiver starts of K4.SDC.R2.N5 contradict.
This proposition uses existence only.

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

The exact count at the post-move state exists (Lemma M^c, below). The open part is existence: a move after which the
count is met. The data say a matching-free special case of the count, Lemma ABS′, already suffices (below).

**Evidence.**
- At n = 4 the conclusion holds outright: no OC₁^max failure at a private-top profile in the complete export (§2).
- *Lift test* (`k4/rfmin/privtop_lift.py`). Take every stored n = 5 failing start whose receiver u picked a private but
  non-top good. Raise that good above u's other goods, keeping the type strict and balanced; the picks are unchanged.
  Then OC₁ holds, and always already **at the picks**: 23,779 of 23,779 (partial6, `results/k4_rfmin/privtop_lift_n5p6.log`)
  and 11,520 of 11,520 (sel2, every 10th, `privtop_lift_n5s2.log`).
  - The mechanism first guessed (u's wish freezes the holder x₁ of u's top t, and the lift frees x₁) is wrong; the
    completions are read below.
- *Random private-top cores*, n = 4–6, 400 instances (`k4/rfmin/privtop_random.py`, `results/k4_rfmin/privtop_random.log`):
  1,297 maximum-matching pick vectors; 1,294 complete at the picks, 3 after one move, none fail. Random cores rarely fail
  OC₁ at all, so this is weak.

**The lift test, read on the completions** (`k4/rfmin/privtop_mech.py`, `results/k4_rfmin/privtop_mech.log`; samples of the
partial6 lifted starts).
- *The first guess is wrong.* The guess was that u's wish freezes the holder x₁ of u's old top t, and that the lift frees
  x₁.
  - At all 1,191 sampled starts (every 20th), t is also wanted by another agent, so x₁ stays frozen after the lift.
  - At 949 of them, no lifted completion gives x₁ any junk; a completion in which x₁ takes none always exists.
- *What the lift frees.* Only u's valuation changes, so a lifted completion fails in the original values only through u's
  own safety. At all 240 sampled starts (every 100th), some lifted completion is blocked in the original values only by
  a single-junk bundle {g, j}, where g is a good u ranks above its private pick other than its top. At 45 of them, other
  lifted completions are blocked by u's top in a single-junk bundle, or by the absorber's bundle.
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

**The exact count after the move: Lemma M^c.** (G1) is already relaxed elsewhere, and (G2) holds after the right chains.
- Lemma M^c (`k4/oc1max_multi.md` §9 on `proof/k4-oc1max-multi-2`; the matching session re-implemented it
  independently) is Lemma 2\* with (G1) dropped and frozen slots added. It assumes only (G2), and is the exact test for
  S^c completions with a given owner.
- Lemma RF-B′'s proof of (G2) (`k4/oc1_hall.md` §24.10 on `claude/k4-oc1-hall`) carries over verbatim to a chain "d takes
  H₀ ⊆ J, x₁ takes Y_d, …, x_t takes Y_{x_{t−1}}" whose head's pick Y_{x_t} nobody wants. The free goods are then junk,
  below every pick, and Y_{x_t}, which nobody wants.

So after such a chain, M^c's (C1)–(C3) with owner f is the exact test. With owner f, (C2) is automatic when |H₀| = 2: f
wants nothing, and a two-good bundle minus a good is a single junk good, below p. "X threatens i" becomes "i values the
junk f keeps above its own bundle", because no other agent values p. On the data the matching in (C3) is never needed:
its greedy special case, Lemma ABS′, suffices after some move at every gap start.

**Lemma ABS′ (proved; Lemma ABS at any state).** Let B be a state with free goods J, write b_i = v_i(B_i), and fix an
agent f. Call r ≠ f a *receiver* at B if |B_r| ≤ 1 and no other agent wants the good of B_r (an empty bundle counts).
Suppose:
- (A0) B_f = {p}, and no other agent values p;
- (A1) = (G2): v_i(g) ≤ b_i for every free good g and every agent i;
- (A2) = (G1): no bundle B_q of two or more goods (q ≠ f) threatens anybody: v_i(B_q ∖ h) ≤ b_i for all i ≠ q, h ∈ B_q;
- (A3) every agent i ≠ f that is not a receiver has v_i(J) ≤ b_i.

Then the following allocation is EFX₀. The receivers in turn take their most valuable free good if they value the free
goods above b_r; f takes the rest; nobody else changes.

*Proof.* Values only rise. The bundles of two or more goods are three kinds.
- *X_f = {p} ∪ F.* For i ≠ f, v_i(p) = 0, so the threat is v_i(F).
  - A non-receiver: v_i(F) ≤ v_i(J) ≤ b_i, by (A3).
  - A receiver that took nothing: F lies inside the goods free at its turn, which it values at most b_r.
  - A receiver with B_r = ∅ values no free good, by (A1).
  - A receiver with B_r = {y_r} that took g_r: it values at most three free goods at its turn (k ≤ 4). At most two of
    them, h and h′, can end in F, with v_r(h) ≤ b_r by (A1) and v_r(h′) ≤ v_r(g_r). So v_r(F) ≤ b_r + v_r(g_r).
- *{y_r, g_r}* for a receiver that took g_r: for i ≠ r the threat is at most max(v_i(y_r), v_i(g_r)) ≤ b_i. y_r is
  unwanted, and g_r was free, so (A1) applies. If B_r = ∅, the bundle {g_r} is a singleton.
- *An unchanged B_q*, by (A2).

These cases include threats to f. Singletons never threaten. ∎ Lemma ABS is the case B = Y. There SD1 and SD2 give (A1),
(A2) is empty, and the non-receivers are the frozen agents.

**Lemma CH (canonical chains; proved).** Let Y be a start (a maximum matching), p_i = v_i(Y_i), d a frozen agent that
values some junk good, and H₀ ⊆ J ∩ R_d with v_d(H₀) > p_d.
1. There is a chain d = x₀ ← x₁ ← ⋯ ← x_t (t ≥ 1) in which:
   - each x_i (i ≥ 1) holds a pick and wants Y_{x_{i−1}};
   - nobody wants Y_{x_t}.
2. Let B′ be the state after the official move "d takes H₀, each x_i takes Y_{x_{i−1}}", and J′ = (J ∖ H₀) ∪ {Y_{x_t}}.
   If f's top good is private, then:
   - (A0) and (A1) hold at B′ for f;
   - (A2) holds if |H₀| = 2;
   - d meets (A3).
3. So with |H₀| = 2, ABS′ gives a one-absorber completion of B′ with absorber f, unless one of the following holds:
   - **(V1)** an agent q outside the chain, whose pick is wanted at B′, has v_q(J′) > p_q. If q ∉ D^full, this needs
     q to value Y_{x_t};
   - **(V2)** a chain member x_i, whose new good Y_{x_{i−1}} another agent wants at B′, has
     v_{x_i}(J′) > v_{x_i}(Y_{x_{i−1}}).

*Proof.*
1. If i wants Y_j, then Y_j was gone at i's turn, so j precedes i in the order. Wanting is therefore acyclic, and
   following wanters from d ends at an agent whose pick nobody wants. If some x_i were pickless, the edges d–h
   (h ∈ J ∩ R_d), x₁–Y_d, …, x_i–Y_{x_{i−1}}, with those of every other pick, would form a larger matching.
2. f is not in the chain: it wants nothing, since its pick is its top, and it is not frozen.
   - (A0) follows.
   - (A1) is RF-B′'s argument. Every value at B′ is at least the pick value. Junk was free at every turn (SD1, SD2).
     Nobody wants Y_{x_t} at Y, and x_t's own value rose.
   - (A2): each H₀ ∖ h is a single junk good, below every pick.
   - d values Y_d, the goods of H₀ and at most 4 − 1 − |H₀| ≤ 1 other good c. Such a c is junk, below p_d, or it is
     Y_{x_t}, which d does not want. So v_d(J′) ≤ p_d < v_d(H₀). Note |H₀| ≥ 2 always, since a single junk good is
     below p_d.
3. An agent q outside the chain keeps Y_q. A wanter at B′ is a wanter at Y, because values only rose, so q is frozen at
   Y. If q ∉ D^full, then v_q(J) ≤ p_q, and only Y_{x_t} can push v_q(J′) above p_q. ∎

**Data** (`k4/rfmin/privtop_absp.py`). At every gap start, every one-move state is tested for ABS′ with the same f.
Every ABS′ construction is checked by the raw EFX₀ definition, at the picks and after the moves.

| sample (random private-top cores) | max starts | ABS′ at the picks | gap starts | ABS′ after some move | constructions checked |
|---|---|---|---|---|---|
| 20,000, n = 4–6, seed 13 | 62,531 | 48,144 | 103 | **103** | 49,548 |
| 400,000, n = 4–6, seed 14 | 1,243,213 | 958,791 | 1,656 | **1,656** | 978,186 |
| 20,000, n = 7, seed 15 | 127,815 | 92,174 | 65 | **65** | 93,371 |

**Canonical chains** (`k4/rfmin/privtop_chains.py`; `results/k4_rfmin/privtop_chains_s13.log`, `privtop_chains_s14.log`).
Lemma CH's claims are asserted on every chain tried: (A0)–(A2), d's (A3), a chain with an unfrozen head, and the
released pick in every (V1) with q ∉ D^full. Gap starts, by |D^full|, both samples together (n = 4–6):

| gap starts | \|D^full\| = 1 | 2 | 3 | 4 | all |
|---|---|---|---|---|---|
| starts | 404 | 1,131 | 218 | 6 | 1,759 |
| some canonical chain leaves ABS′ | 397 | 1,012 | 195 | 5 | 1,609 |
| every pair chain with an unfrozen head leaves ABS′ | 353 | 277 | 17 | 0 | 647 |
| no canonical chain works, but a move in which an agent takes a pick together with junk does | 7 | 119 | 23 | 1 | 150 |

- Canonical chains suffice at 91% of the gap starts, and at 98% of those with one dangerous agent. Every other gap
  start is repaired by a move in which some agent takes a pick together with junk, so that one chain reduces several
  agents' junk at once.
- No "every chain works" statement holds, even with one dangerous agent. At seed 13 all 24 such gap starts have it.
  At seed 14, 51 of 380 have a failing pair chain, through (V1) (69 violations, the released pick) or (V2) (5).
- With two or more dangerous agents, the violations after pair chains are mostly another dangerous agent: 1,972 of
  2,109 at both samples' gap starts.

**What the repairing moves do to the dangerous agents** (`k4/rfmin/privtop_fates.py`; `results/k4_rfmin/privtop_fates_s13.log`,
`privtop_fates_s14.log`). Every official move after which ABS′ holds is classified by the fate of each d ∈ D^full:
- *junk*: d's new bundle is junk only, so d starts the chain;
- *pick+*: d takes a pick together with junk;
- *better*: d takes a single better pick;
- *freed*: d keeps its pick and is a receiver afterwards, because every wanter of Y_d got something it prefers;
- *kept*: d keeps its pick and stays frozen, and the move took enough of its junk.

For each gap start, the table gives the least fate set that some ABS′ move stays inside (both samples, n = 4–6):

| least fate set | \|D^full\| = 1 | 2 | 3 | 4 |
|---|---|---|---|---|
| {junk, freed} | **404** | 855 | 97 | 0 |
| … ∪ {pick+} | 0 | 250 | 85 | 3 |
| … ∪ {better} | 0 | 1 | 12 | 1 |
| … ∪ {kept} | 0 | 25 | 24 | 2 |

- With one dangerous agent, some repair always has d take only junk (at 399 of the 404 starts) or frees d (at the
  other 5). This is the shape of a proof by cases for |D^full| = 1:

  **Conjecture RF-PRIV′₁** (EVIDENCE: 404 of 404). If D^full = {d}, some official move leaves ABS′ for f, and either d
  takes only junk in it, or d is a receiver after it.
- With several dangerous agents, 51 of the 1,355 starts need a move that leaves some dangerous agent frozen on its pick.
  There, other agents take the junk that agent values.

**Conjecture RF-PRIV′** (EVIDENCE: the 1,824 gap starts above, n = 4–7). Let f's top good be private. At every start,
either the picks have a one-absorber completion, or some official move leads to a state where ABS′ holds for f.

It implies RF-PRIV⁺, hence RF-PRIV's conclusion. Unlike RF-PRIV⁺, it is a covering statement with no matching: after
the move, every non-receiver values the free goods at most its bundle.

**Conjecture RF-PRIV⁺** (EVIDENCE: the 1,824 gap starts above, through RF-PRIV′, and the 35,299 lifted n = 5 starts). In a core where some agent f's
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
python3 privtop_mech.py N5P6 20 x1; python3 privtop_mech.py N5P6 100 threats; python3 privtop_mech.py N5P6 50 owner
                                                                                    # §6 lift mechanism, ~15 min
python3 privtop_gap.py 20000 13 4 6                                                 # §6 the starts needing a move, ~20 min
python3 privtop_absp.py 20000 13 4 6; python3 privtop_absp.py 400000 14 4 6         # §6 Lemma ABS′ after one move, ~5 min
python3 privtop_absp.py 20000 15 7 7                                                # §6 the same at n = 7, ~3 min
python3 privtop_chains.py 20000 13 4 6; python3 privtop_chains.py 400000 14 4 6     # §6 Lemma CH, canonical chains, ~5 min
python3 privtop_fates.py 20000 13 4 6; python3 privtop_fates.py 400000 14 4 6       # §6 fates of the dangerous agents, ~5 min
cd ..; for b in 5 6 7 8 9; do python3 twins_count.py 6 $b --mc9 --write=../results/k4_rfmin/mc_n6_b${b}_mc9.json.gz; done
```
