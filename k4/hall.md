# Owner validity as a covering problem, and C₄ᵐⁱⁿ without frozen agents

Workstream `proof/k4-hall`, ledger rows K4.HALL.* (CONJECTURE / EVIDENCE only), ledger open item 18. This is a second,
independent attack on conjecture C₄ᵐⁱⁿ of `k4/c4x.md` §5 (PR #36, branch `proof/k4-c4x`). The other attack (branch
`proof/k4-c4min`) uses the walk/cycle technique of Theorem K3 and was not read for this file. Notation as in
`k4/lb4.md` §1 and `k4/c4x.md` §1.

**Status.** Nothing here changes K4.D or K4.T. What is here:
- **§1 The covering form** (Lemma H1, proved): an owner o is a removal-only owner of P iff the threat hypergraph on
  B_o ∪ J has an independent set X ⊇ B_o with |X| ≥ ω + 2 − u_o(X). Equivalently, a set of |J| − |X| junk goods,
  at most the number of slots of the others, hits every minimal threatening set. So the deficit is ω + 2 minus the
  largest safe owner bundle.
- **§2 Exposure at a Pareto-maximum** (Lemma H3, proved, any P ∈ 𝒫 that is Pareto-maximal):
  - a *free* agent is exposed with respect to at most one owner, in one of three shapes (e1, e2, e3);
  - only the shape e2 can be repaired by removing a good, and then exactly one "label" good has to go.
- **§3 Theorem H0** (no frozen agent; written proof, not reviewed). Let P ∈ 𝒫 be Pareto-maximal, with no frozen agent
  and ω ≥ 1, and let T be the number of agents holding one good.
  - (a) If T ≥ 2, P is removal-only completable. The proof is a counting argument: the exposure sets of the owners
    are disjoint.
  - (b) If P is not removal-only completable, then T ≤ 1 and the exposure relation is a permutation of the agents.
    Rotating along a cycle of it is a Pareto improvement unless two agents on the cycle need the same junk label.
  - **The gap** is exactly this *label collision*. It occurs: a pure core with n = 6, m = 15 has a Pareto-maximal
    pre-allocation without frozen agents that is not completable at all (confirmed by two implementations,
    `attempts/k4-hall-pareto-no-frozen.md`). So "every Pareto-maximum is completable" fails even without frozen
    agents, while the some-form and the Σℓ-form hold there.
- **Consequence.** C₄ᵐⁱⁿ holds for every strict profile on which *some* valid pre-allocation has no frozen agent and
  some Pareto-maximal one of them has T ≥ 2. The full no-frozen case needs the collision closed (§3.4).
- **§4 Evidence and cross-checks**; §5 what changes with frozen agents.

## 1. The covering form of owner validity

Fix a strict profile of an instance in which every agent has three or four relevant goods and is strictly balanced
(every k = 4 core is one), and let 𝒫 be as in `k4/c4x.md` §1. The value-based needs of a base B are
N(B) = {g ∉ B : v(g) > v(B)}. A base is *need-free* if N(B) = ∅. For P ∈ 𝒫, F is the set of frozen agents,
S the number of slots, ω = |J| − S, and W_o = B_o ∪ J for a free agent o. A set X *threatens* x holding B_x if
max_{h ∈ X} v_x(X ∖ h) > v_x(B_x). This is monotone in X.

**Lemma H1 (covering form).** Let P ∈ 𝒫 with ω ≥ 1, o free, and K ⊆ J, X = B_o ∪ K. Let u_o(X) be the number of
agents that are frozen in P but not once o's needs are taken from X. Then some removal-only completion of P has owner
o and owner bundle X iff
- X threatens no agent x ≠ o holding B_x, and
- |X| ≥ ω + 2 − u_o(X).

Hence def(P) = ω + 2 − max (|X| + u_o(X)) over the free o and the safe X. In the complement: the removed junk
C = J ∖ K must hit every minimal threatening subset of W_o (every edge of the *threat hypergraph* H_o), with
|C| ≤ S − cap(o) + u_o(X).

*Proof.* N_o^X ⊆ N(B_o), since v_o(X) ≥ v_o(B_o). So taking o's needs from X only unfreezes agents. Each unfrozen agent
holds one good and gains one slot, and nobody else changes status. The slots of the agents other than o are therefore
S − cap(o) + u_o(X). The completion puts J ∖ K into them, which is possible iff |J| − |K| ≤ S − cap(o) + u_o(X). With
|J| = S + ω and |B_o| + cap(o) = 2 (o is free, |B_o| ≤ 2), this is |X| ≥ ω + 2 − u_o(X). Removal-only means exactly
that X threatens nobody holding its base (`k4/c4x.md` §1). ∎

Every edge of H_o lies in R_x ∖ B_x for one agent x, plus at most one good outside R_x. Each good of R_x ∩ W_o is worth
at most v_x(B_x): it is not in B_x, and not in NA, since J misses NA by (V1) and B_o does by (V2) or because o is free.
So an edge needs two goods of R_x. An agent whose base is empty is never threatened, since N_x = R_x ⊆ NA. The
brute-force check `bad_char` of `k4/hall.c` compares the transversal form with the exact deficit (0 disagreements,
§4).

## 2. Exposure at a Pareto-maximum

P ∈ 𝒫 is *Pareto-maximal* if no P′ ∈ 𝒫 has v_i(B′_i) ≥ v_i(B_i) for all i with one inequality strict. A
Pareto-improvement P′ of P has NA′ ⊆ NA, since each agent's needs shrink when its base value does not drop. So it has at
most as many frozen agents. Hence the maxima of (−|F|, Pareto) are the Pareto-maxima with the fewest frozen agents.

**Lemma H2 (any k).** Let P ∈ 𝒫 be Pareto-maximal.
- **(U)** A free agent with at most one base good values no junk good.
- **(U₂)** A free agent x with a two-good base has no pair B′ ⊆ B_x ∪ (R_x ∩ J) with v_x(B′) > v_x(B_x).

*Proof.* (U) is Lemma U of `k4/c4x.md` §3. For (U₂), let x take B′ instead of B_x. Its needs shrink: a good of B_x ∖ B′
is worth less than v(B_x) < v(B′). The released goods of B_x are not in NA by (V2), and the goods of B′ are in B_x or
in J, so not in NA. The result is in 𝒫 and dominates P. ∎

x is *exposed with respect to* a free owner o ≠ x if W_o threatens x holding B_x.

**Lemma H3 (free exposed agents).** Let P ∈ 𝒫 be Pareto-maximal, o free, and x ≠ o a *free* agent exposed with respect
to o. Then x is exposed with respect to no other free agent, and exactly one of the following holds:
- **(e1)** |B_x| = 1, R_x ∩ J = ∅ and B_o is a pair ⊆ R_x ∖ B_x;
- **(e2)** x has four goods, B_x = {b_x, c_x}, a_x ∈ B_o, d_x ∈ J, and v(a_x) + v(d_x) > v(b_x) + v(c_x);
- **(e3)** x has four goods, |B_x| = 2, R_x ∩ J = ∅ and R_x ∖ B_x = B_o.

With |X| ≥ 3 for every owner bundle X, a removal-only completion with owner o protects an e1 or e3 agent never
(*unhittable*), and an e2 agent iff it removes the *label* d_x.

*Proof.* A threat needs two goods of R_x ∩ W_o (§1). If |B_x| = 1, then R_x ∩ J = ∅ by (U), so both goods are in B_o:
(e1). |B_x| = 0 is impossible, since x would then not be threatened. Let |B_x| = 2. A 3-good agent has only one good
outside its base, so x has four goods, and R_x ∖ B_x = {r, s} ⊆ W_o. If r, s ∈ J, (U₂) with B′ = {r, s} gives
v(r) + v(s) < v(B_x), so there is no threat (θ_x ≤ v(W_o ∩ R_x)). If both are in B_o, we are in (e3), and R_x ∩ J = ∅.
Otherwise say r ∈ B_o and s ∈ J. (U₂) with B′ = {y, s}, y ∈ B_x, gives v(s) < v(y) for both y ∈ B_x. The threat gives
v(r) + v(s) > v(B_x), so v(r) > v(B_x) − v(s) > max_{y ∈ B_x} v(y). Hence r = a_x, s = d_x and B_x = {b_x, c_x}: (e2).

*Uniqueness.* In each case B_{o′} of an owner o′ exposing x must contain a good of R_x ∖ B_x that is not junk. In (e1)
and (e3) it must contain two such goods, and R_x ∖ B_x has at most three goods, already two in B_o. In (e2) the only
non-junk good of R_x ∖ B_x is a_x ∈ B_o.

*Protection.* Let X ⊇ B_o, X ⊆ W_o, |X| ≥ 3.
- In (e1) and (e3), X ∩ R_x = B_o, since R_x ∩ J = ∅. X ⊄ R_x, since |X| ≥ 3 > |B_o| = |X ∩ R_x|, so θ_x(X) =
  v_x(B_o). This exceeds v_x(B_x), since W_o threatens x and meets R_x in B_o alone.
- In (e2), if d_x ∉ X then X ∩ R_x ⊆ {a_x}, which is worth at most v(B_x). If d_x ∈ X then X ∩ R_x = {a_x, d_x}, and
  X ⊄ R_x (|X| ≥ 3), so θ_x(X) = v(a_x) + v(d_x) > v(B_x). ∎

**Corollary H4 (the criterion without frozen agents).** If P is Pareto-maximal, has no frozen agent and ω ≥ 1, then
every agent is free and the owner bundles have ω + 2 ≥ 3 goods (u = 0). So o is a removal-only owner iff no agent is
e1- or e3-exposed with respect to o and |Z_o| ≤ S − cap(o), where Z_o is the set of labels d_x of the e2-exposed agents
x. (Brute force: 0 disagreements with the exact deficit, §4.)

## 3. Theorem H0: no frozen agent

Let P ∈ 𝒫 have no frozen agent (NA = ∅). Then every base is need-free and nonempty, so a one-good base is the agent's
top. Write T for the number of agents with a one-good base; then S = T. A base worth more than a need-free base is
need-free: a good outside the new base is worth at most the old base's value, and a good of the old base is worth at
most that too.

**Theorem H0.** Let P ∈ 𝒫 have no frozen agent and ω ≥ 1, and satisfy (U) and (U₂) of Lemma H2 (every Pareto-maximal P does).
- (a) If T ≥ 2, some agent is a removal-only owner of P. So P is completable, and by Theorem 1′₄ the profile has an
  EFX₀ allocation with at most one bundle of more than two goods.
- (b) If no agent is a removal-only owner, then T ≤ 1, and each agent is exposed with respect to exactly one owner, with
  each owner exposing exactly one agent. So o ↦ (the agent exposed with respect to o) is a permutation π of N. If
  T = 1, the one-good holder t exposes an e2 agent, and every other agent's exposed agent is e1 or e3.

Lemma H3 uses Pareto-maximality only through (U) and (U₂), so H3 and H4 hold under this weaker hypothesis.

*Proof.* Let D(o) be the set of agents exposed with respect to o. Every agent is free, so by Lemma H3 the sets D(o) are
pairwise disjoint, and Σ_o |D(o)| ≤ n. Suppose no agent is a removal-only owner (Corollary H4).
- An agent o with a one-good base has no e1 or e3 exposure, since those need |B_o| = 2. So
  |D(o)| ≥ |Z_o| ≥ S − cap(o) + 1 = T.
- An agent with a pair has |D(o)| ≥ 1: an unhittable exposure, or |Z_o| ≥ T + 1 ≥ 1.

So n ≥ T · T + (n − T), that is T(T − 1) ≤ 0, and T ≤ 1. For T ≤ 1 the bound n ≥ Σ|D(o)| ≥ n is tight, so every
|D(o)| = 1 and every agent lies in one D(o). For T = 1: |D(t)| = 1 ≥ |Z_t| ≥ 1, so t's one exposure is e2. A pair-holder
whose exposure is e2 would need |Z_o| ≥ T + 1 = 2 > |D(o)|, so every pair-holder's exposure is e1 or e3. ∎

### 3.1 The rotation along a cycle of π

Let C be a cycle of π, and for y ∈ C let p = π⁻¹(y) be the owner exposing y. y wants In(y) = B_p ∩ R_y:
- one good for e2 (namely a_y);
- the whole of B_p for e1 and e3.

Let g(y) be y's best good of In(y). A *light* move of y takes g(y) and keeps its best own good that its successor
does not take. A *heavy* move takes In(y), plus the label d_y if y is e2 (then In(y) = {a_y}). The successor π(y)
takes take(π(y)): In(π(y)) if it moves heavy, else {g(π(y))}. y must move heavy if its successor takes all of B_y, or
if keep(y) = B_y ∖ take(π(y)) is empty, or if v(g(y)) + v(max keep(y)) ≤ v(B_y). Let H be the least set of agents
closed under this rule. (It grows monotonically, since a heavy successor takes more.)

**Lemma H5.** If the labels d_y of the e2 agents in H ∩ C are pairwise distinct, the move is a Pareto-improvement in
𝒫. Every y ∈ C gets:
- {g(y), best of keep(y)} if y ∉ H;
- In(y) if y ∈ H is e1 or e3;
- {a_y, d_y} if y ∈ H is e2.

Nobody else moves.

*Proof.* The new bases are pairwise disjoint. y takes only goods of B_p that p gives up (p keeps only keep(p) =
B_p ∖ take(y)), plus distinct junk labels. Each moved agent strictly gains:
- y ∉ H by the rule;
- e1 and e3 in H because W_p threatens y, with W_p ∩ R_y = B_p (Lemma H3);
- e2 in H because v(a_y) + v(d_y) > v(B_y).

New bases worth more than need-free bases are need-free, so the result has NA = ∅ and lies in 𝒫. The one-good holder
t (T = 1) is always in H: π(t) is e2 with In(π(t)) = {a_t} = B_t, so keep(t) = ∅. ∎

So at a Pareto-maximum that is not removal-only completable, every cycle of π contains two e2 agents of H with the same
bottom good: a **label collision**. Theorem H0 and Lemma H5 also give an algorithm for the case without frozen agents:
1. Start from any P without frozen agents.
2. Apply the improvements of (U) and (U₂).
3. If no agent is an owner, rotate a cycle of π.
Every step raises some agents' values and lowers none, so this stops. It can fail only at a label collision. At T ≤ 1 heavy moves are forced only by t and by e3 agents holding {a, d} whose
successor wants their top, and a heavy agent forces its predecessor. So each maximal heavy run starts, going backwards,
at an e2 agent. A collision is two such runs whose e2 starts share their bottom good.

**Corollary H0′ (frozen agents that nobody exposes).** The proof of (a) uses only that every exposed agent is free.
Let P ∈ 𝒫 be Pareto-maximal with ω ≥ 1, and suppose no frozen agent is exposed with respect to any free agent.
- If some free agent has an empty base, it is a removal-only owner. Its W_o = J exposes no free agent: e1 and e3
  need a pair B_o, and e2 needs a_x ∈ B_o.
- Otherwise, if at least two free agents hold one good each, some agent is a removal-only owner.

The count is that of (a), over the free agents, with T the number of free one-good holders and S = T.

### 3.2 The collision occurs: the gap is real

`k4/hall_instances/cyc6.inst`, a pure core, n = 6, m = 15. The agents and their values (good:value) are:

| agent | goods and values | base |
|---|---|---|
| y | 0:8 2:6 3:5 12:4 | {2,3} |
| z | 4:10 2:8 3:6 5:3 | {4,5} |
| w | 4:8 6:6 7:5 13:4 | {6,7} |
| y′ | 6:8 8:6 9:5 12:4 | {8,9} |
| z′ | 10:10 8:8 9:6 11:3 | {10,11} |
| w′ | 10:8 0:6 1:5 14:4 | {0,1} |

The junk is J = {12, 13, 14}. This P has no frozen agent, T = 0 and ω = 3, and it is Pareto-maximal among all 4,015
valid pre-allocations. The permutation π is the 6-cycle y → z → w → y′ → z′ → w′ → y:
- y is e2 w.r.t. w′, z is e3 w.r.t. y, and w is e2 w.r.t. z;
- y′ is e2 w.r.t. w, z′ is e3 w.r.t. y′, and w′ is e2 w.r.t. z′.

z and z′ hold {a, d}, and their successors want their tops. So z, z′, y and y′ are heavy, and both y and y′ need the
label 12. There are no slots, and every owner leaves one agent threatened. So P is not completable, not even with
protection by slot goods (there are none). Both implementations confirm it (`attempts/k4-hall-pareto-no-frozen.md`). The
profile still satisfies C₄ᵐⁱⁿ: 55 of the 56 Pareto-maxima without frozen agents are completable, and so are all 3
Σℓ-maxima. The repair is not Pareto:
- w′ gives 0 to y and takes its own label 14 (a loss for w′);
- y takes {0, 2} and gives 3 to z;
- z keeps its top 4 and takes 3, releasing 5;
- w does not move.

### 3.3 What is proved, and the consequence for C₄ᵐⁱⁿ

- Theorem H0 (a) and Lemma H5 prove: if a profile has a Pareto-maximal P ∈ 𝒫 with no frozen agent, ω ≥ 1 and either
  T ≥ 2, or T ≤ 1 without a label collision on some π-cycle, then P is completable. If ω ≤ 0, P is completable without
  an owner. In both cases the fewest frozen agents is 0 and P has deficit ≤ 0, so C₄ᵐⁱⁿ holds on that profile.
- Not proved: the collision case, and anything with frozen agents (Corollary H0′ aside).

**Proposition HT (the cores H_t of `k4/c4.md` §7).** For every t ≥ 1, the profile H_t has a removal-only completable
pre-allocation without frozen agents. H_t is the family on which LB₄ʳ needs ⌈2t/3⌉ rotations.

The pre-allocation P_t (all bases need-free, hence valid with NA = ∅) is:
- ℓ holds {g_1, z}, worth 14, more than every other good of ℓ;
- x_{j,1} holds {b_{j,1}, c_{j,1}} (10 > 8);
- x_{j,2} holds {a_{j,2}, b_{j,2}} and x_{j,3} holds {a_{j,3}, b_{j,3}};
- every y_j holds its top {a_{j,1}}.

The junk is u, u′, the c_{j,2}, c_{j,3} and g_2, …, g_t. So |J| = 3t + 1, S = t (the y_j), and ω = 2t + 1.

With owner y_1, the set W = {a_{1,1}} ∪ J threatens nobody:
- ℓ values u, u′ in W (9 < 14);
- x_{j,1} values at most one good of W (g_j, or a_{1,1} for j = 1; 3 or 8 < 10);
- x_{j,2} and x_{j,3} value c and g_j in W (7 < 14);
- y_j (j ≥ 2) values at most g_{j+1} in W (its other a's are in the x's bases, and z is ℓ's).

So any t − 1 junk goods may go to the slots of y_2, …, y_t, and y_1 takes the rest (2t + 3 goods). `k4/hall_ht.py`
re-checks the allocation against the raw EFX₀ definition for t ≤ 12. `k4/c4.md` §7 already gives an EFX₀ allocation of H_t
with ℓ the owner (checked for t ≤ 8). The point here is that H_t is in the easy regime of this file: no frozen agent is
needed.

### 3.4 Closing the collision (open)

Conjecture K4.HALL.F0Σ: if some P ∈ 𝒫 has no frozen agent, every Σℓ-maximum among those P is removal-only completable
(evidence §4). A proof would show that a collision at a Σℓ-maximum yields a Σℓ-increasing move. In cyc6 the repair above
is such a move:
- y moves from level {b,c} to {a,b}, a gain of at least 3;
- z moves from {a,d} to {a,c}, a gain of at least 2 (it passes {a,d} and {b,c});
- w′ moves from {b,c} to {c,d}, a loss of at most 4 (only {c,d}, {b,d}, {a}, {b} can lie in between).

The general collision needs the same count along heavy runs of any length.

## 4. Evidence and cross-checks

Tools: `k4/hall.c` enumerates 𝒫 for every strict profile of a core, computes the exact removal-only deficit, and has
the counters below. It was written from the definitions and agrees with `k4/c4x.c` (PR #36), profile by profile, on
every profile with n = 2 and on 5,100 random profiles with n = 3 (`results/k4_hall_xcheck.log`). `k4/hall_check.py` is
an independent plain-Python checker for single pre-allocations: it tries every completion and re-checks the raw
EFX₀ definition. `k4/hall_random.py` generates random instances that are not cores.

**Exhaustive, n ≤ 3** (every strict profile of every k = 4 core with n = 2, 3; `results/k4_hall_n3.log`,
`k4/hall.c -P -G`). The cross-checked quantities also reproduce `k4/c4x.c`'s: C₄ᵐⁱⁿ holds on all 189,216 + 299,837,376
profiles.

| n | profiles with a pre-allocation without frozen agents | their Pareto-maxima (ω ≥ 1 or not) | every one completable | F0 checks at the maxima with ω ≥ 1 |
|---|---|---|---|---|
| 2 | 187,920 of 189,216 | 334,156 | yes (187,920 profiles) | 172,108 maxima: Lemma U, U₂, H3 shapes, criterion H4: 0 violations; no maximum without a valid owner |
| 3 | 283,959,584 of 299,837,376 | 786,313,328 | yes (283,959,584 profiles) | 287,013,316 maxima: 0 violations; no maximum without a valid owner |

**Lemma H5, directly** (`-G`): every pre-allocation (not only the Pareto-maxima) without frozen agents, with ω ≥ 1, that
satisfies (U) and (U₂) and has no removal-only owner. There are 5,720 of them at n = 2 and 187,280 at n = 3, each with
the exposure relation a permutation and T ≤ 1 (Theorem H0 (b)). The rotation rule of §3.1 gives a valid
Pareto-improvement for every one of them (0 failures, 0 label collisions). So the collision needs more agents; cyc6 has
six.

With frozen agents (the same run), the Pareto-maxima inside the min-frozen set are not always completable, as known from
`k4/c4x.md` §5:
- F = 1: 15,414,020 profiles, 292,512 of them with a non-completable maximum, 128 with none completable;
- F = 2: 463,772 profiles, 27,612 with a non-completable maximum, 0 with none completable.

§5 has the structure of these failures, and `results/k4_hall_n3_pareto.log` the counters of Lemmas H6, H7 and conjecture
BT on the same profiles.

**The level-sum form** (conjecture K4.HALL.F0S; `results/k4_hall_n3_sumlev.log`, `k4/hall.c -N -Q1`, every profile with
n ≤ 3): wherever a pre-allocation without frozen agents exists (187,920 + 283,959,584 profiles), every Σℓ-maximum among
them is completable. With frozen agents, the Σℓ-maxima inside the min-frozen class fail on 56,776 (F = 1) and 27,612
(F = 2) profiles with n = 3; that is `k4/c4x.md`'s (−frozen, Σℓ) failure.

Around cyc6 (`results/k4_hall_cyc6_nb.log`) one or two agents' types (w, w′) are varied over all strict balanced
types. Pareto-maxima without frozen agents fail on 10, 10, 20, 10, 10, 20 of the 288, 288, 144, 288, 288, 144
one-agent profiles and on 400 of the 20,736 two-agent profiles. The Σℓ-maxima fail on none of them.

**Samples, n = 4 and n = 5** (`results/k4_hall_samples.log`; `-P -G`, seeded random strict profiles per core). The
columns are:
- (1) profiles with a pre-allocation without frozen agents;
- (2) of those, profiles where every Pareto-maximum without frozen agents is completable;
- (3) Pareto-maxima without frozen agents with ω ≥ 1 checked for Lemmas U, U₂, H3 and H4 (0 violations everywhere);
- (4) pre-allocations checked by the rotation rule (all repaired).

| class | profiles | (1) | (2) | (3) | (4) |
|---|---|---|---|---|---|
| n = 4, one 4-good agent | 67,500 | 50,449 | 50,449 | 1,785 | 0 |
| n = 4, two | 61,800 | 51,272 | 51,272 | 20,322 | 0 |
| n = 4, three | 33,900 | 29,580 | 29,580 | 30,987 | 0 |
| n = 4, pure | 65,700 | 58,290 | 58,290 | 100,496 | 3 |
| n = 5, one | 34,700 | 20,156 | 20,156 | 97 | 0 |
| n = 5, two | 27,340 | 18,336 | 18,336 | 2,035 | 0 |

The same log has the Σℓ form and the big-top-last potential of §5 (`-N -Q1`, `-N -Q5`) on the n = 4 samples. The
Σℓ-maxima inside the min-frozen class have no failure without frozen agents; with frozen agents they fail on 1 + 2
(three 4-good agents) and 24 + 4 (pure) profiles. The big-top-last maxima have no failure at all on the four n = 4
samples.

## 5. With frozen agents: what survives, and where k = 4 breaks

Theorem H0's counting needs every exposed agent to be exposed with respect to one owner. Lemma H3 gives this for free
agents. For frozen agents the analogue of Theorem K3's Lemma R still holds, but it no longer excludes every shared
exposure.

**Lemma H6 (frozen agents cannot improve along a need chain).** Let P ∈ 𝒫 be Pareto-maximal, x frozen with base {g},
and τ a chain end of x (a free agent reached from x in the need digraph through frozen agents; one exists by Lemma C of
`k4/c4x.md` §3). Then v_x(O) < v_x(g) for every set O ⊆ R_x ∩ (J ∪ B_τ) of one or two goods.

*Proof.* Take a simple need chain x = x₀ → x₁ → … → x_s = τ. Suppose some O has v_x(O) > v_x(g). Make the moves:
- each x_{i+1} takes B_{x_i} (a good it needed);
- x takes O;
- the rest of (J ∪ B_τ) ∖ O becomes junk.

Check that the result is a Pareto-improvement in 𝒫:
- Every moved agent strictly gains, so its needs shrink. For x, N(O) ⊆ N(g), since v(O) > v(g). Hence NA′ ⊆ NA.
- Every good of N(O) is still a one-good base: g is x₁'s, and the others did not move or moved along the chain.
- B_τ is not in NA, because τ is free: a one-good free base is not needed, and a pair misses NA by (V2).
- So the new junk and the goods of O miss NA′: (V1) and (V2) hold.

So P′ ∈ 𝒫 dominates P. ∎

At k = 3, Lemma H6 for a top-holder is Lemma R of `k4/c4x.md` §3. At k = 4 it excludes every improving set of at most two
goods. What remains is the one thing a base cannot hold: three goods.

**Lemma H7 (frozen exposed agents).** Let P ∈ 𝒫 be Pareto-maximal, o free, and x frozen with base {g}, exposed with
respect to o. Then exactly one of the following holds.
- **(G) global.** x has four goods, g = a_x, a_x > b_x + c_x (a *big-top* agent), and R_x ∖ {a_x} ⊆ J. Then x is
  exposed with respect to every free agent.
- **(G1)** Not (G); o is a chain end of x; x is a big-top agent with g = a_x and R_x ∖ {a_x} ⊆ J ∪ B_o.
- **(L) local.** Not (G); o is not a chain end of x, and the threat uses a good of B_o.

*Proof.* Every good of R_x ∩ W_o is worth at most v(g), and a threat needs a subset Q ⊆ R_x ∩ W_o with v(Q) > v(g).
- If J alone threatens, Lemma H6 with any chain end shows that no one or two goods of R_x ∩ J beat g. So Q has three
  goods, and so does R_x ∖ {g}, and x has four goods. g = a_x, since for g ≠ a_x the good a_x is needed, hence not in
  W_o. No pair of low(x) beats a_x, so a_x > b_x + c_x: (G).
- If o is a chain end, Lemma H6 with τ = o gives the same conclusion within J ∪ B_o: (G1).
- Otherwise the threat must use a good of B_o: (L). ∎

**What this gives, and what it does not.**
- A local exposure needs one label, or two (e.g., x holds a with c + d < a < b + d, b ∈ B_o and c, d ∈ J), or is
  unhittable.
- A local exposure is tied to the owners whose base holds one of x's lower goods. There are up to three of them (89
  frozen agents exposed w.r.t. two or more owners in the n = 3 sample below).
- (G) and (G1) are the (G1) mechanism of `k4/c4x.md` §5: the rotation that would repair x gives it three goods, so x
  would have to become the owner.

**The data** (`k4/hall.c -N`, Pareto-maxima inside the min-frozen set, with frozen agents and ω ≥ 1):
- **Every profile with n ≤ 3** (`results/k4_hall_n3_pareto.log`):
  - 19,259,044 + 2,592 such maxima. Lemma H6 has no violation, and every global exposure has the shape (G).
  - The frozen exposures (agent, owner) number: global 504,540; G1-type 1,664,700; local with one label 6,052,996;
    local with two labels 371,136; local unhittable 883,312. 248,904 frozen agents are exposed w.r.t. two or more
    owners.
  - 377,832 maxima are not completable, and **every one of them has a frozen big-top agent**. 113,136 of them have no
    (G1) configuration, and 180,876 no global exposure.
- The samples at n = 4 and 5 (`results/k4_hall_samples.log`) agree: 0 non-completable maxima without a frozen big-top
  agent.
- In a non-completable maximum without (G) or (G1) exposures, the big-top agent becomes the owner through an exchange
  cycle that a Pareto-maximum does not see. In those, the big-top agent becomes the owner through an exchange
  cycle that a Pareto-maximum does not see. Example, core 33 of `results/k4_certs_3.json.gz`, instance
  `k4/hall_instances/local3.inst`:
  - agent 0 has values 0:3, 1:2, 2:10, 3:6 and base {2}, frozen;
  - agent 1 has values 2:8, 4:2, 5:3, 6:4 and base {5, 6};
  - agent 2 has values 3:7, 4:3, 5:5, 6:6 and base {3, 4};
  - J = {0, 1}, and there are no slots.
  - Owner 1 leaves agent 2 threatened (e3). Owner 2 leaves agent 0 threatened (local, one label). So P is Pareto-maximal
    and not completable.
  - The cycle "0 gives 2 to 1, 1 gives {5, 6} to 2, 2 gives 3 to 0, 0 becomes the owner of {3, 0, 1, 4}" is completable.

**Conjecture K4.HALL.BT (the obstruction is the big-top agent).** A Pareto-maximal P ∈ 𝒫 with ω ≥ 1 that is not
removal-only completable either has a frozen big-top agent, or has no frozen agent and a label collision (§3.1). At
k = 3 there are no big-top agents, which matches Theorem K3. With frozen agents it holds on every profile with n ≤ 3
and on the n = 4, 5 samples; without frozen agents only the n = 6 collision of §3.2 is known.

The potential "fewest frozen agents, then Σℓ over the agents that are not of big-top type, then Σℓ over the big-top
types" (`-Q5`) gives priority as the conjecture suggests. It has 1 non-completable maximum in a 102,000-profile n = 3
sample (core 41; the exhaustive count is in `results/k4_hall_n3_bigtoplast.log`) and none in the four n = 4 samples of
§4. The variants "big-top types' Σℓ minimized" and "big-top types' smallest bases
first" fail 6 and 4 times on the same n = 3 sample. So the priority is right, but the exact rule is not.
