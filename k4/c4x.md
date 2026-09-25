# C₄∃ by an extremal valid pre-allocation

Workstream `proof/k4-c4x`, ledger rows K4.C4X.* (CONJECTURE / EVIDENCE only), ledger open item 18. A second,
independent attempt at the last open step of the k = 4 case; the other one is the draft PR on `proof/k4-c4`
(`k4/c4.md` there, unreviewed), which follows LB⁺'s counting over runs of Phase 1. This file does not follow that route:
it takes a pre-allocation that is extremal for a potential over *all* valid pre-allocations.

**Target C₄∃.** For every strict profile of every k = 4 core, *some* valid pre-allocation (`k4/lb4.md` §1) has a
completion satisfying (OC₄) in which frozen agents hold their base and only the owner's bundle has more than two
goods. By Theorem 1′₄ (machine-checked, `lean/EFX/PreAllocK.lean`: `SoundCompletion`, `target4_of_completions`),
K4.TIE and K4.CORE this gives TARGET₄.

**Status.** Work in progress; see the summary at the end of the session.

## 1. The space 𝒫 and completability

Fix a strict profile of a k = 4 core (agents with |R_i| ∈ {3, 4}, strictly balanced; all nonempty subset sums of each
R_i distinct).

**Definition (𝒫).** A pre-allocation is a family of pairwise disjoint bases B_i ⊆ R_i with |B_i| ≤ 2. Its junk is
J = M ∖ ⋃ B_i, and the needs of i are the value-based ones, N_i = {g ∈ R_i ∖ B_i : v_i(g) > v_i(B_i)}. It is valid if
(V1) J ∩ NA = ∅ and (V2) no good of a two-good base is in NA, where NA = ⋃ N_i. 𝒫 is the set of valid pre-allocations.

Remarks.
- The needs are the smallest the Definition of `k4/lb4.md` §1 allows, so nothing is lost: a completion that satisfies
  (OC₄) for larger needs does so for these (a larger NA only adds frozen agents and removes slots). With strict types
  they are the pick needs {g : g ≻_i Y} for a one-good base {Y}, and R_i for an empty base.
- Every run of Phase 1 of LB₄ followed by any upgrades, and every rotation of LB₄ʳ whose rotated base has at most two
  goods, is in 𝒫 (`k4/lb4.md` §2, §5), so 𝒫 ≠ ∅.
- (V1) and (V2) say: *every needed good is the whole base of one agent*. Such an agent is frozen (F); the others are
  free, with cap(i) = 2 − |B_i| slots. As in `k4/lb4.md` §1, |F| = |NA| and ω := |J| − S = |F| − σ with σ = 2n − m.

**Definition (completable).** P ∈ 𝒫 is completable if it has a completion in the sense of `lean/EFX/PreAllocK.lean`
(`Completion`, `SoundCompletion`) that satisfies (OC₄): an owner o (a free agent) or none; X_i = B_i ∪ C_i with C_i ⊆ J,
C_i = ∅ for frozen i ≠ o and |B_i| + |C_i| ≤ 2 for free i ≠ o; X_o = B_o ∪ (the rest of J); the owner's needs taken
from its bundle, N_o^X = {g ∈ R_o ∖ X_o : v_o(g) > v_o(X_o)} (frozen status and slots recomputed with them); and
v_j(X_o ∖ h) ≤ v_j(X_j) for all j ≠ o, h ∈ X_o. By Theorem 1′₄ such an X is EFX₀ with at most one bundle of more than
two goods. If ω ≤ 0, the completion without owner exists.

**Removal-only completability.** A sufficient condition: some owner o and C ⊆ J such that X_o = B_o ∪ (J ∖ C)
threatens no agent x ≠ o *holding its base alone* (max_h v_x(X_o ∖ h) ≤ v_x(B_x)), and |C| ≤ S_o(C), the number of
slots of the agents other than o with frozen status computed from the owner's needs N_o^X. Then C can go into those
slots in any way. Its *deficit* is def(P) := |J| − S if that is ≤ 0, and otherwise the least value of |C| − S_o(C) over
the free owners o and the sets C ⊆ J that leave nobody threatened; P is removal-only completable iff def(P) ≤ 0.

## 2. What the computation says (step 1)

Tools: `k4/c4x.c` enumerates 𝒫 for every strict profile of a core (types from `k4/check4.py`, as every k = 4
tool), tests every candidate potential Φ in both forms, and has the exact completability test and the deficit;
`k4/c4x_run.py` drives it over the certificate files of K4.R3–R4 (`results/k4_certs_*.json.gz`) and the k = 3 core
list `results/certs_lb_2_6.json.gz`. `k4/c4x_check.py` is an independent implementation written from the definitions
(every base map, every completion literally as Lean's `Completion` with `ownerNeeds`, (OC₄), and a raw EFX₀ re-check
of every completion found); `k4/c4x_crosscheck.py` compares the two profile by profile (number of valid
pre-allocations, number of completable ones, and both forms for eight potentials).

For a potential Φ: "every" = every Φ-maximum of 𝒫 is completable (the form a proof would establish); "some" = some
Φ-maximum is. Potentials are maximized; lexicographic ones are written as tuples. ℓ_i(B) = #{T ⊆ R_i : v_i(T) <
v_i(B)} is the level of a base (`k4/gm4.md`), leximin/leximax are over the level vector, "slots" is S, "-frozen" is
−|F| (equivalently −ω), and "-deficit" is −def(P), computed on the pre-allocations with the fewest frozen agents.

## 3. The extremal principle where it works: k = 3 (Theorem K3)

At k = 3 the principle closes with the plainest potential: **every Pareto-maximal valid pre-allocation is
completable.** This is a second, structural proof of conjecture D at k = 3 (already proved and machine-checked by LB⁺,
`proofs/lb_last_step.md`), and it shows which properties of three goods the principle needs; §4 checks each of them at
k = 4. Written proof, not yet reviewed: CONJECTURE in the ledger (K4.C4X.K3) until an independent review.

**Setting.** A k = 3 core with strict types: every agent i has R_i = {a_i, b_i, c_i}, v(a) > v(b) > v(c) > 0,
v(a) < v(b) + v(c), all subset sums distinct; m ≤ 2n (L4), so σ = 2n − m ≥ 0. 𝒫 as in §1. P′ *Pareto-dominates* P if
v_i(B′_i) ≥ v_i(B_i) for all i with one inequality strict; P is *Pareto-maximal* if no P′ ∈ 𝒫 dominates it (it exists:
𝒫 is finite and nonempty). Every maximum of a potential that increases strictly with each v_i(B_i) (Σℓ, leximin,
leximax, Σ 2^ℓ, Σ v) is Pareto-maximal.

Notation for P ∈ 𝒫: a *terminal* is a free agent with nonempty needs; the *need digraph* has an edge y → z when B_y is
a single good g and g ∈ N_z. For a *top-holder* x (B_x = {a_x}) write low(x) = {b_x, c_x}.

**Three-good facts.** (i) A two-good base has no needs and is never threatened: any other bundle meets R_x in at most
one good, worth less than the base (balance). (ii) An agent holding {b} or {c} or nothing is never threatened by a
bundle X ⊆ W := B_o ∪ J of a free owner o: the goods of R_x above its base are needed, hence not in W (J by (V1), B_o
because o is free), and at most one good lies below. (iii) A top-holder x is threatened by X only if low(x) ⊆ X.

**Lemma U (no upgrade; any k).** If P is Pareto-maximal and x is free with |B_x| ≤ 1, then R_x ∩ J = ∅.

*Proof.* If B_x = ∅, R_x = N_x ⊆ NA, which misses J by (V1). If B_x = {y} and g ∈ R_x ∩ J, let B′_x = {y, g}. Its
value-based needs are contained in N_x, so NA′ ⊆ NA; J′ = J ∖ {g}; (V2) for {y, g}: y ∉ NA because x is free, g ∉ NA by
(V1). So P′ ∈ 𝒫, and it dominates P. ∎

**Lemma C (need chains; any k).** If P is Pareto-maximal, the need digraph has no directed cycle of frozen agents,
and every frozen agent x has a *need chain* x = x₀ → x₁ → … → x_s (s ≥ 1, x₀, …, x_{s−1} frozen and distinct, x_s a
terminal).

*Proof.* On a cycle y₀ → … → y_{k−1} → y₀ of frozen agents let every y_{i+1} take B_{y_i}: the bases stay single goods,
the set of base goods, J and the two-good bases are unchanged, and every y_{i+1} gets a good it needed, so its needs
shrink: P′ ∈ 𝒫 dominates P. A frozen agent has a successor (someone needs its good); following successors through
frozen agents cannot cycle, so it reaches a free agent, which needs the previous good: a terminal. ∎

**Lemma R (LB⁺'s rotation is excluded; k = 3).** If P is Pareto-maximal, x is a frozen top-holder and τ is the end of a
need chain from x, then low(x) ⊄ J ∪ B_τ.

*Proof.* Otherwise apply the rotation of `proofs/lb_last_step.md` Theorem B: every x_i (i ≥ 1) takes B_{x_{i−1}}, x takes
low(x), and B_τ becomes junk. B_τ is empty or one good not in NA (a terminal is free, and it has no two-good base by
fact (i)), so J′ = (J ∪ B_τ) ∖ low(x) misses NA ⊇ NA′ ((V1)), low(x) misses NA ((V2)), and every agent of the chain
strictly gains (x by balance). P′ ∈ 𝒫 dominates P. ∎

**Lemma E (who is exposed; k = 3).** Let P be Pareto-maximal and t a terminal, W_t = B_t ∪ J, and E_t the set of agents
x ≠ t that some X ⊆ W_t threatens while x holds B_x alone. If x ∈ E_t, then x is a frozen top-holder, B_t = {y_t} with
y_t ∈ low(x), the other good z_x of low(x) is junk, and no need chain from x ends at t. (So E_t = ∅ if B_t = ∅.)

*Proof.* By fact (iii) x is a top-holder with low(x) ⊆ W_t. If x is free, low(x) ∩ J = ∅ (Lemma U), so low(x) ⊆ B_t,
which has at most one good: impossible. So x is frozen; by Lemma C some need chain from x ends at a terminal τ, and by
Lemma R low(x) ⊄ J ∪ B_τ ⊇ J. Hence exactly one good of low(x) is in B_t and the other is junk. A chain from x ending at
t would contradict Lemma R with τ = t. ∎

Write Z_t = {z_x : x ∈ E_t} ⊆ J, and T for the number of terminals.

**Lemma O (owner criterion; k = 3).** If ω ≥ 1 and t is a terminal with |Z_t| ≤ S − cap(t), then P has a completion with
owner t that satisfies (OC₄), with the owner's needs from its base.

*Proof.* |J| = S + ω > S − cap(t). Take C with Z_t ⊆ C ⊆ J and |C| = S − cap(t), fill the slots of the free agents other
than t with C, and let X_t = B_t ∪ (J ∖ C) ⊆ W_t. If X_t threatened some x ≠ t holding X_x ⊇ B_x, it would threaten x
holding B_x (monotonicity, `k4/c4.md` §1), so x ∈ E_t and low(x) ⊆ X_t, but z_x ∈ C. Only X_t has more than two goods and
frozen agents hold their bases, so Theorem 1′₄ applies (`SoundCompletion.of_baseNeeds`). ∎

**Theorem K3.** Every Pareto-maximal P ∈ 𝒫 of a k = 3 core is completable: without owner if ω ≤ 0, and otherwise with
a terminal as owner and a removal-only completion (Lemma O).

*Proof.* Let ω ≥ 1. Then |F| = ω + σ ≥ 1, so a terminal exists (Lemma C). Suppose |Z_t| > S − cap(t) for every terminal
t. The other terminals have cap ≥ 1, so S − cap(t) ≥ T − 1 and |Z_t| ≥ T for every terminal t.

*A cycle with distinct junk labels.* Start at a terminal t₁. At step r ≥ 1, the labels z_{x₁}, …, z_{x_{r−1}} are used;
while r ≤ T, pick x_r ∈ E_{t_r} with z_{x_r} unused (|Z_{t_r}| ≥ T > r − 1) and let t_{r+1} be the end of a need chain
from x_r (Lemma C); t_{r+1} ≠ t_r (Lemma E). Some t_{r+1} repeats an earlier t_q by step T. This gives a cycle
t_q, x_q, …, t_r, x_r (back to t_q): distinct terminals, x_i ∈ E_{t_i} with pairwise distinct z_{x_i}, and need chains
Q_i from x_i to the next terminal.

*Shortening.* Among all such cycles take one with the fewest terminals, with simple chains. It has at least two
terminals (a chain from x_i to t_i is excluded by Lemma E). A chain's middle agents are frozen and terminals are free,
so no terminal is a middle agent; a top-holder has no needs, so no edge of the need digraph enters an x_j, and no x_j
lies on another chain. If Q_i and Q_j (i ≠ j) shared a frozen agent q, then x_i ⇝ q ⇝ (end of Q_j) would be a need chain
from x_i to the terminal after t_j, which is not t_i (Lemma E); cutting the cycle there removes the terminals strictly
after t_i up to t_j, at least one, and keeps a subset of the labels: fewer terminals, a contradiction. So the chains are
pairwise disjoint.

*The cycle move.* Every x_i takes low(x_i) = {y_{t_i}, z_{x_i}}; along Q_i every agent after x_i takes the base good of
its predecessor (so the next terminal takes the good of the last frozen agent of Q_i and gives up y_{t_{i+1}}, which
goes to x_{i+1}); nobody else moves. Every good still has one holder (the chains are disjoint, the labels distinct), J′ =
J ∖ {z_{x_i}}, every base has at most two goods. Every moved agent strictly gains (x_i by balance, the others take a
needed good), so its needs shrink and NA′ ⊆ NA. (V1): J′ ⊆ J. (V2): the new two-good bases {y_{t_i}, z_{x_i}} miss NA
(t_i is free; (V1)), and the old ones belong to agents that did not move (two-good agents are not terminals, frozen
agents or top-holders). So P′ ∈ 𝒫 dominates P: a contradiction. Hence some terminal t has |Z_t| ≤ S − cap(t), and Lemma
O applies. ∎

*Where three goods were used.* Fact (i) (two-good bases are envy-free, so upgraded agents are never exposed and never
chain ends); fact (iii) with Lemma R (a top-holder's only better base without its top is the pair low(x), which has
two goods, so the rotation stays in 𝒫, and an exposed agent needs exactly one junk good kept out); σ ≥ 0 (a terminal
exists when ω ≥ 1). Lemmas U and C hold for every k. The private-goods rule of cores is not used.

*Checks against brute force* (`k4/c4x.c -T`, counters of `k4/c4x_run.py`): on every Pareto-maximum with ω ≥ 1 of
every strict profile of every k = 3 core with n ≤ 5 (343 cores, 2,333,088 profiles, 343,256 such maxima) Lemmas U, C,
E hold (0 violations), every Pareto-maximum is completable, some terminal is always a valid owner, and the criterion
|Z_t| ≤ S − cap(t) agrees with the exact owner test on every terminal. "Every terminal is a valid owner" is false
(80 terminals, all in the situation the label argument handles: two exposed agents whose chains end at one terminal).
