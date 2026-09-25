# C₄∃ by an extremal valid pre-allocation

Workstream `proof/k4-c4x`, ledger rows K4.C4X.* (CONJECTURE / EVIDENCE only), ledger open item 18. A second,
independent attempt at the last open step of the k = 4 case; the other one is the draft PR on `proof/k4-c4`
(`k4/c4.md` there, unreviewed), which follows LB⁺'s counting over runs of Phase 1. This file does not follow that route:
it takes a pre-allocation that is extremal for a potential over *all* valid pre-allocations.

**Target C₄∃.** For every strict profile of every k = 4 core, *some* valid pre-allocation (`k4/lb4.md` §1) has a
completion satisfying (OC₄) in which frozen agents hold their base and only the owner's bundle has more than two
goods. By Theorem 1′₄ (machine-checked, `lean/EFX/PreAllocK.lean`: `SoundCompletion`, `target4_of_completions`),
K4.TIE and K4.CORE this gives TARGET₄. Lean's form of C₄∃ (`TheoremC4exists`, bases of any goods) is equivalent to
K4.D on strict cores (`C4exists_iff`, PR #35); for the narrower space 𝒫 used here only "completable ⇒ K4.D" holds (§1).

**Status.** Not a proof of C₄∃. What is here:
- **The space and the test** (§1): 𝒫 = valid pre-allocations with bases of at most two goods and value-based needs;
  *completable* = has a completion that is a Lean `SoundCompletion`. `k4/c4x.c` enumerates 𝒫 for every strict profile
  and tests completability exactly; an independent Python checker agrees with it on every profile with n = 2 and on a
  sample with n = 3.
- **No simple potential works at k = 4** (§2, §5, `attempts/k4-c4x-*.md`): for Σℓ, Σ 2^ℓ, leximax, leximin, Pareto-
  maximality, fewest frozen agents and their simple tie-breaks, some maximum is not completable (smallest failures at
  n = 2 or 3, each confirmed by both implementations); for several, no maximum is.
- **Conjecture C₄ᵐⁱⁿ** (§5, K4.C4X.MIN): some pre-allocation with the fewest frozen agents is completable, even with
  protection by removal only (deficit ≤ 0); equivalently every maximum of (−frozen, −deficit) is completable.
  Exhaustive for n ≤ 3 (300,026,592 strict profiles) and n = 4 with one or two 4-good agents, sampled beyond, and true on
  the cores H_1–H_3 that defeat LB₄ʳ's bounded rotations (§6). A proof needs an augmenting step that lowers the deficit.
- **Theorem K3** (§3, written proof, not reviewed): at k = 3 every Pareto-maximal P ∈ 𝒫 is completable, with a
  terminal as owner: if no terminal were valid, a walk with fresh junk labels closes a cycle of exposures whose
  rotation is a Pareto improvement. A second, extremal proof of D at k = 3; every lemma is checked by brute force.
- **One 4-good agent** (§4, written proofs, not reviewed): with the 3-good agents first,
  Ψ = (Σℓ over the 3-good agents, ℓ_w), every Ψ-maximum is completable in the cases w frozen (Theorem A), w a terminal
  with at most one good (B₁), w free, not a terminal and not exposed (C0), and no terminal (Lemma C2). **The gap:** w
  free and holding two goods (cases B₂ and C1, §4.3); on the data w or a 3-good terminal is always a valid owner there
  (w alone is not enough from n = 5 on). Every Ψ-maximum is completable for n ≤ 4 (exhaustive) and on 3,470,000 sampled
  profiles with n = 5.

Nothing here changes K4.D or K4.T.

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
- The picks of any run of Phase 1 of LB₄, with their pick needs, form a valid pre-allocation (`k4/lb4.md` §2: (V1)
  by (I2); there are no two-good bases), so 𝒫 ≠ ∅.
- (V1) and (V2) say: *every needed good is the whole base of one agent*. Such an agent is frozen (F); the others are
  free, with cap(i) = 2 − |B_i| slots. As in `k4/lb4.md` §1, |F| = |NA| and ω := |J| − S = |F| − σ with σ = 2n − m.

**Definition (completable).** P ∈ 𝒫 is completable if it has a completion in the sense of `lean/EFX/PreAllocK.lean`
(`Completion`, `SoundCompletion`) that satisfies (OC₄): an owner o (a free agent) or none; X_i = B_i ∪ C_i with C_i ⊆ J,
C_i = ∅ for frozen i ≠ o and |B_i| + |C_i| ≤ 2 for free i ≠ o; X_o = B_o ∪ (the rest of J); the owner's needs taken
from its bundle, N_o^X = {g ∈ R_o ∖ X_o : v_o(g) > v_o(X_o)} (frozen status and slots recomputed with them); and
v_j(X_o ∖ h) ≤ v_j(X_j) for all j ≠ o, h ∈ X_o. By Theorem 1′₄ such an X is EFX₀ with at most one bundle of more than
two goods. If ω ≤ 0, the completion without owner exists.

**Relation to the Lean definitions** (`lean/EFX/PreAllocK.lean`; the target `EFX.LB4R.TheoremC4exists` of PR #35). A
completable P ∈ 𝒫 with its completion is literally an `EFX.LB4.SoundCompletion`: `base` maps each good of B_i to i; `N`
is the value-based needs, which satisfy `Needs` (its lower bound, and its upper bound since v_i(g) > v_i(B_i) ≥ 0);
`Valid` is (V1), (V2); `Frozen` is "the base is one good, in NA"; `Completion`'s conditions (owner not frozen, frozen
non-owners get no junk, |C_i| + |B_i| ≤ 2 for free non-owners) are the ones `k4/c4x.c` and `k4/c4x_check.py` impose,
with the owner's needs replaced by `ownerNeeds` exactly as in `SoundCompletion`; and `OC` is (OC₄). 𝒫 is a *subclass* of
Lean's pre-allocations: Lean allows bases of any size and with goods outside R_i, and any `Needs` between the two
bounds; 𝒫 takes bases inside R_i of at most two goods and the smallest needs. Every statement here produces a sound
completion, so it proves `TheoremC4exists` for the profiles it covers. By the audit of PR #35 (`C4exists_iff`, which
rests on `sound_of_d2`: a D2-shaped EFX₀ allocation is a sound completion whose bases are its whole bundles, of any size
and possibly with goods outside R_i), Lean's C₄∃ is equivalent to K4.D on strict cores. 𝒫 is narrower, so for 𝒫 only one
direction holds: a completable P gives K4.D for its profile.

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

**Main table.** Profiles on which the form fails (0 everywhere in the column C₄ᵐⁱⁿ: some pre-allocation with the
fewest frozen agents has deficit ≤ 0, i.e. every maximum of (−frozen, −deficit) is completable). "All" = every strict
profile of every core of the class; "sample" = random strict profiles per core (seeded, `c4x_run.py --rand`).

| cores | profiles | C₄ᵐⁱⁿ fails | −frozen: every / some | leximin: every / some | log |
|---|---|---|---|---|---|
| k = 4, n = 2 (5) | all 189,216 | 0 | 50,320 / 0 | 0 / 0 | `results/k4_c4x_n3.log`, `k4_c4x_n3_pareto.log` |
| k = 4, n = 3 (51) | all 299,837,376 | 0 | 12,710,832 / 0 | 38,016 / 128 | the same |
| k = 4, n = 4, one 4-good agent (135) | all 7,247,232 | 0 | 176 / 0 | 0 / 0 | `results/k4_c4x_n4_1.log` |
| k = 4, n = 4, two (309) | all 724,847,616 | 0 | 203,952 / 0 | 4,520 / 1,772 | `results/k4_c4x_n4_2.log` |
| k = 4, n = 4, three (339) | sample 1,695,000 | 0 | 23,942 / 0 | 78 / 5 | `results/k4_c4x_samples.log` |
| k = 4, n = 4, pure (219) | sample 1,095,000 | 0 | 73,946 / 0 | 182 / 4 | the same |
| k = 4, n = 5, one 4-good agent (1,735) | sample 1,735,000 | 0 | 1 / 0 | 0 / 0 | the same |
| k = 4, n = 5, two (5,468) | sample 546,800 | 0 | 24 / 0 | 2 / 2 | the same |
| k = 4, random connected cores, n = 6–8 | 4,200 (one per random core) | 0 | – | – | `results/k4_c4x_random.log` |
| k = 4, H_1, H_2, H_3 (§6) | 3 | 0 | fails / 0 | 0 / 0 | `results/k4_c4x_ht.log` |
| k = 3, n ≤ 6 (3,436) | all 146,640,096 | 0 | 0 / 0 | 0 / 0 | `results/k4_c4x_k3_pareto.log` |

At k = 3 even the plain frozen count works: *every* valid pre-allocation with the fewest frozen agents is completable (n
≤ 6), and so is every Pareto-maximum (Theorem K3). At k = 4 neither holds (n = 2 for the frozen count, n = 3 for Pareto;
§5 and `attempts/`). The other potentials tested (Σℓ, Σ 2^ℓ, leximax, Σv, slots, exposure counts and 31 lexicographic
combinations; `results/k4_c4x_n3_potentials.log`, 20,000 random profiles per n = 3 core) fail at n = 3 in the
every-form; the table in `attempts/k4-c4x-pareto-potentials.md` has the Pareto-type ones at n = 3. The independent
checker `k4/c4x_check.py` agrees with `k4/c4x.c` on every profile with n = 2 and on 5,100 random profiles with n = 3
(`results/k4_c4x_crosscheck.log`: valid and completable counts, and both forms of eight potentials including the
deficit); the other rows are `k4/c4x.c` alone.

## 3. The extremal principle where it works: k = 3 (Theorem K3)

At k = 3 the principle closes with the plainest potential: **every Pareto-maximal valid pre-allocation is completable.**
This is a second, structural proof of conjecture D for k = 3 cores (already proved and machine-checked by LB⁺,
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
holding B_x (max_h v_x(X_t ∖ h) > v_x(X_x) ≥ v_x(B_x)), so x ∈ E_t and low(x) ⊆ X_t, but z_x ∈ C. Only X_t has more than
two goods and frozen agents hold their bases, so Theorem 1′₄ applies (`SoundCompletion.of_baseNeeds`). ∎

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
lies on another chain. If Q_i and Q_j (i ≠ j) shared a frozen agent, let q be the first agent of Q_i on Q_j; then
x_i ⇝ q ⇝ (end of Q_j) (Q_i up to q, then Q_j from q; simple, by the choice of q) would be a need chain from x_i to the
terminal after t_j, which is not t_i (Lemma E); cutting the cycle there removes the terminals strictly
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
chain ends); fact (iii) with Lemma R (a top-holder's only better base without its top is the pair low(x), which has two
goods, so the rotation stays in 𝒫, and an exposed agent needs exactly one junk good kept out); σ ≥ 0 (a terminal exists
when ω ≥ 1). Lemmas U and C hold for every k. The private-goods rule of cores is used only through L4 (m ≤ 2n, so σ ≥ 0
and a terminal exists when ω ≥ 1), so Theorem K3 proves D for k = 3 *cores* (and with the CORE reduction TARGET); LB⁺
covers every balanced 3-good instance. Without σ ≥ 0 the owner need not be a terminal: for R_0 = {0, 1, 2}, R_1 =
{2, 3, 4} (not a core: m = 5 > 2n) all 52 Pareto-maxima over the 36 ranking profiles have ω ≥ 1 and no terminal (e.g.
bases {0, 1} | {2, 3}, J = {4}); they are completable with owner 0 (reviewer's example on PR #36; confirmed by
`k4/c4x.c -T`).

*Checks against brute force* (`k4/c4x.c -T`, counters of `k4/c4x_run.py`; `results/k4_c4x_k3_lemmas.log`): on every
Pareto-maximum with ω ≥ 1 of every strict profile of every k = 3 core with n ≤ 6 (3,436 cores, 146,640,096 profiles,
1,460,716,706 Pareto-maxima, 25,456,130 of them with ω ≥ 1) Lemmas U, C and E hold (0 violations), every Pareto-maximum
is completable, some terminal is always a valid owner, and the criterion |Z_t| ≤ S − cap(t) agrees with the exact owner
test on all 28,313,452 terminals. "Every terminal is a valid owner" is false (17,056 terminals, all with two exposed
agents whose chains end at one terminal), and the exposure graph does have cycles (at 3,000 maxima, first at n = 6), as
the proof allows: in a cycle two exposed agents share a junk label. Example (`results/k4_c4x_k3_pareto.log`, core 2964):
terminals 3 and 5 expose agents 2 and 4, whose chains end at each other's terminal, and both need the junk good 2; both
terminals are valid (one label, one slot).

## 4. One 4-good agent: the 3-good agents first

Now let the core have exactly one agent w with four goods (a_w > b_w > c_w > d_w, a_w < b_w + c_w + d_w, all
subset sums distinct); the other agents have three goods. By L4 for k = 4 (`k4/SCOUT.md`), m ≤ 2(n − 1) + 3, so
σ ≥ −1. Pareto-maximality is not enough here (§5: a Pareto-maximum that is not completable at n = 3), and neither is
leximax or Σ 2^ℓ; leximin is (evidence), and so is the potential

  **Ψ(P) = (Σ_{i ≠ w} ℓ_i(B_i), ℓ_w(B_w))**, lexicographic: the 3-good agents first, then w.

Evidence: every Ψ-maximum is completable on every strict profile of every core with one 4-good agent and n = 3 (14
cores, 119,232 profiles) or n = 4 (135 cores, 7,247,232 profiles), and on 3,470,000 sampled profiles of the 1,735 cores
with n = 5 (`results/k4_c4x_one.log`); both orders of the two coordinates were tested and
only this one works (w first fails at n = 3). With two 4-good agents the analogue (Σℓ over 3-good agents, then over
4-good agents) fails (§5).

A Ψ-maximum P satisfies:
- **(M1)** no P′ ∈ 𝒫 has v_i(B′_i) ≥ v_i(B_i) for every 3-good agent i with one inequality strict, *whatever w gets*;
- **(M2)** no P′ ∈ 𝒫 differs from P only in w's base and gives w more.

Everything below uses only (M1) and (M2). Lemmas U and C of §3 hold (U: by (M1) for 3-good agents, by (M2) for w; C: a
cycle of frozen agents has at least two agents, so a 3-good one). Facts (i)–(iii) of §3 hold for the 3-good agents.
Moreover:
- **Lemma U₂ (swap).** A free agent with a two-good base values no junk good more than either of its base goods
  (otherwise it swaps them, a gain for it; the released good is in no need set by (V2)). So a free 3-good agent with
  base {b, c} has a ∉ J, and one with base {a, c} has b ∉ J; w's junk goods are worse than both goods of a two-good
  base of w.
- **Lemma R₃** (Lemma R for 3-good agents). If x is a 3-good frozen top-holder and τ the end of a need chain from x,
  low(x) ⊄ J ∪ B_τ. The proof of §3 applies; τ may now be w, and if B_w has two goods they go to the junk (they are not
  in NA by (V2)) while w takes the good it needed.
- The case split below is by w's status: **(A)** w frozen; **(B)** w a terminal (free, N_w ≠ ∅); **(C)** w free with
  N_w = ∅.

### 4.1 Case A: w frozen (proved)

Let B_w = {g}, L = R_w ∖ {g}, and let Two be the set of goods lying in two-good bases of agents other than w. Every
h ∈ L ∩ Two has v_w(h) ≤ v_w(g), since h ∉ NA ⊇ N_w by (V2).

**Lemma R_w (w cannot be rotated).** For every end τ of a need chain from w there is h ∈ L ∩ Two with
v_w(h) > v_w(O*_τ), where O*_τ is the set of the (at most two) best goods of L ∩ (J ∪ B_τ) (∅ if there are none).

*Proof.* Rotate along the chain: every agent after w takes its predecessor's base good (x₁ takes g), w takes O*_τ, and
the rest of B_τ goes to the junk. Everybody but w strictly gains, and x₁ ≠ w is a 3-good agent, so by (M1) the result is
not in 𝒫. Needs other than w's only shrink, O*_τ ⊆ J ∪ B_τ misses NA, and B_τ ∖ O*_τ is not needed; so the only way
to be invalid is a good of R_w ∖ O*_τ worth more than O*_τ that is not a single-good base in the result. g is x₁'s base;
a good of L in a single-good base of P other than B_τ is still one (chain agents pass single goods on); a good of
L ∩ (J ∪ B_τ) outside O*_τ is worth less than each good of O*_τ. What remains is a good of L ∩ Two worth more than
O*_τ. ∎

**Lemma E_w (a frozen w is exposed like a 3-good top-holder).** If w is frozen and a 3-good terminal t exposes w
(W_t = B_t ∪ J threatens w holding B_w), then B_t = {y} with y ∈ L, exactly one good u of L is junk,
v_w(y) + v_w(u) > v_w(g), and no need chain from w ends at t.

*Proof.* A threat by W_t is at most v_w(W_t ∩ L). Take any chain end τ of w and h as in Lemma R_w. Since h ∉ J ∪ B_τ,
L ∩ (J ∪ B_τ) has at most two goods, so it equals O*_τ and v_w(L ∩ J) ≤ v_w(O*_τ) < v_w(h) ≤ v_w(g): the junk alone
threatens nothing. So B_t = {y} with y ∈ L (a 3-good terminal holds at most one good), and t is not a chain end of w
(else W_t ∩ L = O*_τ). h ∉ W_t (it lies in a two-good base of an agent other than t, and is not junk), so
W_t ∩ L ⊆ {y, u} where u is the third good of L; v_w(y) ≤ v_w(g) because t is free (y ∉ NA); so the threat needs u ∈ J
and v_w(y) + v_w(u) > v_w(g). ∎

**Theorem A.** If w is frozen and ω ≥ 1, some 3-good terminal is a valid owner (removal-only, owner's needs from
its base).

*Proof.* The proof of Theorem K3 goes through with the following changes.
- Terminals: all are 3-good (w is frozen), and there is one (|F| ≥ 1, Lemma C).
- Exposed agents w.r.t. a terminal t: 3-good ones are frozen top-holders with one junk label (Lemma E of §3, which
  used only Lemmas U, C, R₃); w, if exposed, has the single label u (Lemma E_w). Removing all labels protects every
  exposed agent: for w, X_t ∩ R_w ⊆ {y} is worth at most v_w(g). So Lemma O holds with Z_t the set of labels.
- The walk with fresh labels is unchanged (w's label, once used, is not fresh, so w is picked at most once).
- Shortening: w may have needs (if g is not a_w), so w can lie inside another chain Q_j. If w = x_i does, let q be the
  first agent of Q_j on Q_i (at the latest w); then x_j ⇝ q ⇝ t_{i+1} (Q_j up to q, then Q_i from q; simple, by the
  choice of q) is a need chain from x_j; it does not end at t_j (no need chain from x_j ends at
  t_j, Lemma E), and cutting the cycle there drops at least one terminal and keeps a subset of the labels. So in a
  shortest cycle no exposed agent lies on another chain, and chains are disjoint as before.
- The cycle move: if w = x_i, w takes {y_{t_i}, u}, worth more than g; its needs are the goods of R_w worth more than
  v_w(y) + v_w(u) > v_w(g), all of them in N_w(g) ⊆ NA, which are single-good bases of the result as well (the move
  passes single goods along chains and only turns the terminals' goods y_t and junk goods into two-good bases). Every
  moved agent gains, so NA′ ⊆ NA, and the result is valid as in §3. It raises every moved 3-good agent (the terminals
  of the cycle are 3-good), contradicting (M1). ∎

### 4.2 Case C with no terminal (proved for connected cores, n ≥ 3)

**Lemma C2.** If ω ≥ 1 and P has no terminal, the core is connected and n ≥ 3, then w is free and a valid owner with
any completion.

*Proof.* No terminal means no frozen agent (Lemma C), so ω = −σ ≥ 1, and σ ≥ −1 forces m = 2n + 1, ω = 1. Counting
incidences, Σ_i |R_i| = 3n + 1 = Σ_g deg(g) ≥ 2m − π = 4n + 2 − π, so the number π of private goods is at least n + 1;
the private-goods rule of cores allows at most one per 3-good agent and two for w, so π = n + 1 and every shared good
has exactly two valuers. With NA = ∅ every agent is free and w is not a terminal. The exposed agents w.r.t.
W_w = B_w ∪ J are 3-good top-holders x (facts (i)–(ii)) with low(x) ⊆ W_w, and low(x) ∩ J = ∅ by Lemma U; so
low(x) = B_w. Then both goods of low(x) are shared by x and w only, x's private good is a_x, and w's two other goods
are private: {x, w} is a connected component, so n = 2. Hence nobody is exposed, and every completion with owner w
satisfies (OC₄). ∎

The two-agent cores (n = 2) are covered by the exhaustive run.

### 4.3 Cases B and C with a terminal: what is proved and the gap

The cases B₁ and C0 are proved below; what remains for a proof of "every Ψ-maximum is completable" with one 4-good agent
is **w free and holding two goods** (cases B₂ and C1; their proved parts and the exact open steps are below). A proof
would give, with Theorem 1′₄, K4.TIE and K4.CORE, TARGET₄ for every instance in which at most one agent values four
goods (the reduction to cores only removes agents and goods, so it never raises an agent's number of relevant goods;
cores with no 4-good agent are Theorem K3's):
- **(B₁)** w is a terminal holding at most one good (proved). Then w has a slot, cannot be exposed (by Lemma U for w
  its goods in W_t = B_t ∪ J lie in B_t, at most one good y, and v_w(y) ≤ v_w(B_w) because t is free, y ∉ N_w),
  and no agent can have low(x) ⊆ B_w; w.r.t. every terminal (3-good or w) the exposed agents are frozen 3-good
  top-holders with one junk label (for the owner w: Lemmas U and R₃, as in Lemma E); every terminal other than t has a
  slot, so |Z_t| ≥ T when t is not valid; and the walk of Theorem K3 over all terminals applies, w taking part as a
  terminal (in the cycle move it gives its good to the exposed agent that wants it and takes the needed good from the
  previous chain). Some terminal is a valid owner.
- **(B₂)** w is a terminal holding two goods. Then w is still not exposed by a 3-good terminal (its base leaves out a
  needed good, which is a frozen agent's base, not in W_t). Two sub-cases:
  - **(B₂′) w is the only terminal** (99,049 of the 106,125 case-B₂ maxima at n = 4). Every need chain ends at w, so no
    agent is exposed w.r.t. W_w with a junk label (such an agent's chains avoid its owner, Lemma E); the only possible
    exposed agents are 3-good top-holders x with low(x) = B_w **(P1)**. If such an x is frozen, its chain ends at w and
    the cycle "x takes B_w, the chain rotates, w takes the good it needed" contradicts (M1). **Open: a free x with
    low(x) = B_w.** Without it, w is a valid owner with any completion.
  - **(B₂″) 3-good terminals exist as well.** The walk of Theorem K3 over all terminals needs, besides excluding (P1),
    **one slot**: w has none, so a 3-good terminal t only gets |Z_t| ≥ S − cap(t) + 1 ≥ T − 1, one less than the walk
    uses. **Open.** (At n = 4: 7,076 such maxima; in 16 of them no 3-good terminal is valid, and w is.)
  Evidence: at n ≤ 4, (P1) occurs at Ψ-maxima only with ω ≤ 0 (1,072 at n = 4), and in case B w itself is always a valid
  owner. That stops at n = 5: in the sample of `results/k4_c4x_one.log` (2,000 profiles per core, 3,470,000 profiles)
  two Ψ-maxima with ω ≥ 1 are in case B₂″ with a frozen (P1) agent whose chains avoid w, and there w is *not* a valid
  owner, while a 3-good terminal is (core 1085 of `results/k4_certs_5_n4_1.json.gz`: w = agent 0 with values
  0:2, 3:6, 4:10, 5:3 holds {3, 5} and needs 4; agent 3 with values 3:2, 5:3, 6:4 holds its top 6, frozen). So in case
  B₂″ the owner cannot always be w, and a proof has to go through the walk.
- **(C1)** w is free with N_w = ∅ and exposed by a 3-good terminal t. Then B_w = {b_w, c_w} with
  a_w < b_w + c_w < a_w + d_w, B_t = {a_w} and d_w ∈ J: by Lemma U the base has two goods, by Lemma U₂ the junk good
  of the complementary pair is worse than both base goods, which leaves only this shape. The walk breaks here (w has no
  need chain). The data says more: at every such maximum *nobody* is exposed w.r.t. W_w = B_w ∪ J, so w is a valid
  owner with any completion (**Lemma C1′, open**). Part of it is proved: an agent x exposed w.r.t. W_w is a 3-good
  top-holder with low(x) ⊆ W_w, so either (t1) x is frozen with low(x) = {y, z}, y ∈ B_w, z ∈ J (Lemmas U, R₃), or
  (t2) low(x) = B_w. Note that z may be d_w. (a) If x is frozen and some need chain from x ends at t, let x take
  low(x), rotate the chain (t takes the good it needed and gives up a_w), and let w take {a_w} ∪ (B_w ∖ {y}) in case t1
  ({a_w, c_w} or {a_w, b_w}: worth more than b_w + c_w, no needs since it contains a_w) and {a_w, d_w} in case t2 (worth
  more than B_w, no needs); what is left of B_w goes to the junk. Everyone moved gains and the result is valid,
  contradicting (M1). (b) In case t1 with a chain from x ending at τ ≠ t, let x take {y, z}, rotate the chain (τ
  releases its base to the junk), and let w keep the other good of B_w, adding d_w if z ≠ d_w: if y = c_w, w's new base
  {b_w, d_w} (or {b_w} when z = d_w) needs at most a_w, still t's base; if y = b_w, z ≠ d_w and b_w < c_w + d_w, the
  base {c_w, d_w} needs at most a_w as well. The result is valid and every agent of x's chain gains, contradicting (M1)
  (w may lose). Open: t1 with y = b_w and chains avoiding t, when b_w > c_w + d_w or z = d_w (then w keeps {c_w}, which
  needs b_w, now in x's two-good base), and t2 when x is free or its chains avoid t. (At the sampled Ψ-maxima E_w = ∅ in
  case C1, so these are gaps of the argument only.) Evidence: 300 case-C1 maxima at n = 4 (none
  at n = 3), E_w = ∅ at all of them; 52 in the n = 5 sample, w valid at all.
- **(C0)** w free, N_w = ∅, not exposed by any 3-good terminal, and a 3-good terminal exists: the walk over the
  3-good terminals applies verbatim (exposed agents are frozen 3-good top-holders; chain ends are 3-good terminals),
  so some 3-good terminal is valid. (Proved.)

Counters (`k4/c4x.c -W` on the Ψ-maxima with ω ≥ 1; `results/k4_c4x_one.log`): n = 3, one 4-good agent: 9,282 maxima (w
a terminal 3,386; w not a terminal (frozen or free) and a 3-good terminal exists 576, of which w frozen 244; no terminal
5,320); n = 4: 200,808 maxima (118,841; 48,811, of which 16,341 with w frozen; 33,156); n = 5, sample of 3,470,000
profiles: 52,440 maxima (35,087; 15,091, of which 3,399 with w frozen; 2,262). Lemma R_w and Lemma E_w: 0 violations;
(P1): 0 at n ≤ 4, 2 at n = 5 (above); case C1: 0 at n = 3, 300 at n = 4 and 52 at n = 5, with nobody exposed w.r.t. W_w
in all of them; w frozen: every 3-good terminal is valid (stronger than Theorem A); no terminal: w valid. Every
Ψ-maximum is completable in all three classes.

### 4.4 A refinement: w holds as little as possible (evidence)

Let **Ψ₂(P) = (Σ_{i ≠ w} ℓ_i(B_i), −|B_w|, ℓ_w(B_w))**. Every Ψ₂-maximum is completable on the same classes (n = 3 and
n = 4 exhaustive, 3,470,000 sampled profiles at n = 5; `results/k4_c4x_one.log`), and at its maxima with ω ≥ 1 the
structure is simpler: neither (P1) nor any agent x with low(x) ⊆ B_w occurs, and **some terminal is always a valid
owner** (w if w is a terminal; otherwise a 3-good terminal, including in case C1; w if there is no terminal). The price:
(M2) becomes "no P′ with the same 3-good bases gives w a base of the same size worth more or a smaller base", so Lemma U
no longer holds for w (an upgrade of w lowers Ψ₂), and the argument of case B that w is not exposed must be redone.
Counters (`k4/c4x.c -W -p "18,22,19"`, `results/k4_c4x_psi2.log`): n = 4: 247,271 maxima with ω ≥ 1, 0 violations of the
rule; w exposed by a 3-good terminal at 15,962 of them, and a 3-good terminal is valid at all of these.

## 5. General k = 4: where the principle stops, and the conjecture

**What carries over to every k.** Lemma U (no upgrade) and Lemma C (need chains) use nothing about three goods, and
hold at every Pareto-maximum; brute force confirms both at k = 4 (0 violations at the Pareto-maxima with ω ≥ 1 of every
profile with n = 2 and of 1,020,000 sampled profiles with n = 3; `k4/c4x.c -T`, `results/k4_c4x_k4_pareto_T.log`).

**What breaks** (each with the smallest example found; `k4/c4x.c -T -x` prints them):
- **(G1) Better bases with three goods.** An agent of type a > b + c has no base of at most two goods worth more than
  its top without the top; its only such base is {b, c, d}. So LB⁺'s rotation (Lemma R) leaves 𝒫, and a frozen
  top-holder of this type can sit with all three lower goods in the junk: a Pareto-maximum that is not completable at
  n = 3, m = 6 (`attempts/k4-c4x-pareto-potentials.md`). Allowing a base of three or four goods for the owner (as LB₄ʳ
  does) makes the potentials worse (`attempts/k4-c4x-variant-spaces.md`).
- **(G2) Two-good bases that are not envy-free.** A free 4-good agent with base {b, c} and a + d > b + c (or its
  other non-envy-free pairs) has no slot and is threatened by a and d in the owner's bundle: the smallest failure of
  "fewest frozen agents first" (n = 2, m = 5, `attempts/k4-c4x-frozen-first.md`).
- **(G3) ω ≥ 1 without frozen agents.** σ = 2n − m can be negative at k = 4, so a large bundle may be needed while no
  agent is frozen and there is no terminal; the owner must then be an agent that needs nothing. At n = 3, 81% of the
  Pareto-maxima with ω ≥ 1 have no terminal (858,982 of 1,060,981 in the sample of `results/k4_c4x_k4_pareto_T.log`).
- **(G4) Two labels.** An exposed 4-good agent can need two goods kept out of the owner's bundle (a flat agent,
  a < c + d), so the one-label counting of Theorem K3 does not apply.
With one 4-good agent, (G1) and (G2) are exactly what Lemma R_w and the cases B₂ and C1 of §4 are about, (G3) is
Lemma C2, and (G4) cannot happen at a Ψ-maximum when w is frozen (Lemma E_w).

**Measured at k = 4** (Pareto-maxima of 20,000 random profiles per n = 3 core, `results/k4_c4x_k4_pareto_T.log`, which
also has the counts for every profile with n = 2): Lemma E fails for 14,317 exposed agents, an exposed agent can reach
its owner by a need chain (12,209, impossible at k = 3 by Lemma R), the exposure graph has cycles at 12,185 maxima, and
4,424 of the 1,020,000 sampled n = 3 profiles have a Pareto-maximum that is not completable.

**Conjecture K4.C4X.MIN (C₄ᵐⁱⁿ).** For every strict profile of every k = 4 core, some valid pre-allocation with the
fewest frozen agents (equivalently, the smallest ω: the smallest large bundle any pre-allocation needs) has deficit ≤ 0:
it has an owner o (or none) and a set C ⊆ J of junk goods that fits into the other agents' slots, with the owner's
needs taken from its bundle, such that B_o ∪ (J ∖ C) threatens no agent holding its base alone. Equivalently, every
maximum of Φ_def = (−|F|, −def) is completable (removal-only). By Theorem 1′₄, K4.TIE and K4.CORE it implies TARGET₄.

A proof along the extremal route would take a Φ_def-maximum with def > 0 and produce a pre-allocation with as few frozen
agents and a smaller deficit: an augmenting step. The data on those steps (`results/k4_c4x_moves.log`): from a
min-frozen pre-allocation with positive deficit, some pre-allocation with as few frozen agents and a smaller deficit
differs from it in the base of one agent in 97% of the cases, and of at most three agents always (137,220 such
pre-allocations in 1,020,000 sampled n = 3 profiles; at n = 2, 93% and at most two). The one-agent steps change a free
agent's base, never a frozen one's, in several ways (`k4/c4x.c -M`, the same sample; a pre-allocation can admit steps of
several kinds): a one-good base gains a good (24,832 pre-allocations admit such a step), a two-good base loses one
(71,665), a two-good base is replaced by another two-good base (130,653, the most common), or the base changes otherwise
(86,347); 3,811 admit no one-agent step. Theorem K3 and §4 are the cases where a Pareto-type potential replaces the
deficit.

## 6. The cores H_t (the obstruction to bounded rotations)

`k4/c4.md` §7 on branch `proof/k4-c4` (PR #33, under review) builds pure cores H_t (n = 4t + 1, m = 10t + 3; t
gadgets of three x's and a y chained through goods g_j) on which LB₄ʳ with index insertion needs ⌈2t/3⌉ nested
rotations, each rotation repairing one gadget. They are the natural test for a *global* extremal choice, which must
"see" every gadget at once. `k4/c4x_ht.py` builds H_t, and `k4/c4x.c` with `-1` (one profile, only valid
pre-allocations generated) or `-1s` (streamed, for large n) tests it (`results/k4_c4x_ht.log`):

| core | n, m | valid pre-allocations | fewest frozen | min-frozen with deficit ≤ 0 | maxima of Σℓ / leximax / leximin | Pareto-maxima |
|---|---|---|---|---|---|---|
| H_1 | 5, 13 | 920 | 0 (574 of them) | 538 of 574 | 2 / 1 / 1, all completable | 6, all completable |
| H_2 | 9, 23 | 181,784 | 0 (68,876) | 63,937 of 68,876 | 2 / 1 / 1, all completable | 30, all completable |
| H_3 | 13, 33 | 35,976,296 | 0 (8,292,664) | yes (the first one examined) | 2 / 1 / 1, all completable | not computed |

So H_t is not hard for the global route: conjecture C₄ᵐⁱⁿ holds on H_1–H_3, and so does "every maximum of Σℓ, leximax,
leximin is completable" (these potentials fail elsewhere, §2). On H_1–H_3 some valid pre-allocation has no frozen agent
at all (computed), while Phase 1 freezes 3t agents, so the per-gadget count of Proposition H there ("slot places minus
goods forced out of the owner's bundle", −2 per untouched gadget) is a count for Phase 1's states: taken globally, the
extremal pre-allocations never have an untouched gadget. The global form of that count is the deficit, and on H_1–H_3
its minimum over the min-frozen pre-allocations is ≤ 0.

## 7. Reproduce

Every log under `results/k4_c4x_*.log` starts with the command(s) that wrote it (`# command:` lines); they are, by log
(times on 4 CPUs):
```
# k4_c4x_n3.log (§2, n <= 3, all profiles; ~40 min)
python3 k4/c4x_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz -R -p "6,17;6,17,0;6,17,3;6,17,8;6;6,0;6,8" -x 3
# k4_c4x_n4_1.log (n = 4, one 4-good agent; ~1 min) and k4_c4x_n4_2.log (two; ~2 h)
python3 k4/c4x_run.py results/k4_certs_4_n4_1.json.gz -R -p "6,17;3;6,3;6,8,3;6;6,8" -x 3
python3 k4/c4x_run.py results/k4_certs_4_n4_2.json.gz -R -p "6,17;3;6,8,3;6" -x 3
# k4_c4x_samples.log (§2, n = 4 with three 4-good agents or pure, n = 5 with one or two: random profiles per core)
python3 k4/c4x_run.py results/k4_certs_4_n4_3.json.gz -R -p "6,17;3;18,19;6" --rand=5000 --seed=11 -x 2
python3 k4/c4x_run.py results/k4_certs_4_pure.json.gz -R -p "6,17;3;18,19;6" --rand=5000 --seed=12 -x 2
python3 k4/c4x_run.py results/k4_certs_5_n4_1.json.gz -R -p "6,17;3;18,19;6" --rand=1000 --seed=13 -x 2
python3 k4/c4x_run.py results/k4_certs_5_n4_2.json.gz -R -p "6,17;3;18,19;6" --rand=100 --seed=14 -x 2
# k4_c4x_random.log (§2, random connected cores, n = 6-8; the log has the full loop over 14 (n, m, #4-good) triples)
python3 k4/c4x_random.py 7 12 3 300 --seed=712
# k4_c4x_n3_pareto.log (Pareto-type potentials, n <= 3, all profiles)
python3 k4/c4x_run.py results/k4_certs_2.json.gz results/k4_certs_3.json.gz -Q -p "0;1;2;3;4;6,3;18,19;20,21" -x 2 --jobs=2
# k4_c4x_n3_pareto_some.log (the some-form of Pareto-maximality on the 18 pure n = 3 cores)
python3 k4/c4x_run.py results/k4_certs_3.json.gz --only=3,11,14,17,23,28,29,32,33,38,41,43,44,45,46,48,49,50 -Q -p "0;3" -x 2 --jobs=4
# k4_c4x_n3_potentials.log (§2, the long list of potentials, n = 3, 20,000 random profiles per core; the log has the list)
python3 k4/c4x_run.py results/k4_certs_3.json.gz -R -p "0;1;2;3;4;5;6;7;8;9;6,0;6,3;..." --rand=20000 --jobs=4
# k4_c4x_k3_pareto.log and k4_c4x_k3_lemmas.log (§3, k = 3, n <= 6, all profiles; the second ~45 min on 2 CPUs)
python3 k4/c4x_run.py results/certs_lb_2_6.json.gz -T -R -p "3;0;6,17;6" -x 5 --jobs=2
python3 k4/c4x_run.py results/certs_lb_2_6.json.gz -T -p "3" -x 3 --jobs=2
# k4_c4x_one.log (§4; the n = 3 line uses the 14 cores of k4_certs_3 with exactly one 4-good agent) and k4_c4x_psi2.log (§4.4)
python3 k4/c4x_run.py results/k4_certs_3.json.gz --only=0,1,4,5,7,9,12,15,18,19,21,24,26,36 -W -p "18,19;18,22,19;3" -x 2
python3 k4/c4x_run.py results/k4_certs_4_n4_1.json.gz -W -p "18,19;18,22,19;3" -x 2
python3 k4/c4x_run.py results/k4_certs_5_n4_1.json.gz -W -p "18,19;18,22,19;3" --rand=2000 --seed=21 -x 2
python3 k4/c4x_run.py results/k4_certs_4_n4_1.json.gz -W -p "18,22,19" --jobs=2
# k4_c4x_k4_pareto_T.log and k4_c4x_moves.log (§5)
python3 k4/c4x_run.py results/k4_certs_2.json.gz -T -p 3 --jobs=1
python3 k4/c4x_run.py results/k4_certs_3.json.gz -T -p 3 --rand=20000 --jobs=1
python3 k4/c4x_run.py results/k4_certs_2.json.gz -M -p 6,17 --jobs=1
python3 k4/c4x_run.py results/k4_certs_3.json.gz -M -p 6,17 --rand=20000 --jobs=1
# k4_c4x_variants.log (attempts/k4-c4x-variant-spaces.md)
python3 k4/c4x_run.py results/k4_certs_2.json.gz -w0 -R -p 6,17 --jobs=1
python3 k4/c4x_run.py results/k4_certs_2.json.gz -E -a -p 6 --jobs=1
python3 k4/c4x_run.py results/k4_certs_3.json.gz -E -a -p 6 --rand=20000 --jobs=2
python3 k4/c4x_run.py results/k4_certs_2.json.gz -3 -R -p "6,17;6" --jobs=4
python3 k4/c4x_run.py results/k4_certs_3.json.gz -3 -R -p "6,17;6" --rand=20000 --jobs=4
python3 k4/c4x_run.py results/k4_certs_3.json.gz --only=0,1,4,5,7,9,12,15,18,19,21,24,26,36 -3 -Q -p "3;0;2" --jobs=4
# k4_c4x_ht.log (§6)
B=$(python3 -c "import sys; sys.path.insert(0, 'k4'); import c4x_run; print(c4x_run.binary())")
for t in 1 2; do python3 k4/c4x_ht.py $t | $B -1s -R -a -p "6;0;2;3;6,0;6,3"; done
for t in 1 2; do python3 k4/c4x_ht.py $t | $B -1 -R -Q -p "6,17;6;0;1;2;3;6,0;6,3;6,8;4"; done
python3 k4/c4x_ht.py 3 | $B -1s -R -p "6;0;2;3;6,0;6,3"
# k4_c4x_crosscheck.log (the independent checker: n = 2 all profiles, ~15 min; n = 3, 100 random profiles per core)
python3 k4/c4x_crosscheck.py results/k4_certs_2.json.gz --all
python3 k4/c4x_crosscheck.py results/k4_certs_3.json.gz --rand=100
# the smallest failures of attempts/k4-c4x-*.md, both implementations
python3 attempts/k4_c4x_attempts.py
```
`k4/c4x_run.py` compiles `k4/c4x.c` into the temporary directory under a name made from a hash of the source (its
`binary()`; `C4X_BIN` overrides the path). Potentials are given as `-p "f,f;f,f"`: `;`-separated lexicographic lists of
feature indices (0 Σℓ, 1 Σ 2^ℓ, 2 leximax, 3 leximin, 4 Σv, 6 −frozen, 8 slots, 17 −deficit (with `-R`), 18/19 Σℓ over
3-good/4-good agents, 22 −|B_w|; the full list is `featname` in `k4/c4x.c`). Other options: `-w0` owner's needs from its
base, `-E` envy-free multi-good bases only, `-3` one base of 3–4 goods, `-Q` Pareto-maxima (every- and some-form),
`-T`/`-T2` exposure counters at Pareto-/first-potential maxima, `-W` the counters of §4, `-M` augmenting-step distances,
`-d` dump every valid pre-allocation, `-1`/`-1s` one profile (stored / streamed), `-x N` examples.
