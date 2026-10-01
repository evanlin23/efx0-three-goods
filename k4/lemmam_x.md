# Lemma M by exchange between first agents

Workstream `proof/k4-lemmam-x` (ledger rows K4.LMX.*; target K4.RF.M, `k4/rulef.md` §6 Step 3: items M1–M3 and
(G2)). Builds on `k4/rulef.md` (PR #72, branch `proof/k4-rulef` at aebd620: Lemmas K, K′, KR, S, rule RK, Lemma M),
`k4/c4.md` (Lemma E, Theorems A₄, B₄, Lemma R; row K4.C4.AB.L), `k4/c4one.md` §6 (Lemmas Ω, Ψ; rows K4.C4.OM,
K4.C4.PSI) and `k4/lb4.md`. Notation as there. Nothing here changes K4.D, K4.T or K4.RF.M's status.

Tools: `k4/lemmam_x.c` (`k4/rulef.c` of #72 verbatim plus a mode `-A43`: the class of every first agent, and for every
bad first agent the roles of the other agents in its run and the candidates a′ of §2), `k4/lemmam_x_run.py` (driver,
one worker, resumable), `k4/lemmam_x_check.py` (second implementation on PR #33's model `k4/c4_verify_H/lb4r.py` with
#72's `k4/rulef_model.py`, without code from `k4/lemmam_x.c`).

**Status.** STATUS_PLACEHOLDER

## 1. Setting

A k = 4 core with a strict profile. For an agent a, τ_a is "a first, then index order" (rule F's sequences,
`k4/rulef.md` §1), Phase 1 uses LB's P-step key, and P_a^ns, P_a^ef are the states after need-shrinking and after
envy-free upgrades to their fixpoints (LB₄ʳ's order). As in `k4/rulef.md` §4, a is in **K0** if some policy, owner o
and kept set K give Lemma K deficit ≤ 0 at P_a^pol, or ω(P_a^pol) ≤ 0; in **K1** if some single rotation of LB₄ʳ (every
frozen k, need chain and base O) from P_a^pol reaches a state with Lemma K deficit ≤ 0 for some owner (or ω ≤ 0 and no
base of three goods); pol ranges over need-shrinking and envy-free upgrades (RK₃ adds no upgrades, which only enlarges
the classes). Lemma K is taken with the kept-out sets of `k4/rulef.md` §2 Remark 4 (`-Y1`), the lemma as stated
(K4.RF.K). Call a **good** if a ∈ K0 ∪ K1 and **bad** otherwise. Then

> **Lemma M** (K4.RF.M, open). Every strict profile of every k = 4 core has a good first agent.

The exchange form asked for (`k4/rulef.md` §6 Step 3): *if a is bad, a specific agent a′ = c(a), read off a's run, is
good.* Any such map c proves Lemma M (take any a; if it is bad, c(a) is good). A weaker form also suffices: *if a is
bad, c(a) is good or c(a) is "smaller" than a in a fixed well-founded order* (then a minimal agent is good); §2 tests
both (the second as "iterated": follow c from a until a good agent, a repeat, or n steps).

For a bad a write P := P_a^ef. Then (Lemma 1 below) ω(P) ≥ 1, and with the notation of `k4/c4.md` §1–§2: r is the
last-processed agent that is not upgraded (not frozen, by (A1)), W := B_r ∪ J, an agent x ∉ U, x ≠ r, is *exposed*
(x ∈ E) if it is threatened by W with its base, F, T, U are the frozen, terminal and upgraded agents, B* is r's block
and k* its leader. A *need chain* from a frozen x is x = x₀ → x₁ → … → x_t with x_{i+1} ∉ U needing Y_{x_i}, x₀, …,
x_{t−1} ∈ F and x_t ∈ T; it lies in x's block and increases in processing order ((A4), (B2)); its last agent is an
*end* of x.

## 2. Which a′ works: the data

PLACEHOLDER_DATA

## 3. What the run of a bad first agent looks like

**Lemma 1.** Let a be bad and P = P_a^ef. Then
- (a) ω(P) ≥ 1, and r is a terminal with |B_r| ≤ 1;
- (b) some exposed agent is frozen (E ∩ F ≠ ∅); so every bad run has an exposed frozen agent, and the ends of its
  need chains, the "needers at the end of a need chain" of §2, exist;
- (c) some 4-good agent is exposed, or the run is in (G2): LB⁺'s bad case of Theorem A₄ (k* ∈ E ∩ F, k* ≠ r, every
  need chain from k* ends at r, the sets π_x = {b_x, c_x} ∩ J of the exposed agents pairwise disjoint), r has four
  goods, and r is exposed after LB⁺'s rotation (k* takes O := {b_k*, c_k*}) along every need chain k* → r.

*Proof.* (a) ω(P) ≤ 0 puts a in K0. r is not frozen and holds at most its pick by (A1) of `k4/c4.md` §1 (K4.C4.AB.L).

(b) Under envy-free upgrades an upgraded agent holds an envy-free base, so it is never threatened (`k4/c4.md` §1), and
an agent without a pick is not threatened (Lemma E). So if E ∩ F = ∅, every agent of E is free in the sense of Lemma S
(`k4/rulef.md` §6, K4.RF.S: unmarked, not frozen, a one-good base), and Lemma S with o = r and the empty service σ of
the agents of E that are not free gives deficit(r, ∅) ≤ |σ| − κ₀ = −κ₀ ≤ 0: a ∈ K0.

(c) Suppose no 4-good agent is exposed. Outside LB⁺'s bad case Theorem A₄'s proof (K4.C4.AB.L) gives H ⊆ J with
|H| ≤ S − cap(r) meeting every π_x, x ∈ E, where every x ∈ E is a 3-good block leader holding a_x with
R_x ∩ W = {b_x, c_x} (Lemma E(i)). Serve x by the kept-out set {h}, h ∈ H ∩ π_x: W ∖ {h} meets R_x in one good, worth
less than a_x, so x is not threatened. This is a ∅-service of Lemma K for owner r of size ≤ |H| ≤ S − cap(r) = κ^∅
(r is not frozen, so N_r^∅ = N_r and κ^∅ counts the slot places of the agents other than r): a ∈ K0. In the bad case,
if r is not a 4-good agent exposed after LB⁺'s rotation along some chain k* → r, Theorem B₄ (K4.C4.AB.L) makes the
rotation a valid `RotStep` with ω′ ≤ 0, or gives the hitting set H′ of B₄(c), which serves the agents exposed w.r.t.
the owner k* by singletons in the same way, with |H′| ≤ S′ = κ′ (k* has no slot): a ∈ K1, since class K1 tries every
single rotation. So a bad run with no exposed 4-good agent is in (G2). ∎

(c) is the remark "C40 ⊆ K0 ∪ K1" of `k4/rulef.md` §4 and §6 Step 1 (made by the PR #72 referee), stated for one run.
So M3 of `k4/rulef.md` §6 reduces to (G2), which §4 treats.

Where the deficit of M1 sits is a Hall condition. For x ∈ X := E ∩ F let ρ(x) be the least size of a kept-out set
D ⊆ J serving x (x not threatened by W ∖ D with its base; ∞ if none), and let D(x) be the set of ends of need chains
from x that are neither r nor exposed.

**Lemma 3 (the overloaded ends).** Let a be bad and P = P_a^ef. Then some nonempty X′ ⊆ X has
Σ_{x ∈ X′} ρ(x) > |⋃_{x ∈ X′} D(x)|.

*Proof.* Otherwise, by Hall's theorem (each x taken ρ(x) times), there are pairwise disjoint sets T_x ⊆ D(x) with
|T_x| = ρ(x). Serve each x ∈ X by a least kept-out set D_x; these serve all agents of E that are not free in the sense
of Lemma S (upgraded agents and agents without a pick are not exposed), with |σ| ≤ Σ_x ρ(x). By Lemma S (o = r, not
frozen, |B_r| ≤ 1), σ extends to a ∅-service of E at most one good larger per free agent of E, placed in that agent's
own slot place. Lemma K's κ for owner r counts at least one slot place for every free agent of E and, separately, one
for every agent of ⋃ T_x: these are ends of need chains, so terminals (unmarked, not frozen, other than r), and not
exposed. So the deficit of (r, ∅) is at most Σ ρ(x) − |⋃ T_x| = 0, and a ∈ K0. ∎

At k = 3 every x ∈ X is a 3-good block leader with ρ(x) = 1 and an end in its own block, and the ends of distinct
leaders are distinct; X′ can only be {k*} with D(k*) = ∅ (all ends equal to r): LB⁺'s bad case. At k = 4 the
violating sets of the data are of three kinds: an end shared by several exposed frozen agents of one block (the gadgets
of H_t: X′ = {x_{j,1}, x_{j,2}, x_{j,3}}, D(X′) = {y_j}); all ends equal to r (every bad run with n ≤ 4); and an end
that is itself exposed (`k4/c4.md` §6.1 item 3). The candidates a′ of §2 are read off these ends.

## 4. (G2)

(G2) of `k4/c4.md` §6: no 4-good agent is exposed, LB⁺'s bad case holds (conditions (1)–(3) of Theorem A₄), r has four
goods, and after LB⁺'s rotation along any need chain k* → r (each chain agent takes its predecessor's pick, k* takes
O := {b_k*, c_k*} ⊆ W, Y_r returns to the junk) r is exposed w.r.t. the new owner k*. Theorem B₄ (K4.C4.AB.L) then
gives nothing. Lemma 2 shows that for a bad first agent this can only happen in a rigid shape: k*'s two lower goods are
goods of r. Otherwise one rotation (LB⁺'s, along a longest chain) is certified by Lemma K, with r served by a slot good
of its own; this is the step Theorem B₄ misses, since it serves exposed agents by kept-out goods only.

**Lemma 2.** Let a be bad, P = P_a^ef in (G2), and k* = x₀ → x₁ → … → x_t = r a longest need chain from k*
(t ≥ 1); put Y′ := Y_{x_{t−1}}, O := {b_k*, c_k*}, L := R_r ∩ W, and let P′ be LB⁺'s rotation along this chain. Then
- (a) in P no agent other than r needs Y′, and in P′ the agent r is a terminal (unmarked, not frozen, base {Y′}) and
  exposed;
- (b) O ⊆ R_r; precisely, either Y′ = b_r and O = {c_r, d_r}, or Y′ = a_r, O ⊆ {b_r, c_r, d_r} and L ⊆ O ∪ {d_r}.

*Proof.* (a) Let z ≠ r need Y′ in P. Upgraded agents need nothing under envy-free upgrades (`k4/c4.md` §1), so
z ∉ U, and by (B2) z is processed after x_{t−1}, in the same block; so z is none of x₀, …, x_{t−1}. If z ∈ T, then
x₀ → … → x_{t−1} → z is a need chain from k* that ends at z ≠ r, against (2) of the bad case. If z ∈ F, follow needs
from z: its pick is in NA, so some agent outside U needs it and is processed after z (B2); repeat while the agent
reached is frozen. Processing positions increase, so this stops at a terminal, and x₀ → … → x_{t−1} → z → … is a need
chain from k* (distinct agents, increasing positions) of length more than t; by (2) it ends at r, against the choice
of a longest chain. So only r needs Y′ in P.
In P′ (Lemma R, K4.C4.AB.L: NA′ ⊆ NA, and chain agents get the needs of their new picks): an agent off the chain needs
what it needed in P, hence not Y′. A chain agent x_i, 1 ≤ i ≤ t − 2, was processed before x_{t−1}, when Y′ was still
there, so it ranks Y′ below its old pick Y_{x_i} (if it values Y′ at all), hence below its new pick Y_{x_{i−1}}, which
it needed. x_{t−1} (if t ≥ 2) now holds Y_{x_{t−2}}, which it ranks above Y′ = its old pick. k* holds O, an envy-free
pair of a 3-good balanced agent, and needs nothing. So nobody needs Y′ in P′: r, which holds it, is not frozen, and it
is unmarked (`RotStep` marks only k*). It is exposed in P′ because P is in (G2).

(b) Suppose (b) fails; we certify P′ with owner k* and K = ∅ (Lemma K), so that a ∈ K1, a contradiction. P′ is a
valid pre-allocation reached by one `RotStep` (Theorem B₄(a)), every base but O has at most two goods, and k* is not
frozen. W′ := O ∪ J′ = W (Lemma R(a)). Let E′ be the agents other than k* threatened by W with their base in P′.
Upgraded agents are not threatened, and by Lemma R(c) (no 4-good agent is exposed in P, so no chain agent is exposed in
P′) E′ ⊆ (E ∖ {k*}) ∪ {r}.
- *x ∈ E′ ∖ {r}.* By (1) of the bad case x ∉ B*, so x is off the chain (which lies in B*) and keeps its base; by
  Lemma E(i) x is a 3-good leader holding a_x with R_x ∩ W = {b_x, c_x}. If {b_x, c_x} ⊆ O, then {b_x, c_x} = O and
  π_x = O ∩ J = π_k*, which is not empty (at most one good of O is Y_r), against (3). So some h_x ∈ {b_x, c_x} lies in
  W ∖ O = J′; the kept-out set {h_x} serves x (W ∖ {h_x} meets R_x in one good, worth less than a_x).
- *r, if r ∈ E′.* NA′ ⊆ NA and W ∩ NA = ∅, so the goods of L are ranked below Y′ (the goods above it are r's needs);
  r is threatened, so |L| ≥ 2 and Y′ ∈ {a_r, b_r}. We find a slot good g ∈ L ∩ J′ with r not threatened by W ∖ {g}
  when it holds {Y′, g} ((s) of Lemma K; r is a terminal of P′ with one slot place by (a)):
  - Y′ = b_r: L = {c_r, d_r}; as (b) fails, one of them is not in O, so it is in J′; take it as g. W ∖ {g} meets R_r in
    one good, worth less than b_r.
  - Y′ = a_r, b_r ∈ L ∩ J′: g = b_r; W ∖ {g} meets R_r in at most {c_r, d_r}, and v(c) + v(d) < v(a) + v(b).
  - Y′ = a_r, b_r ∉ L ∩ J′, c_r ∈ L ∩ J′: g = c_r; W ∖ {g} meets R_r in at most {b_r, d_r}, and v(b) + v(d) <
    v(a) + v(c).
  - Y′ = a_r, b_r, c_r ∉ L ∩ J′: then L ⊆ O ∪ {d_r}; as (b) fails, O ⊄ R_r, so |L ∩ O| ≤ 1, and |L| ≥ 2 gives
    d_r ∈ L ∩ J′ with L ∖ {d_r} a single good; g = d_r leaves one good, worth less than a_r.
- *Count.* The service has size at most |E ∖ B*| + 1 (one kept-out good per x ∈ E′ ∖ {r} ⊆ E ∖ B*, and g). Lemma K's
  κ′ counts the slot places of the agents other than k* that are not frozen in P′. Among them: r (one place, by (a));
  and for each x ∈ E ∖ B* the end τ(x) of a need chain from x (x itself if x ∈ T), a terminal of x's block (A4) with
  at least one place. These ends are distinct (one exposed 3-good agent per block, Lemma E(i)), lie outside B* (so
  they are not r and not on the chain, and keep their bases), and stay non-frozen since NA′ ⊆ NA. So
  κ′ ≥ |E ∖ B*| + 1, and the deficit of (P′, k*, ∅) is at most 0 (or ω′ ≤ 0). Class K1 tries every single rotation of
  LB₄ʳ, this one among them, so a ∈ K1. ∎

So for a bad first agent, (G2) is the configuration "k* is a 3-good leader whose two lower goods are goods of the
4-good r, which moves up to its top or to its b along the chain and is then threatened by k*'s new base O itself" (the
mechanism of `k4/c4.md` §6.1 item 4 and `attempts/k4-c4-lbplus-rotation.md`, here shown to be the only one). In the
case Y′ = b_r it is completely rigid: R_r = {a_r, Y′, b_k*, c_k*}, r's old pick is one of b_k*, c_k*, and a_r is held
by a frozen agent (r needs it). No rotation of the same run repairs it on the data: (G2) occurs in bad runs (§2), and
there the exchange of §2 repairs it; on every one of them, a′ = r (the needer at the end of the chain) is good.
What is open for (G2) is the exchange itself (§5).

## 5. The exchange: mechanism, Ω and Ψ, and what remains

### 5.1 A standalone step: the first block decides

**Lemma 4.** Let a, a′ be agents, β and β′ the first blocks of the runs of τ_a and τ_{a′}. If β and β′ have the same
agents and their agents pick the same set of goods (in any assignment), then after the first block the two runs
process the same agents in the same order with the same picks. Their Phase 1 states differ only in which agent of β
holds which good of the common set, and they have the same junk J₀.

*Proof.* When the first block ends, both runs have the same set G of remaining goods and the same unprocessed agents.
From there Phase 1 is a function of (G, unprocessed agents): a P-step takes the agent of least LB key (rank of its
favourite good of G, number of its goods in G, index), an insertion step the first unprocessed agent in index order
(τ_a and τ_{a′} have length one), and every agent takes its favourite good of G. By induction the two runs agree. ∎

(The upgrades can still differ outside β, since NA changes with the picks of β.) Lemma 4 reduces an exchange whose
first block keeps its agents and goods to a statement about that block. On the data this is the common case at
n ≤ 4, where the bad runs are single blocks and the exchange permutes the picks (§5.2); on H_t it is not (the exchange
agent lies in another gadget, and its run has a different block structure).

PLACEHOLDER_EXCHANGE

## 6. No fixed rotation bound for a single chosen first agent

Proposition HH of `k4/lemmam_bt.md` §3 (PR #83, a written proof under review) refutes Lemma M on HH₃: HH_t is two
copies A, B of H_t with ℓ_B's good u identified with ℓ_A's u (n = 8t + 2, m = 20t + 5, every agent 4-good, none
big-top), and for t ≥ 3 no first agent a makes LB₄ʳ(τ_a) succeed with at most one rotation. The same count, with q
rotations in place of one, bounds the rotations of every first agent.

**Proposition R.** For every d ≥ 0 and every t with 2t − 2 > 3d, on HH_t no first agent a makes LB₄ʳ(τ_a) succeed
with at most d rotations (under each upgrade policy, every owner or none, the owner's needs from its base or its
bundle, chains ending at any agent that is not frozen). So no fixed bound on the rotations makes a rule that chooses
only the first agent work: d = 1 fails on HH₃, d = 2 on HH₅, d = 3 on HH₆, and so on.

*Proof.* Fix a and let D be the copy containing a, C the other one. We use from `k4/lemmam_bt.md` §1, §3 (PR #83):
Lemma P (protecting goods: if forced agents have protecting sets Π(f) disjoint except for c goods each in two of them,
and own-slot sets Σ(f) disjoint from all Π's, then their number is at most the slot places of the free agents other
than the owner plus c), the forced agents (F1) (an x holding exactly its a, its b, c junk) and (F2) (an ℓ holding g₁,
u and u′ junk), with c = 1 (u is in Π(ℓ_A) ∩ Π(ℓ_B)); and Lemmas 1, 2 there (Phase 1 and upgrades of HH_t: C runs
exactly as H_t's index run and admits no upgrade, so all its gadgets are *untouched* (α): y_j on e_j, each x_{j,i} on
{a_{j,i}}, frozen; in D, gadgets before a's gadget j are (α), gadget j is (β1) or (β2), later ones (β2)).

*Needs stay in gadgets, after any number of rotations.* By induction on the rotations, as in Proposition H's proof
(`k4/c4.md` §7): every need of an agent is an a of its own gadget and each ℓ keeps g₁ and needs nothing; a chain
agent takes a good it needed, an a of its gadget; a rotated head takes O ⊆ R_k ∩ (J ∪ B_end), and validity keeps its
value-based needs among the a's. The copies share only u, which only the ℓ's value. So every need chain, hence every
RotStep, lies in one gadget of one copy.

*Balance per gadget.* For a completion X with owner o, the balance of a group of agents is (slot places of its free
agents other than o) − (its forced agents). Then: ℓ_A, ℓ_B at most 0 each; an untouched (α) gadget exactly −2 (y one
place, three frozen forced x's); and **every gadget of any valid state in which its agents' needs are a's of the
gadget has balance at most +1.** Indeed only y and an x whose base is a single good other than its a can contribute
+1 (an x on {a} is frozen or forced: at most 0; a base of two or more goods, or the owner, gives 0). Such an x values
its a (8) above its base (at most 6), so it needs a, which must then be a one-good base, held by y (frozen, 0); y
holds one good, so at most one x is of this kind, and then y gives 0. If that x is the owner with its needs from its
bundle, it gives 0 and y at most +1. So the gadget gives at most +1. In D the Phase 1 balances are at most −2 for
gadgets before j, +1 for j and 0 for later ones (Lemma 2 of #83 and the count there, every policy), so D starts at
most at 1.

*Count.* Let q_C, q_D ≤ d be the rotations in C and in D. At most q_C gadgets of C and q_D of D are touched. An
untouched gadget keeps its Phase 1 balance (−2 in C; at most −2, +1, 0 in D as above), a touched one gives at most +1,
so each touched gadget raises its copy's bound by at most 3. So the total balance is at most
(−2t + 3q_C) + (1 + 3q_D) + 0 ≤ −2t + 1 + 3d < −1 when 2t − 2 > 3d. Lemma P with c = 1 needs at least −1. An output
of LB₄ʳ is such a completion with an owner (ω = |NA| − σ ≥ −σ = 4t + 1 ≥ 1, and a base of three or more goods makes
its agent the owner), so there is none. ∎

The bound is a count, so it is the same for Lemma K's classes (whose certificates are outputs): on HH_t with
2t − 2 > 3d no first agent is certified with d rotations. On HH₃ (d = 1) the classes are those of PR #83 (every first
agent in neither K0 nor K1, `k4/rulef.c` and `k4/lemmam_bt.py`) and of `k4/lemmam_x.c -A43` here (§2).
Larger d is a statement about HH₅ (n = 42) and beyond, where the count is the evidence; a direct search with two nested
rotations on HH₃ already exceeds the ~20 minutes allowed per run here.

## 7. The repaired target: the insertion agent chosen at every insertion step

HH_t needs a chosen insertion step in each copy (x_{1,2} in each, then index order: no rotation, `k4/lemmam_bt.md` §3),
and Proposition R shows that no fixed number of rotations replaces those choices. The natural repair keeps the
rotations per block bounded and chooses every insertion step.

A *run* is now Phase 1 with any insertion sequence τ (the agent inserted at each insertion step chosen freely; P-steps
by LB's key, as in LB₄ʳ and Lean's `phase1State`). Its blocks β₁, …, β_k: each starts at an insertion step and is
closed under P-steps; agents of later blocks value no good picked in an earlier one (B1), and a need chain stays in
its block (A4). So the blocks are the natural unit for a local statement. In LB⁺ (k = 3) every block but the last is
automatically fine (Theorem A: each exposed leader has a terminal of its own block), and only the last can be one
slot short (the bad case, one rotation). At k = 4 a block can be short, and the insertion choice is what fixes it.

### 7.1 The block count, and why it certifies

Let a run have just closed a block β, and let G be the set of goods not yet picked. Take the state *without upgrades*
(each agent holds its pick; RK₃'s third policy). The following depend on β and G only:
- *frozen:* an agent of β whose pick is needed by another agent of β (by (B2) nobody outside β ever needs it);
- X_β: the frozen agents of β threatened by W_β with their pick, where W_β := G, and for the last block (when no agent
  is left) W_β := G ∪ {Y_r}, r its last-processed agent (the owner);
- ρ_β(x) for x ∈ X_β: the least s such that, for every good h ∈ G ∩ R_x (the owner's future pick, not known yet, cannot
  be kept out; in the last block no h), some D ⊆ (G ∩ R_x) ∖ {h} with |D| = s leaves x not threatened by W_β ∖ D;
- D_β(x): the ends of need chains from x inside β that are not threatened by W_β with their pick, other than r;
- the **block count** δ(β) := max(0, max over nonempty X′ ⊆ X_β of Σ_{x∈X′} ρ_β(x) − |⋃_{x∈X′} D_β(x)|).

**Lemma 5 (block counts certify).** If every block of a run has block count 0, its Phase 1 state (no upgrades) has
Lemma K deficit at most 0 with owner r and K = ∅. So LB₄ʳ(τ) succeeds without rotation (no-upgrade policy).

*Proof.* Without upgrades r, the last-processed agent, is not frozen ((A1): an agent needing Y_r would come after r).
Let W := J ∪ {Y_r} be the final W, E the exposed agents and X = E ∩ F. For x in a block β_i other than the last, W ⊆ G_i
(the goods unpicked when β_i closed; r's pick is among them), and for the last block W = W_β. Frozen status is final:
by (B2) the needs of every agent lie in its own block. So, by monotonicity of threats, every x ∈ X lies in some X_{β_i},
and every end in D_{β_i}(x) is a terminal of the final state, other than r and not exposed.
For x ∈ X ∩ β_i (not the last block) take h := Y_r if Y_r ∈ R_x (else any h), and D ⊆ (G_i ∩ R_x) ∖ {h} of size
ρ_{β_i}(x) as in the definition; then D_x := D ∩ J is a kept-out set of Lemma K: W ∖ D_x ⊆ (G_i ∖ D) ∪ {Y_r} = G_i ∖ D
(Y_r ∉ D, and Y_r ∈ G_i), so x is not threatened. In the last block D ⊆ G = J directly. So the agents of X are served
with at most Σ_{x∈X} ρ(x) goods. Hall's condition holds in every block (count 0), the sets D_{β_i}(x) of different
blocks are disjoint (ends lie in their block), so it holds for X: there are disjoint T_x ⊆ D(x) with |T_x| = ρ(x).
Each agent of ⋃ T_x is a terminal other than r with at least one slot place, not exposed. The free exposed agents
cost at most their own places (Lemma S, owner r with |B_r| ≤ 1). So the deficit of (r, ∅) is at most
Σ ρ(x) − |⋃ T_x| = 0 (Lemma 3's proof). ∎

At k = 3 every block but the last has count 0 whatever its leader: a non-leader has lost a good, so at most one of its
goods below its pick is unpicked and it is not threatened by G; the leader x, if frozen and exposed, has
ρ = 1 (if h is b_x keep c_x out, and conversely) and an end in its block that is not r and not exposed. The last block
has count at most 1: LB⁺'s bad case. So Lemma 5 contains LB⁺'s Theorem A, block by block.

### 7.2 Adaptive Lemma M

**Conjecture M_ad (local form).** For every strict profile of every k = 4 core, a run can be built block by block so
that every block other than the last has block count 0: at each insertion step some unprocessed agent starts a block
of count 0. The last block then has count 0 (Lemma 5: no rotation) or count 1, repaired by one rotation (Lemma KR).

**Conjecture M_ad (global form).** For every strict profile of every k = 4 core some insertion sequence τ and some
upgrade policy reach, with at most one rotation, a state of Lemma K deficit ≤ 0. In Lean: some τ with
`EFX.LB4R.SucceedsR 1 v agents goods τ` (§7.4).

The local form is what an exchange lemma can prove: at an insertion step where the agent of least index starts a block
of positive count, show that another agent, read off that block (an overloaded end, Lemma 3), starts a block of count
0. Ω and Ψ (`k4/c4one.md` §6) are exactly moves of this kind — they change the agent inserted at the start of one
block and keep the prefix — but their new block has P-steps in their order, not LB's key's, and they bound ω, not the
block count, so they do not give the step as they stand.

### 7.3 Data (EVIDENCE)

`k4/lemmam_x.c -A44` builds the run greedily: at each insertion step it simulates the block of every unprocessed
agent, takes the least block count (ties: least index), and at the end reports the least number d ≤ cap of nested
rotations after which Lemma K certifies the run under some policy (`k4/lemmam_x_adp.py`).

PLACEHOLDER_ADPDATA

### 7.4 Lean

`lean/EFX/LB4R.lean` and `lean/EFX/RuleF.lean` (PR #72) already contain what M_ad needs: `phase1State v agents goods τ`
takes any insertion sequence (each entry picks the inserted agent among the unprocessed ones), and
`SucceedsR d v agents goods τ` is "LB₄ʳ(τ) succeeds with at most d rotations". The global form is

    def TheoremAdaptive (A G) : Prop := ∀ agents goods v, agents.Nodup → goods.Nodup → IsCore4 v agents goods →
      Strict v agents goods → ∃ τ : List Nat, SucceedsR 1 v agents goods τ

(and `AdaptiveConn` with `Connected` and a 4-good agent, as `RuleFConn`). `TheoremRuleF` is its special case τ = [a].
It implies `TheoremC4exists` (and `C4existsConn`, hence TARGET₄) by the existing proofs, word for word:
`sound_of_succeeds hag hgd (succeeds_of_succeedsR (by omega) h)` for the τ the hypothesis provides, as in
`C4exists_of_ruleF`. A version with one rotation per block needs `SucceedsR d` for unbounded d; `sound_of_succeeds`
generalizes at once (`rotReach_inv` holds for every d), but `succeeds_of_succeedsR` does not (it needs d ≤ 3), so that
version would need a three-line `sound_of_succeedsR`. Lemma K's certificates are `Output`s (`k4/rulef.md` §7, step 1),
so Lemma 5 and the data are statements about `SucceedsR 0` and `SucceedsR 1`.

## 8. Reproduce

PLACEHOLDER_REPRO
