# Rule F made explicit: a first-agent rule for LB₄ʳ and the A₄⁺ᴺ counting gap

Workstream `proof/k4-rulef` (ledger rows K4.RF.*, open items 18 and 27; rank 2 of `k4/strategy.md`). Builds on
`k4/adaptive.md` (#44: rule F, Proposition H′, Theorem A₄⁺ᴺ), `k4/c4.md`, `k4/c4one.md`, `k4/lb4.md`, `k4/hall.md`
and `proofs/lb_last_step.md`. Notation as there. Nothing here changes K4.D or K4.T.

Tools: `k4/rulef.c` (`k4/adaptive.c` of #44 plus the modes `-A40`, every first agent with its counts and the explicit
rules, and `-A41`, rule RK alone), `k4/rulef_run.py` (driver, one worker), `k4/rulef_model.py` and `k4/rulef_check.py`
(Lemma K written again from the text on PR #33's independent model `k4/c4_verify_H/lb4r.py`, with the completion of
its proof built and checked against `Output` of `lean/EFX/LB4R.lean` and the raw EFX₀ definition).

DRAFT (numbers being filled in).

## 1. Setting

A k = 4 core, a strict profile, LB₄ʳ (`k4/lb4.md` §5; in Lean `EFX.LB4R.Succeeds`). For an agent a, τ_a is the
insertion sequence "a first, then index order" (in Lean the list `[a]`, `lean/EFX/LB4R.lean` choice 2). Rule F
(`k4/adaptive.md` §1) runs LB₄ʳ(τ_a) for a = 0, 1, … and keeps the first that succeeds with the fewest rotations.
Its success with at most one rotation on every profile tested is K4.AD.F/K4.AD.E. A proof needs (strategy §3, rank 2):
1. a first-agent rule that can be stated without running LB₄ʳ;
2. the counting theorem that closes the gap A₄⁺ᴺ leaves (K4.AD.AN, K4.C4.GAP);
3. a rotation statement for what remains.

A state P is valid pre-allocation in the sense of `k4/lb4.md` §1 (bases B_i, needs N_i containing every good of
R_i ∖ B_i worth more than B_i, (V1), (V2)); J is its junk, F its frozen agents (a one-good base in NA), and a free
agent x has cap(x) = 2 − |B_x| slot places. Every state LB₄ʳ reaches is one (`EFX.LB4R.Inv`, K4.C4.FRAME). For an
agent x, a bundle L and a holding H, *threatened(x, L, H)* means max_{h ∈ L} v_x(L ∖ h) > v_x(H); it is monotone
(`k4/c4.md` §1): it stays true when L grows or v_x(H) drops.

## 2. Lemma K: an owner count with kept goods and served agents

**Lemma K.** Let P be a valid pre-allocation and o an agent that is not frozen, such that every base other than B_o
has at most two goods. Put W_o := B_o ∪ J. Fix a set K ⊆ J of goods that will stay in the owner's bundle, and let
- N_o^K := {g ∈ N_o : v_o(g) > v_o(B_o ∪ K)}, NA^K := N_o^K ∪ ⋃_{i ≠ o} N_i;
- F^K := the agents other than o whose base is one good of NA^K (so F^K ⊆ F ∖ {o}), and
  κ^K := Σ_{x ≠ o, x ∉ F^K} (2 − |B_x|), the slot places of the agents other than o once o's needs are N_o^K;
- E := {x ≠ o : threatened(x, W_o, B_x)}, the agents some bundle of the owner could threaten.

A *K-service* chooses for every x ∈ E either
- (s) a *slot good* g_x ∈ J ∖ K, where x ∉ F^K, |B_x| ≤ 1 and not threatened(x, W_o ∖ {g_x}, B_x ∪ {g_x}); or
- (r) a *kept-out set* D_x ⊆ J ∖ K with not threatened(x, W_o ∖ D_x, B_x),

with the slot goods pairwise distinct. Its size is |G ∪ H|, G the slot goods, H the union of the kept-out sets. The
*deficit* of (o, K) is the least size of a K-service minus κ^K (+∞ if E has an agent with no option).

If some K-service has size at most κ^K, then P has a completion X with owner o, the owner's needs taken from its
bundle, that satisfies (OC₄), in which frozen agents hold exactly their bases and only X_o may have more than two
goods. So X is EFX₀ (Theorem 1′₄, K4.LB4.S), and if P is a state of LB₄ʳ(τ) with ω ≥ 1, X is an `Output` and
LB₄ʳ(τ) succeeds.

*Proof.* Let C := G ∪ H, so |C| ≤ κ^K and C ∩ K = ∅.
- *Placing C.* Put each slot good g_x into the slot of x (x ∉ F^K, |B_x| ≤ 1, so x has a place). The agents other
  than o outside F^K have κ^K places, |G| of them used, and |H ∖ G| ≤ κ^K − |G|; put the goods of H ∖ G into
  unused places, one each. Let X_o := B_o ∪ (J ∖ C), and X_x := B_x plus its placed goods for x ≠ o.
- *The owner's needs shrink to N_o^K or less.* X_o ⊇ B_o ∪ K, since K ∩ C = ∅. Let N_o^X := {g ∈ R_o ∖ X_o : v_o(g) >
  v_o(X_o)}. A good of N_o^X lies outside B_o and is worth more than v_o(X_o) ≥ v_o(B_o), so it is in N_o (the
  Definition), and it is worth more than v_o(B_o ∪ K), so it is in N_o^K. Hence NA^X := N_o^X ∪ ⋃_{i ≠ o} N_i ⊆ NA^K
  ⊆ NA, the agents frozen with these needs are among F^K, and (V1), (V2) still hold.
- *X is a completion.* Every good is in one bundle; bases are kept; an agent that received a good is outside F^K,
  hence free under NA^X, with at most 2 − |B_x| goods added; frozen agents (under NA^X) are in F^K and hold exactly
  their base; only X_o may exceed two goods (bases other than B_o have at most two). The owner is not frozen under
  NA^X: it was not frozen, and NA^X ⊆ NA.
- *(OC₄).* Let x ≠ o. If x ∉ E: X_o ⊆ W_o and v_x(X_x) ≥ v_x(B_x), so x is not threatened by X_o (monotonicity).
  If x is served by (s): X_x = B_x ∪ {g_x} and X_o ⊆ W_o ∖ {g_x}. If x is served by (r): X_o ⊆ W_o ∖ D_x and
  X_x ⊇ B_x. Either way monotonicity gives the claim.

Theorem 1′₄ (K4.LB4.S, machine-checked: `EFX.LB4.Valid.sound`, with the owner's needs from its bundle) makes X
EFX₀. For a state of LB₄ʳ with ω ≥ 1, `Output` asks exactly for such a completion with an owner (`EFX.LB4R.Output`:
`Completion` with `ownerNeeds`, `OC`, and an owner when ω ≥ 1). ∎

**Remarks.**
1. *What it contains.* With K = ∅ and every agent of E served by (r) with a set D_x of size ρ_o(x), and the agents
   with dem(x) = 1 served by (s), it is the count of Theorems A₄⁺(o) (K4.C4.AO) and A₄⁺ᴺ (K4.AD.AN), except that
   Lemma 2₄'s sequential choice "the ≻-best junk good not yet placed" is replaced by the *robust* condition (s); the
   (r) sets may overlap (one kept-out good serves several agents, as in LB⁺'s hitting set, `proofs/lb_last_step.md`
   Lemma 1); and the kept set K takes the owner's needs from its bundle into account (the unfreezing clause of
   Lemma H1, `k4/hall.md` §1, there for removal-only completions). On every leaf of the n = 2 classes the A₄⁺ᴺ,
   A₄⁺(o) and intermediate counts being ≤ 0 imply Lemma K's deficit ≤ 0 (334,752 checks, 0 exceptions).
2. *Not exact.* Lemma K is a sufficient condition. LB₄ʳ's owner test is exact for a given C (`k4/lb4.md` Lemma 3₄);
   it allows a slot good that protects only against the final X_o, and the owner's needs from the final bundle.
3. *Where it is used.* Any valid pre-allocation: the state after Phase 1 and upgrades of either policy, and the state
   after rotations (a `RotStep` result passes (V1), (V2) and has at most one base of three or more goods, which must
   then be the owner's).

*Second implementation.* `k4/rulef_model.py` computes the same deficit (without `k4/rulef.c`'s restriction of slot
goods outside R_x to one representative) on PR #33's model, builds the completion of the proof and checks it with
`lb4r.output_check` (the literal `Output` of `lean/EFX/LB4R.lean`) and the raw EFX₀ definition. On every leaf
representative of the n = 2 classes (27,896 profiles, both policies, every first agent): 108,056 completions built,
0 failures; the two implementations agree on the sign of the deficit everywhere (`k4/rulef_check.py`).

## 3. Lemma KR: one rotation, in count form

LB⁺'s Theorem B (`proofs/lb_last_step.md` §5) and its k = 4 forms (B₄, B₄ʷ of `k4/c4.md`, BT1 of `k4/hall_bt.md`)
rotate a frozen agent k along a need chain to the owner and make k the owner. In the language of Lemma K the gain is
explicit: k leaves the set of agents to serve, and the old owner becomes an ordinary agent with a slot.

**Lemma KR.** Let P be a valid pre-allocation whose bases have at most two goods, o an agent that is not frozen with
|B_o| ≤ 1, W := B_o ∪ J, E the agents other than o threatened by W with their base, and σ a ∅-service of E (Lemma K
with K = ∅) of size κ + δ, where κ is the number of slot places of the agents other than o. Let k be a frozen agent,
k = x₀, x₁, …, x_t = o a need chain (distinct agents, t ≥ 1, x₀, …, x_{t−1} frozen, Y_{x_i} ∈ N_{x_{i+1}}), and
O ⊆ R_k ∩ W with v_k(O) > v_k(Y_k). Let P′ be the rotation (`k4/lb4.md` §5; `EFX.LB4R.RotStep`): x_i takes
Y_{x_{i−1}} (1 ≤ i ≤ t), B_o returns to the junk, and k takes the base O (marked, value-based needs). Suppose
- (i) no good of O is used by σ for an agent other than k;
- (ii) o is not frozen in P′ (no agent other than o needs Y_{x_{t−1}} in P′).

Let c_k be the number of goods σ uses for k and for no other agent (c_k = 0 if k ∉ E), and ε := 1 if o is threatened by
W holding Y_{x_{t−1}} and has a slot good g_o ∈ J′ ∖ G that serves it ((s) of Lemma K; G the slot goods of σ), ε := 0
if o is not threatened, and ε := ∞ otherwise. Then P′ is a valid pre-allocation, the rotation is a `RotStep`, and
(P′, owner k, K = ∅) has deficit at most δ − 1 − c_k + ε. In particular, if δ ≤ 1 and either o is not threatened in
P′ or c_k ≥ 1 and ε = 1, LB₄ʳ succeeds after this one rotation, with owner k.

*Proof.* *Validity* (the proof of Lemma R(b) of `k4/c4.md` §4a, which uses nothing about the upgrade policy).
W ∩ NA = ∅: J by (V1), B_o since o is not frozen. Each x_i (i ≥ 1) now holds a pick it ranked above its old one, so
its needs (the goods ranked above its pick) shrink. k's new needs N′_k = {g ∈ R_k ∖ O : v_k(g) > v_k(O)} are worth
more than v_k(O) > v_k(Y_k), so they lie in N_k. Nobody else changes, so NA′ ⊆ NA. Then J′ = W ∖ O ⊆ W misses NA′
((V1)); O ⊆ W misses NA′ ((V2) for k, which `RotChecks` asks of every marked agent); the other two-good bases are
unchanged and miss NA ⊇ NA′. Only O may have three or more goods. The chain is a need chain of P whose last agent o is
not frozen, and O ⊆ R_k ∩ (J ∪ B_o): this is a `RotStep`.

*W does not change.* W′ := O ∪ J′ = O ∪ (W ∖ O) = W (Lemma R(a)).

*Who is threatened* (Lemma R(c)). Let x ≠ k be threatened by W with its base B′_x in P′. If x is not on the chain,
B′_x = B_x, so x ∈ E. If x = x_i with 1 ≤ i < t, v_x(B′_x) > v_x(B_x), so by monotonicity x was threatened by W
with B_x: x ∈ E. So E′ ⊆ (E ∖ {k}) ∪ {o}.

*Capacity.* An agent off the chain that is not frozen in P is not frozen in P′ (same base, NA′ ⊆ NA). In P, k and the
x_i with i < t are frozen (no slot) and o is excluded from κ; in P′, k is excluded and o holds one good and, by (ii),
is not frozen. So κ′ ≥ κ + 1.

*A service of E′.* For x ∈ E′ ∖ {o} ⊆ E ∖ {k} keep σ's choice. It is admissible in P′: by (i) its goods lie in
J ∖ O ⊆ J′; a kept-out set D_x keeps x safe since W is the same and x's base is worth at least as much (monotonicity);
a slot good g_x was chosen for an agent with a slot that is off the chain (chain agents other than o are frozen in P),
whose base and W are unchanged and which is still not frozen. Slot goods stay distinct. If o ∈ E′, add (s) with g_o.
The size is at most |σ| − c_k + ε. So the deficit of (P′, k, ∅) is at most (κ + δ − c_k + ε) − (κ + 1). ∎

At k = 3 in LB⁺'s bad case: o = r, k = k*, O = {b_k*, c_k*}; (i) is the disjointness of the sets π_x; (ii) and "r not
threatened" are Theorem B(e); δ = 1 is "one terminal short". Lemma KR is that argument with any frozen k, any O and the
counting of Lemma K.

## 4. Rule RK: a first-agent rule whose every test is a certificate

For an agent a and a policy pol (need-shrinking or envy-free upgrades), let P_a^pol be the state after Phase 1(τ_a)
and upgrades of pol to their fixpoint (LB₄ʳ's order: smallest-index eligible agent, best eligible good).

**Rule RK.** Scan a = 0, 1, …, n − 1 (index order) three times and take the first a found:
1. (K0) some pol and some owner o, kept set K have Lemma K deficit ≤ 0 at P_a^pol, or ω(P_a^pol) ≤ 0;
2. (K1) some pol and some single rotation of P_a^pol (any frozen k, need chain and base O, as LB₄ʳ's R(1)) reach a
   state with Lemma K deficit ≤ 0 for some owner (or ω ≤ 0 and no base of three goods);
3. (C40) the envy-free run of τ_a satisfies the hypothesis of Corollary C₄⁰ (no 4-good agent exposed w.r.t. r, and in
   LB⁺'s bad case r is not a 4-good agent exposed after LB⁺'s rotation);

and a = 0 if none applies (the *open* class). Run LB₄ʳ(τ_a).

RK never runs LB₄ʳ's owner search: it runs Phase 1, the two upgrade fixpoints, the rotations of R(1), and evaluates
Lemma K's count. Each class carries its own proof that LB₄ʳ(τ_a) succeeds: K0 with no rotation (Lemma K), K1 with at
most one (Lemma K at the rotated state, which is a valid pre-allocation reached by a `RotStep`), C40 with at most one
(Corollary C₄⁰, K4.C4.AB.L, machine-checked). So **rule RK is correct exactly when the open class is empty**, which is
the existence statement

**Lemma M (missing).** For every strict profile of every k = 4 core some first agent a is in class K0, K1 or C40.

What a proof of rule F still needs is Lemma M; §5 gives the data, §6 what is known about a proof.
