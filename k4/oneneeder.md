# The one-needer regime at the T3 stage (f = 1)

Workstream `proof/k4-oneneeder` (PR #84). Ledger rows K4.ON.* (CONJECTURE / EVIDENCE until refereed). Task:
`k4/dl13.md` §6 item 3 (on branch `proof/k4-dl13`, PR #75): at a T3-stage state whose frozen good has exactly one needer
z, show that the frozen agent x is big-top and that its lower goods are within reach of one helper, so that Corollary
8.2 of `k4/dl13.md` §2.1 (the Lemma 7 swap) applies. Builds on `k4/dl2.md` §4 (Lemmas 1, 1′, 2, 3, 6, 7; PROVED rows
K4.DL2.MOVES, K4.DL2.DEF), `k4/dl13.md` §1–§3 (Lemmas 8, 10, Corollary 8.2, Proposition T; refereed in the PR #75
review), `k4/hall.md` §1 (Lemma H1, K4.HALL.COVER) and `k4/c4min_reduce.md` §1–§2 (Lemmas K, T and Theorem Z′,
K4.C4MIN.RED.Z, PROVED). Nothing here changes K4.D or K4.T.

The claims are about **f = 1**, where the frozen-chain swap (T3⁺) of the coordinator's new relation R_C is a plain (T3)
swap. (DL_RT4 and the key-graph DL with single (T3)/(T4) edges are refuted at n = 5, f = 3 by compute/k4-rt4-n5b/-n5c;
the coordinator changes those ledger rows.)

**Status: the regime is not closed in general; it is closed at n = 3 by exhaustive computation (one implementation,
cross-checked on a sample), and no instance with n ≥ 4 is known.** Written proofs (not yet refereed):
- **Lemma A** (§2): every key whose frozen agent is big-top has a state of deficit ≤ 1 (≤ 0 if ω = 1), by Theorem Z′.
  So at a T3-stage state of a big-top key: def = 1, V = ω + 1, ω ≥ 2.
- **Lemma B and Corollaries B1–B3** (§3): at f ≥ 1 no pre-allocation has every agent need-free. With z the only needer:
  no pair worth more than g to z (resp. no rich pair of x) can be freed together with need-free bases of the others;
  after a swap, x's bundle threatens z only if z is big-top and the bundle contains B_z; for a non-big-top x an x-alone
  triple must sit at an owner o ≠ z whose base meets every rich pair of x in its bundle.
- **Propositions C, D, E** (§4): from an *x-alone triple* (o, X, c) (a best owner o, an optimal bundle X, a junk good c
  whose only blocker is x), the swap of Corollary 8.2 reaches def ≤ 0: without helper when o = z (Proposition C, with
  two exceptions: u_z(X) = 1, and R_z = R_x with ω ≥ 3), and with o as the only helper when o ≠ z, as soon as o has an
  *escape* (a need-free base outside L with at most one good of its old bundle that leaves o envying nothing x keeps;
  Proposition D). If o values no lower good of x, its most valuable need-free base outside L is an escape when it takes
  at most one good of the bundle, and at n = 3 it always gives the swap (Proposition E).

What the T3 stage is still needed for (§5): (i) the existence of an x-alone triple (the strong form of `k4/dl13.md`
§6 item 1, SX, in this regime); (ii) an escape when o ≠ z, which fails at T1-stuck states that are not at the T3 stage
(`attempts/k4-oneneeder-escape-t1.md`, n = 4); (iii) x big-top.

Data (EVIDENCE, §6): exhaustively at n = 3 (all 299,837,376 strict profiles of the 51 cores; 7,284,544 with f = 1,
ω ≥ 1), every one of the 97,824 one-needer T3-stage states has x big-top, def = 1, an x-alone triple, and Corollary 8.2
with at most one helper; Proposition C applies at the 38,496 with a triple at z and Proposition D (an escape) at the
86,976 with a triple at o ≠ z; u never contributes and R_z ≠ R_x. At n = 3 a T3-stage state has a big-top x iff its
frozen good has one needer. At n = 4 and n = 5 (33.6 million sampled and catalogue profiles, 4,164 T3-stage states)
no T3-stage state is one-needer, and in the 2,152 T3-stage states of the samples that record it, x is never big-top.

## 1. Setting

Notation of `k4/dl2.md` §4 and `k4/dl13.md` §1. A strict profile of a connected k = 4 core whose fewest frozen agents is
f = 1, with ω = 1 − (2n − m) ≥ 1. P ∈ 𝒫 min-frozen; its frozen agent is x with base {g}; 𝒩 = NA(P) = {g}; the *key* of
P is (x, g) (`k4/c4min_reduce.md` §1; there it is written (g, x)). By Lemma K of `k4/c4min_reduce.md`, g is x's top;
L := R_x ∖ {g} are x's *lower goods*. A *needer* is an agent z with g ∈ N_z; by Lemma T there, every needer has top g.
A base B of an agent i is *need-free* if N_i(B) = ∅; every free agent that is not a needer is need-free (its needs lie
in 𝒩 = {g} and exclude g). A set worth more to i than a need-free base of i is need-free (every good outside it is
worth at most the base). x is *big-top* if |R_x| = 4 and v_x(g) > v_x(b) + v_x(c) (b > c > d its lower goods); then a
set Z ⊆ M ∖ {g} threatens x holding {g} iff L ⊆ Z and Z ≠ L (Lemma 8(a) of `k4/c4min_f1.md`; directly: a proper subset
of L is worth at most b + c, and L plus a good x does not value is worth b + c + d > v_x(g) after removing that good).
A *rich pair* of x is S ⊆ L, |S| = 2, v_x(S) > v_x(g); a big-top x has none.

def(P) = ω + 2 − V(P), V(P) := max (|Z| + u_o(Z)) over the free o and their safe bundles Z (Lemma H1). At f = 1,
u_o(Z) = 1 iff no agent other than o needs g and v_o(Z) > v_o(g) (`k4/dl13.md` §2.1, the term ι).

**The T3 stage at f = 1.** No (T4) move exists (one frozen agent), and (T1) ∪ (T2) are exactly the moves inside a key
(`k4/dl2.md` §3). So P is at the T3 stage iff def(P) > 0 and def(P) = def*(κ) := min{def(P′) : P′ min-frozen with key
κ = (x, g)}. P is *one-needer* if exactly one agent z needs g; z is free (x does not need its own base).

**An x-alone triple** at P is (o, X, c): o a best owner (Val_P(o) = V(P)), X an optimal bundle of o, c ∈ J ∖ X, such
that Y := X ∪ {c} threatens x holding {g} and no agent w ∉ {o, x} holding B_w (the only blocker of c is x). This is the
strongest form of the frozen obstruction of `k4/dl13.md` §2.3 (row A4 there: a junk good of a best owner blocked by one
frozen agent alone). Equivalently (when x is big-top and def(P) = 1): some free o has a bundle of ω + 2 goods that
threatens no agent other than x; then L ⊊ Y, and the lower goods of x are within reach of the single agent o:
L ⊆ Y ⊆ B_o ∪ J. (If o has such a bundle Y, removing a good of L ∖ B_o gives a safe bundle of ω + 1 = V(P) goods, which
is optimal, and u = 0 there since the value cannot exceed V(P).)

## 2. Big-top keys have least deficit at most 1

**Lemma A.** Let κ = (x, g) be a key with x big-top on g (f = 1, ω ≥ 1). Then some min-frozen Q with key κ has
def(Q) ≤ 1, and def(Q) ≤ 0 if ω = 1. Consequently, at a T3-stage state P with key κ: ω ≥ 2, def(P) = 1 and
V(P) = ω + 1.

*Proof.* By Theorem Z′(ii) of `k4/c4min_reduce.md` §2 (configurations at the key exist by Lemma K there, since ω ≥ 1),
some configuration at κ (pairs Q_y ⊆ M ∖ {g} for y ≠ x with Q_y ∩ U_y admissible, pool L₀ with ω goods) has a
free-valid owner o: X := Q_o ∪ L₀ threatens no y ∉ {o, x} holding Q_y. Let Q be the pre-allocation with x on {g} and
B_y := Q_y ∩ U_y for every y ≠ x (U_y = R_y ∖ {g}). Each B_y is admissible for {g}, so by Lemma K Q is min-frozen with
key κ. X is a bundle of o in Q: B_o ⊆ Q_o ⊆ X, and the goods of X ∖ B_o (those of Q_o outside U_o, and the pool) lie in
no base of Q. X threatens no free y ≠ o holding B_y, since v_y(B_y) = v_y(Q_y) (the goods of Q_y ∖ U_y are worthless to
y, as g ∉ Q_y). If X does not threaten x, V(Q) ≥ |X| = ω + 2 and def(Q) ≤ 0; this is the case if ω = 1, since
|X| = 3 = |L| and a threat needs L ⊊ X. Otherwise L ⊆ X; as |B_o| ≤ 2 < |L|, some ℓ ∈ L ∖ B_o exists, and X ∖ {ℓ} is a
bundle of o that threatens nobody (it misses ℓ, and threats are monotone), so V(Q) ≥ ω + 1 and def(Q) ≤ 1 (Lemma H1).
At a T3-stage P with key κ, 0 < def(P) = def*(κ) ≤ def(Q) ≤ 1, and ω ≥ 2 by the case ω = 1. ∎

So for a big-top key the T3 stage asks for a swap to a state of deficit ≤ 0, i.e. to a completable state of the
neighbouring key (z, g).

## 3. Need-free pre-allocations and what they exclude

**Lemma B.** At f ≥ 1 no pre-allocation (pairwise disjoint B_i ⊆ R_i, |B_i| ≤ 2) has every agent need-free.

*Proof.* It would lie in 𝒫 (NA = ∅ makes (V1), (V2) empty) with no frozen agent. ∎

Throughout §3–§4, P is min-frozen with f = 1, x on {g}, and z the only needer of g. A *swap* is the role swap of
`k4/dl13.md` §2.1: z takes {g}, x takes A, and a helper h (or none) takes B′_h, where (as in Corollary 8.2) B′_h is
admissible and g ∉ N_h(B′_h), i.e. B′_h is need-free; G := J ∪ B_z ∪ B_h.

**Corollary B1 (z cannot be bought off).** Let H be a set of free agents other than z with pairwise disjoint need-free
bases B′_h ⊆ J ∪ B_z ∪ ⋃_{h ∈ H} B_h (h ∈ H). Then every Q ⊆ (J ∪ B_z ∪ ⋃_{h ∈ H} B_h) ∖ ⋃_h B′_h with Q ⊆ R_z,
|Q| ≤ 2 has v_z(Q) < v_z(g). Likewise every S ⊆ L in that set with |S| ≤ 2 has v_x(S) < v_x(g).

*Proof.* Otherwise give z the base Q (resp. x the base S and z the base {g}), H their bases B′_h, x the base {g} (resp.
nothing more), and everybody else its base in P. z on Q is need-free because v_z(Q) > v_z(g) and g is z's top; x on S
likewise; z on {g} and x on {g} hold their tops; H is need-free by assumption; the others are free non-needers of P,
hence need-free. The bases are disjoint, inside the relevant sets, of at most two goods: Lemma B. ∎

With H = ∅ this contains Proposition T(d) of `k4/dl13.md`.

**Corollary B2 (when z is threatened after a swap).** In a swap with helper h (or none), a set Z ⊆ G ∖ B′_h threatens
z holding {g} only if z is big-top on g and L_z := R_z ∖ {g} ⊆ Z, so in particular only if B_z ⊆ Z.

*Proof.* θ_z(Z) = v_z(Z ∖ q) for some q ∈ Z; put Q′ := (Z ∖ q) ∩ R_z, so v_z(Q′) > v_z(g) and g ∉ Q′. If some subset of
Q′ with at most two goods were worth more than g to z, Corollary B1 (H = {h} or ∅) would be contradicted. So
|Q′| ≥ 3, i.e. Q′ = L_z (|R_z| = 4), and every pair of L_z is worth less than g: z is big-top on its top g. B_z ⊆ U_z =
L_z. ∎

**Corollary B3 (non-big-top x).** If x is not big-top, no rich pair S ⊆ L lies in J ∪ B_z; and if (o, X, c) is an
x-alone triple, then o ≠ z and every rich pair S ⊆ X ∪ {c} meets B_o. Moreover o has no need-free base inside
(J ∪ B_z ∪ B_o) ∖ S for such an S.

*Proof.* The first and last claims are Corollary B1 (H = ∅, resp. H = {o}). Let Y := X ∪ {c}; it threatens x holding
{g}, so v_x(Y ∖ q) > v_x(g) for some q ∈ Y, and (Y ∖ q) ∩ R_x ⊆ L (g ∉ Y). A single lower good is worth less than g, so
(Y ∖ q) ∩ L has two goods, which form a rich pair inside Y, or three (x has four goods), and then {b, c} ⊆ Y is rich
since x is not big-top. If o = z, or if a rich pair S ⊆ Y misses B_o, then S ⊆ J ∪ B_z (Y ⊆ B_o ∪ J), against the
first claim. ∎

So a non-big-top x in this regime needs an owner o whose need-free bases all use x's rich pairs; the data (§6) never
show it at the T3 stage, but no argument here excludes it.

## 4. The swap from an x-alone triple

Throughout, P is at the T3 stage (f = 1), x is big-top, z is the only needer of g, and A := {b, c_x} (x's two best
lower goods; admissible for x, its needs being {g}). By Lemma A, def(P) = 1 and V(P) = ω + 1 ≥ 3. The T3 stage enters
the propositions below only through def(P) = 1: they hold verbatim at every min-frozen P with def(P) = 1 (and Lemma G
replaces the T3 stage by T1-stuckness).

**Proposition C (the needer is the owner).** Let (z, X, c) be an x-alone triple with u_z(X) = 0. Then the swap without
helper gives def(P′) ≤ 0 < def(P), with x's bundle Z := Y or Y ∖ {ℓ} (Y := X ∪ {c}), unless R_z = R_x and ω ≥ 3.

*Proof.* |X| = V(P) = ω + 1, so |Y| = ω + 2. Y threatens x, so L ⊆ Y ⊆ W_z = J ∪ B_z = G, and A ⊆ L. By Lemma 6 P′ is
min-frozen with key (z, g), and nobody but z needs g in P′. Y threatens no agent w ∉ {x, z} holding B_w (x-alone).
- If Y does not threaten z holding {g}, Z := Y is a safe bundle of x in P′ containing L, and Corollary 8.2 gives
  def(P′) ≤ ω + 1 − |Y| = −1.
- Otherwise, by Corollary B2 (no helper), z is big-top on g and L_z ⊆ Y. If L_z ≠ L, take ℓ ∈ L_z ∖ L and Z := Y ∖ {ℓ}:
  Z ⊇ L ⊇ A, Z ∩ R_z ⊆ L_z ∖ {ℓ} is worth less than g to z (z big-top), Z ⊆ Y threatens no w ∉ {x, z}, and Corollary
  8.2 gives def(P′) ≤ ω + 1 − (ω + 1) = 0.
- If L_z = L and ω = 2: if L ⊆ X then X = L (X is safe), so v_z(X) > v_z(g) (z big-top) and u_z(X) = 1, excluded;
  so c ∈ L and Z := L is a safe bundle of x in P′ (it is not a proper superset of L_z = L, and L ⊆ Y), with
  |Z| = 3 = ω + 1: def(P′) ≤ 0. ∎

At n = 3, R_z = R_x forces ω ≤ 2: the third agent must value every good outside R_x, at most four goods, and share one
with R_x (connectedness), so m ≤ 4 + 3 = 7 and ω = m − 5 ≤ 2.

**Proposition D (an escape for the owner).** Let (o, X, c) be an x-alone triple with o ≠ z; Y := X ∪ {c} and
Rest := (J ∖ Y) ∪ B_z. An *escape* of o is a need-free base B′ ⊆ ((Y ∖ L) ∪ Rest) ∩ R_o (so g ∉ B′) with
|B′ ∩ Y| ≤ 1 and θ_o(Y ∖ B′) ≤ v_o(B′), such that B_o ⊄ B′ (o is the helper) or B′ = B_o is a single good outside L
(no helper). If o has an escape B′, the swap (z takes {g}, x takes A, o takes B′) gives def(P′) ≤ 0 < def(P), with
x's bundle Z := Y ∖ B′.

*Proof.* u_o(X) = 0 (z ≠ o needs g), so |X| = ω + 1 and |Y| = ω + 2; L ⊆ Y ⊆ B_o ∪ J. Let G := J ∪ B_z ∪ B_o; then
G = Y ∪ Rest. L ⊆ G (with no helper, L ∩ B_o = ∅ gives L ⊆ J ⊆ J ∪ B_z), B′ ⊆ G ∖ L is need-free (admissible with
g ∉ N_o(B′)), and the helper gives up a good of B_o: Corollary 8.2's hypotheses on x, z, A and the helper hold.
Z = Y ∖ B′ satisfies A ⊆ L ⊆ Z ⊆ G ∖ B′, so it is a bundle of x in P′. It is safe in P′: it threatens no w ∉ {x, z, o}
(Z ⊆ Y, x-alone triple); it misses B_z ≠ ∅ (Z ⊆ B_o ∪ J), so it does not threaten z holding {g} (Corollary B2); and it
does not threaten o holding B′ (escape). |Z| = ω + 2 − |B′ ∩ Y| ≥ ω + 1, and Corollary 8.2 gives
def(P′) ≤ ω + 1 − |Z| ≤ 0. ∎

So, given an x-alone triple at o ≠ z, the one-needer regime is a statement about o alone: the agents other than x, z, o
never block Z ⊆ Y. The next proposition finds the escape when o does not value x's lower goods.

**Proposition E (an owner indifferent to x's lower goods).** In the setting of Proposition D, let T′ be a most valuable
need-free base of o inside (G ∖ L) ∩ R_o, G := J ∪ B_z ∪ B_o (if o has one there).
- (a) A set Z ⊆ G ∖ T′ threatens o holding T′ only if Z contains a good of L that o values.
- (b) If o values no good of L, B_o ⊄ T′ and |T′ ∩ Y| ≤ 1, then T′ is an escape.
- (c) If o values no good of L, B_o ⊄ T′, |T′ ∩ Y| = 2 and n = 3, the swap with helper o on T′ and
  Z := (Y ∖ T′) ∪ {e}, e ∈ Rest (from J ∖ Y if it is nonempty), gives def(P′) ≤ 0.

*Proof.* (a) Suppose θ_o(Z) > v_o(T′): θ_o(Z) = v_o(Z ∖ q) for some q ∈ Z, and Q := (Z ∖ q) ∩ R_o ⊆ G ∖ T′ has
v_o(Q) > v_o(T′). Suppose Q contains no good of L. If |Q| ≤ 2, Q is need-free (worth more than the need-free T′) and lies
in G ∖ L: against the choice of T′. If |Q| ≥ 3, o has four goods, T′ = {t} and Q = R_o ∖ {t} ⊆ G ∖ L; then {t, q′}
(q′ ∈ Q) is need-free, inside G ∖ L and worth more than T′: again a contradiction.
(b) T′ ⊆ G ∖ L = (Y ∖ L) ∪ Rest, since B_o ⊆ Y. Y ∖ T′ ⊆ G ∖ T′ contains no good of L that o values, so by (a) it does
not threaten o holding T′.
(c) At n = 3 the agents are x, z, o, so |J ∖ Y| = |J| − (|Y| − |B_o|) = (2 − |B_z|) + (2 − |B_o|) + ω − (ω + 2) +
|B_o| = 2 − |B_z|, and Rest has two goods, both outside T′ ⊆ Y. Z ⊇ L ⊇ A, |Z| = ω + 1, Z ⊆ G ∖ T′. Z threatens nobody
in P′: there is no agent besides x, z, o; o is not threatened by (a); if e ∈ J ∖ Y, Z ⊆ B_o ∪ J misses B_z, and if
J ∖ Y = ∅ then Rest = B_z has two goods and Z misses one of them, so B_z ⊄ Z: by Corollary B2 z is not threatened.
Corollary 8.2 (helper o: T′ is need-free in G ∖ L and B_o ⊄ T′) gives def(P′) ≤ 0. ∎

On the data, Proposition E never applies at a T3-stage state: there the owner o ≠ z of every x-alone triple values a
lower good of x (§6). The next two statements use o's best base inside its own pot instead.

**Proposition F (an owner whose best base avoids L).** In the setting of Proposition D, let Q* be a most valuable
need-free base of o inside W_o ∩ R_o (W_o = B_o ∪ J; B_o is one, so Q* exists).
- (a) No subset of W_o ∖ Q* threatens o holding Q*.
- (b) If Q* ∩ L = ∅, |Q* ∩ Y| ≤ 1, and B_o ⊄ Q* or Q* = B_o is a single good, then Q* is an escape.

*Proof.* (a) If θ_o(Z) > v_o(Q*) for some Z ⊆ W_o ∖ Q*, then Q := (Z ∖ q) ∩ R_o has v_o(Q) > v_o(Q*) for some q ∈ Z.
If |Q| ≤ 2, Q is need-free (worth more than a need-free base) and lies in W_o: against the choice of Q*. If |Q| = 3, o has
four goods, Q* = {t} and Q = R_o ∖ {t} ⊆ W_o, and {t, q′} (q′ ∈ Q) is need-free, in W_o, and worth more than Q*.
(b) W_o = Y ∪ (J ∖ Y) (B_o ⊆ Y), so Q* ⊆ W_o ∖ L ⊆ (Y ∖ L) ∪ Rest, and Y ∖ Q* ⊆ W_o ∖ Q* does not threaten o by (a). ∎

**Lemma G (an owner whose best base meets L, at a T1-stuck state).** In the setting of Proposition D, let P be T1-stuck
(it need not be at the T3 stage) with def(P) = 1, Q* as in Proposition F with Q* ∩ L ≠ ∅ and Q* ≠ B_o, and P* the state
with o re-based to Q*. Then Z₀ := B_z ∪ (Y ∖ Q*) is a bundle of z in P* that does not threaten x holding {g}, and one of
the following holds:
- Z₀ threatens o holding Q*, and every subset of Z₀ that does contains a good of B_z;
- Z₀ threatens some agent w ∉ {x, z, o} holding B_w (necessarily through a good of B_z, as Y does not threaten w);
- |B_z| = 1, Q* ⊆ Y and v_z(Z₀) < v_z(g).

*Proof.* Q* is need-free, hence admissible, and lies in B_o ∪ J: by Lemma 1(c) of `k4/dl2.md`, P* is min-frozen with
needed set {g}; o is need-free in P*, so z is still the only needer. Y ∖ Q* ⊆ (B_o ∪ J) ∖ Q* ⊆ J(P*), so Z₀ is a bundle
of z in P*. It misses the good of Q* ∩ L, so it does not threaten x (x big-top). A subset of Z₀ without a good of B_z
lies in W_o ∖ Q* and does not threaten o (Proposition F(a)). If Z₀ is safe in P*, Lemma H1 in P* and T1-stuckness give
1 = def(P) ≤ def(P*) ≤ ω + 2 − |Z₀| − u′_z(Z₀), with |Z₀| = |B_z| + ω + 2 − |Q* ∩ Y|; so |B_z| + 1 + u′_z(Z₀) ≤
|Q* ∩ Y| ≤ 2, which forces |B_z| = 1, |Q* ∩ Y| = 2 and u′_z(Z₀) = 0, i.e. g ∈ N_z(Z₀): v_z(Z₀) < v_z(g). ∎

Lemma G is how T1-stuckness enters: an owner that would rather hold a lower good of x frees the rest of the key for z,
unless it values z's base (then a good of B_z is the natural escape for it) or z's base is dangerous to a third agent.
Turning the three cases into an escape is open (§5).

## 5. What remains

The step from the T3 stage to Corollary 8.2 splits into three statements, each true on all data (§6) and each needing
more than the local lemmas above.

1. **Conjecture SX1 (an x-alone triple).** At every one-needer T3-stage state with f = 1 some best owner has an x-alone
   triple. Its absence means: no free agent has a bundle of ω + 2 goods that threatens nobody but x, so the deficit 1 of
   P is caused by the free agents alone. This is item 1 of `k4/dl13.md` §6 (Conjecture SX) in its strong form,
   restricted to big-top keys; Lemma A shows that *some* state of the key has such a bundle (the state of Theorem Z′),
   but not that P has one. It needs the T3 stage: at T1-stuck one-needer states it fails (94 states on #53's n = 3
   catalogue, §6), as SX fails at `dl13-n3m6` (`k4/dl13.md` §5).
2. **Conjecture ES (an escape).** At every T1-stuck one-needer state with f = 1, def = 1, x big-top and an x-alone
   triple, Proposition C applies at some triple with owner z, or some triple with owner o ≠ z has an escape. True at
   every such state of the exhaustive n = 3 run and of the n = 4, 5 catalogues (§6), so on the data the T1-stuck
   hypothesis suffices here. Per triple it is false (`attempts/k4-oneneeder-escape-t1.md`, n = 4: a triple whose owner's
   top is held by a third agent), and without stuckness it is false (same file, n = 3: the owner needs a lower good of
   x, re-bases to it, and z then owns everything else, deficit −1; that is the first case of Lemma G turned around).
   Propositions E and F prove it when o's best base avoids L and takes at most one good of its bundle; Lemma G is the
   first step of the remaining case.
3. **x big-top.** Corollary B3 constrains a non-big-top x; the data never show one at a one-needer T3-stage state, while
   at T1-stuck one-needer states it occurs (12 states on #53's n = 3 catalogue), so this too needs the T3 stage.
4. **Proposition C's exceptions**: u_z(X) = 1 (then |X| = ω, L_z ⊆ X, and the swap's bundle has one good too few), and
   R_z = R_x with ω ≥ 3 (impossible at n = 3). Neither occurs in the data.

With SX1, ES and 3–4, Lemma A and Propositions C, D give: at every one-needer T3-stage state with f = 1, x is big-top,
def(P) = 1, and a swap of Corollary 8.2 with at most one helper (o, or none) reaches a state of deficit ≤ 0, i.e. a
completable state of the neighbouring key (z, g).

## 6. Data (EVIDENCE)

`k4/oneneeder.c` (driver `k4/oneneeder_run.py`) enumerates the min-frozen class of every profile with f = 1, computes
every deficit by Lemma H1, the least deficit of every key, and at every one-needer T3-stage state tests: x big-top;
def(P) = 1; an x-alone triple (with o ≠ z, with o = z); u at a best owner; Corollary 8.2 with at most one helper
(its conclusion asserted against the exact deficit of the swapped state, looked up in the class); Propositions C and D
(the construction of each, its safety and def(P′) ≤ 0 asserted the same way); some improving (T3) move (exact scan);
R_z = R_x. No assertion fails in any run.

Second implementation: `k4/oneneeder_check.py` (on `k4/suite/model.py`, with its own deficit by Lemma H1, asserted equal
to `model.Inst.deficit` with --check). The C tool also agrees, profile by profile, with a Python computation on
`k4/dl13_stuck.py`'s model (the T1-stuck dumps of `k4/dl13.md` §1): 2,541 profiles, 1,009 one-needer T3-stage states,
Corollary 8.2 at all of them (`k4/dl13_lemmas.py`'s C3 test), 0 mismatches.

| input | profiles | f = 1, ω ≥ 1 | T3-stage | one needer | x big-top | def = 1 | x-alone triple (o ≠ z / o = z) | u | Cor. 8.2 (none / best owner / other helper) | Prop. C / D |
|---|---|---|---|---|---|---|---|---|---|---|
| n = 3, every strict profile of the 51 cores | 299,837,376 | 7,284,544 | 397,192 | 97,824 | 97,824 | 97,824 | 97,824 (86,976 / 38,496) | 0 | 97,824 (54,528 / 86,976 / 10,368) | 38,496 / 86,976 |
| n = 3, 20,000 random per core (seed 11) | 1,020,000 | 28,055 | 1,104 | 183 | 183 | 183 | 183 (160 / 80) | 0 | 183 (111 / 160 / 22) | |
| `k4/dl13.md` §1 dumps, f = 1 profiles | 2,541 | 2,541 | 10,621 | 1,009 | 1,009 | 1,009 | 1,009 (917 / 375) | 0 | 1,009 (536 / 917 / 90) | |

At n = 3 the T3-stage states whose frozen agent is big-top are exactly the 97,824 one-needer ones; every T3-stage state
(one needer or not) has an improving (T3) move. The f = 1 profile count equals #53's count of f = 1 gap profiles at
n = 3 (`k4/gap.md` §2: 7,284,544).

n = 4 and n = 5 (logs `results/k4_oneneeder/cat_*`, `certs4_*`, `target*`): #53's gap catalogues and hunts (every
record), seeded random profiles of the certified n = 4 cores (unrestricted, and with every 4-good agent restricted to
big-top types), and a targeted sample (`--target`: for every good g valued by exactly two agents x, z with |R_x| = 4,
x restricted to big-top types with top g and z to types with top g, the shape of the one-needer regime). Together
33,569,273 profiles, 4,291,224 with f = 1 and ω ≥ 1, 1,083,408 def > 0 states, 4,164 T3-stage states (all with at
least two needers of the frozen good); in the 2,152 T3-stage states of the runs that record it (`certs4_*_s41`) x is
never big-top, and the big-top-restricted and targeted runs have no T3-stage state at all.

## 7. Failed candidates

`attempts/k4-oneneeder-escape-t1.md`: "at every one-needer state with def > 0, x big-top and an x-alone triple at
o ≠ z that is T1-stuck, o has an escape" fails at n = 4 (a (T2) move lowers the deficit there); without T1-stuckness it
fails at n = 3. On `k4/dl13.md` §1's profiles: 2,397 T3-stage triples, all with an escape; 84 T1-stuck triples not at the
T3 stage without one; 4,859 non-stuck triples without one.

## 8. Reproduce

```
sh k4/oneneeder_runs.sh                      # every run of section 6 (one process at a time)
python3 k4/oneneeder_check.py catalog results/k4_gap/gap_n3.json.gz --shapes   # second implementation, n = 3 sample
python3 attempts/k4_oneneeder_attempts.py    # section 7, both implementations
```
